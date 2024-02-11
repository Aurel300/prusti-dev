use std::collections::HashMap;

use crate::{ExprFolder, ExprGen, ExprGenData};

pub trait Optimizable: Sized {
    fn optimize(&self) -> Self;
}

impl<'vir, T> Optimizable for Option<&'vir T>
where
    T: Optimizable,
{
    fn optimize(&self) -> Self {
        self.map(|inner| {
            let o = inner.optimize();
            crate::with_vcx(move |vcx| vcx.alloc(o))
        })
    }
}

impl<'vir, T> Optimizable for &'vir [&T]
where
    T: Optimizable,
{
    fn optimize(&self) -> Self {
        let v = self
            .iter()
            .map(|e| {
                let e = e.optimize();
                crate::with_vcx(|vcx| vcx.alloc(e))
            })
            .collect::<Vec<_>>();
        crate::with_vcx(move |vcx| vcx.alloc_slice(&v))
    }
}

impl<'vir, Curr, Next> crate::Optimizable for ExprGenData<'vir, Curr, Next> {
    fn optimize(&self) -> Self {
        let r = crate::with_vcx(move |vcx| vcx.alloc(ExprGenData { kind: self.kind }));
        let s1 = (VariableOptimizerFolder {
            rename: Default::default(),
        })
        .fold(r);

        let s2 = BoolOptimizerFolder.fold(s1);
        let s3 = EveryThingInliner::new().fold(s2);

        ExprGenData { kind: s3.kind }
    }
}

struct BoolOptimizerFolder;

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for BoolOptimizerFolder {
    fn fold_binop(
        &mut self,
        kind: crate::BinOpKind,
        lhs: ExprGen<'vir, Cur, Next>,
        rhs: ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        let lhs = self.fold(lhs);
        let rhs = self.fold(rhs);

        if let crate::BinOpKind::CmpEq = kind {
            if let crate::ExprKindGenData::Const(crate::ConstData::Bool(b)) = rhs.kind {
                return if *b {
                    // case lhs == true
                    lhs
                } else {
                    // case lhs == false
                    crate::with_vcx(move |vcx| vcx.mk_unary_op_expr(crate::UnOpKind::Not, lhs))
                };
            }
        }

        crate::with_vcx(move |vcx| vcx.mk_bin_op_expr(kind, lhs, rhs))
    }
}

pub(crate) struct EveryThingInliner<'vir, Cur, Next> {
    rename: HashMap<&'vir str, crate::ExprGen<'vir, Cur, Next>>,
}

impl<'vir, Cur, Next> EveryThingInliner<'vir, Cur, Next> {
    fn new() -> Self {
        Self {
            rename: HashMap::new(),
        }
    }
}

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for EveryThingInliner<'vir, Cur, Next> {
    fn fold_let(
        &mut self,
        name: &'vir str,
        val: ExprGen<'vir, Cur, Next>,
        expr: ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        self.rename.insert(name, val);

        let val = self.fold(val);
        let expr = self.fold(expr);

        crate::with_vcx(move |vcx| vcx.mk_let_expr(name, val, expr))
    }

    fn fold_local(&mut self, local: crate::Local<'vir>) -> crate::ExprGen<'vir, Cur, Next> {
        let lcl = crate::with_vcx(move |vcx| vcx.mk_local_ex_local(local));

        self.rename.get(local.name).map(|e| *e).unwrap_or(lcl)
    }
}

pub(crate) struct VariableOptimizerFolder<'vir> {
    rename: HashMap<String, &'vir str>,
}

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for VariableOptimizerFolder<'vir> {
    fn fold_local(&mut self, local: crate::Local<'vir>) -> crate::ExprGen<'vir, Cur, Next> {
        let nam = self
            .rename
            .get(local.name)
            .map(|e| *e)
            .unwrap_or(local.name);
        crate::with_vcx(move |vcx| vcx.mk_local_ex(&nam, local.ty))
    }

    fn fold_old(
        &mut self,
        expr: crate::ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        // Do not go inside of old
        crate::with_vcx(|vcx| vcx.mk_old_expr(expr))
    }

    fn fold_let(
        &mut self,
        name: &'vir str,
        val: ExprGen<'vir, Cur, Next>,
        expr: ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        let val = self.fold(val);

        match val.kind {
            // let name = loc.name
            crate::ExprKindGenData::Local(loc) => {
                let t = self
                    .rename
                    .get(loc.name)
                    .map(|e| e.to_owned())
                    .unwrap_or(loc.name);
                assert!(self.rename.insert(name.to_string(), t).is_none());
                return self.fold(expr);
            }
            _ => {}
        }

        let expr = self.fold(expr);

        if let crate::ExprKindGenData::Local(inner_local) = expr.kind {
            if inner_local.name == name {
                // if we encounter the case `let X = val in X` then just return `val`
                return val;
            }
        }
        crate::with_vcx(move |vcx| vcx.mk_let_expr(name, val, expr))
    }
}
