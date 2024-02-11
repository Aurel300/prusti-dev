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

        let s2 = EveryThingInliner::new().fold(s1);
        let s3 = BoolOptimizerFolder.fold(s2);

        ExprGenData { kind: s3.kind }
    }
}

struct BoolOptimizerFolder;

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for BoolOptimizerFolder {
    // transforms `a == true` into `a` and `a == false` into `!a`
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

    // Transforms `c? true : false` into `c`
    fn fold_ternary(
        &mut self,
        cond: ExprGen<'vir, Cur, Next>,
        then: ExprGen<'vir, Cur, Next>,
        else_: ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        let cond = self.fold(cond);
        let then = self.fold(then);
        let else_ = self.fold(else_);

        if let (
            crate::ExprKindGenData::Const(crate::ConstData::Bool(true)),
            crate::ExprKindGenData::Const(crate::ConstData::Bool(false)),
        ) = (then.kind, else_.kind)
        {
            return cond;
        }

        crate::with_vcx(move |vcx| vcx.mk_ternary_expr(cond, then, else_))
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
        let val = self.fold(val);

        self.rename.insert(name, val);

        let expr = self.fold(expr);

        expr
    }

    fn fold_local(&mut self, local: crate::Local<'vir>) -> crate::ExprGen<'vir, Cur, Next> {
        let lcl = crate::with_vcx(move |vcx| vcx.mk_local_ex_local(local));

        self.rename.get(local.name).map(|e| *e).unwrap_or(lcl)
    }

    // Transforms `C ? f(a) : f(b)` into `f(C? a : b)`
    fn fold_ternary(
        &mut self,
        cond: ExprGen<'vir, Cur, Next>,
        then: ExprGen<'vir, Cur, Next>,
        else_: ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        let cond = self.fold(cond);
        let then = self.fold(then);
        let else_ = self.fold(else_);

        if let (
            crate::ExprKindGenData::FuncApp(then_app),
            crate::ExprKindGenData::FuncApp(else_app),
        ) = (then.kind, else_.kind)
        {
            if then_app.args.len() == 1
                && else_app.args.len() == 1
                && else_app.target == then_app.target
                && else_app.result_ty == then_app.result_ty
            {
                return crate::with_vcx(move |vcx| {
                    vcx.mk_func_app(
                        then_app.target,
                        &[vcx.mk_ternary_expr(cond, then_app.args[0], else_app.args[0])],
                        then_app.result_ty,
                    )
                });
            }
        }

        crate::with_vcx(move |vcx| vcx.mk_ternary_expr(cond, then, else_))
    }

    // transforms `foo_read_x(foo_cons(a_1, ... a_n))` into a_x
    fn fold_func_app(
        &mut self,
        target: &'vir str,
        src_args: &'vir [ExprGen<'vir, Cur, Next>],
        result_ty: Option<crate::Type<'vir>>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        let src_args = self.fold_slice(src_args);

        // Hacky way to do read of cons:
        if src_args.len() == 1 {
            if let crate::ExprKindGenData::FuncApp(innerfuncapp) = src_args[0].kind {
                if let Some((start, "cons")) = innerfuncapp.target.rsplit_once("_") {
                    if let Some((_, read_nr)) = target.rsplit_once("_") {
                        if target.ends_with(&format!("read_{}", read_nr))
                            && target.starts_with(start)
                        {
                            if let Ok(read_nr) = read_nr.parse::<usize>() {
                                return innerfuncapp.args[read_nr];
                            } else {
                                println!("ERROR: Not a number: {} {}", innerfuncapp.target, target);
                            }
                        }
                    }
                }
            }
        }

        crate::with_vcx(move |vcx| vcx.mk_func_app(target, src_args, result_ty))
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
