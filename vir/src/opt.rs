use std::collections::HashMap;

use crate::{ExprFolder, ExprGen, ExprGenData};

struct OptFolder<'vir> {
    rename: HashMap<String, &'vir str>,
}

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for OptFolder<'vir> {
    fn fold_local(&mut self, local: crate::Local<'vir>) -> crate::ExprGen<'vir, Cur, Next> {
        let nam = self
            .rename
            .get(local.name)
            .map(|e| *e)
            .unwrap_or(local.name);
        crate::with_vcx(move |vcx| vcx.mk_local_ex(&nam, local.ty))
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

pub fn opt<'vir, Cur, Next>(
    expr: &'vir crate::ExprKindGenData<'vir, Cur, Next>,
) -> &'vir crate::ExprKindGenData<'vir, Cur, Next> {
    let r = crate::with_vcx(move |vcx| vcx.alloc(ExprGenData { kind: expr }));

    (OptFolder {
        rename: Default::default(),
    })
    .fold(r)
    .kind
}
