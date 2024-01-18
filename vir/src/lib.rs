#![feature(rustc_private)]
#![feature(never_type)]
#![feature(iter_intersperse)]

mod context;
mod data;
mod debug;
mod gendata;
mod genrefs; // TODO: explain gen...
mod macros;
mod refs;
mod reify;
mod callable_idents;

use std::collections::HashMap;

pub use callable_idents::*;
pub use context::*;
pub use data::*;
pub use gendata::*;
pub use genrefs::*;
pub use refs::*;
pub use reify::*;

fn default_fold_expr<'vir, Cur, Next, T: ExprFolder<'vir, Cur, Next>>(
    this: &mut T,
    e: &'vir crate::ExprGenData<'vir, Cur, Next>,
) -> &'vir crate::ExprGenData<'vir, Cur, Next> {
    match e.kind {
        ExprKindGenData::Local(local) => this.fold_local(local),
        ExprKindGenData::Field(recv, field) => this.fold_field(recv, field),
        ExprKindGenData::Old(expr) => this.fold_old(expr),
        ExprKindGenData::Const(value) => this.fold_const(value),
        ExprKindGenData::Result => this.fold_result(),
        ExprKindGenData::AccField(AccFieldGenData { recv, field, perm }) => {
            this.fold_acc_field(recv, field, *perm)
        }
        ExprKindGenData::Unfolding(_) => todo!(),
        ExprKindGenData::UnOp(_) => todo!(),
        ExprKindGenData::BinOp(_) => todo!(),
        ExprKindGenData::Ternary(_) => todo!(),
        ExprKindGenData::Forall(_) => todo!(),
        ExprKindGenData::Let(_) => todo!(),
        ExprKindGenData::FuncApp(_) => todo!(),
        ExprKindGenData::PredicateApp(_) => todo!(),
        ExprKindGenData::Lazy(_, _) => todo!(),
        ExprKindGenData::Todo(_) => todo!(),
    }
}

pub trait ExprFolder<'vir, Cur, Next>: Sized {
    fn fold(&mut self, e: crate::ExprGen<'vir, Cur, Next>) -> crate::ExprGen<'vir, Cur, Next> {
        default_fold_expr(self, e)
    }

    fn fold_local(&mut self, local: crate::Local<'vir>) -> crate::ExprGen<'vir, Cur, Next> {
        crate::with_vcx(move |vcx| vcx.mk_local_ex_local(local))
    }

    fn fold_field(
        &mut self,
        recv: crate::ExprGen<'vir, Cur, Next>,
        field: crate::Field<'vir>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        crate::with_vcx(move |vcx| vcx.mk_field_expr(recv, field))
    }

    fn fold_old(
        &mut self,
        expr: crate::ExprGen<'vir, Cur, Next>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        crate::with_vcx(move |vcx| vcx.mk_old_expr(expr))
    }

    fn fold_const(&mut self, value: crate::Const<'vir>) -> crate::ExprGen<'vir, Cur, Next> {
        crate::with_vcx(move |vcx| {
            vcx.alloc(ExprGenData {
                kind: vcx.alloc(ExprKindGenData::Const(value)),
            })
        })
    }

    fn fold_result(&mut self) -> crate::ExprGen<'vir, Cur, Next> {
        crate::with_vcx(move |vcx| {
            vcx.alloc(ExprGenData {
                kind: vcx.alloc(ExprKindGenData::Result),
            })
        })
    }

    fn fold_acc_field(
        &mut self,
        recv: ExprGen<'vir, Cur, Next>,
        field: Field<'vir>,
        perm: Option<ExprGen<'vir, Cur, Next>>,
    ) -> crate::ExprGen<'vir, Cur, Next> {
        crate::with_vcx(move |vcx| vcx.mk_acc_field_expr(recv, field, perm))
    }
}

pub fn opt<'vir, Cur, Next>(
    expr: &'vir crate::ExprKindGenData<'vir, Cur, Next>,
) -> &'vir crate::ExprKindGenData<'vir, Cur, Next> {
    let r = crate::with_vcx(move |vcx| vcx.alloc(ExprGenData { kind: expr }));

    opt_intenal(r, &mut Default::default()).kind
}

fn opt_slice<'vir, Cur, Next>(
    slice: &[&'vir crate::ExprGenData<'vir, Cur, Next>],
    rename: &mut HashMap<String, &'vir str>,
) -> Vec<&'vir crate::ExprGenData<'vir, Cur, Next>> {
    slice
        .iter()
        .map(|arg| opt_intenal(arg, rename))
        .collect::<Vec<_>>()
}

/// Optimize a vir expresison
///
/// This is intended to make debugging easier by making the resulting viper code a bit more readable
///
/// This should be replaced with a proper solution
fn opt_intenal<'vir, Cur, Next>(
    expr: &'vir crate::ExprGenData<'vir, Cur, Next>,
    rename: &mut HashMap<String, &'vir str>,
) -> &'vir crate::ExprGenData<'vir, Cur, Next> {
    match expr.kind {
        crate::ExprKindGenData::Local(d) => {
            let nam = rename.get(d.name).map(|e| *e).unwrap_or(d.name);
            crate::with_vcx(move |vcx| vcx.mk_local_ex(&nam, d.ty))
        }

        crate::ExprKindGenData::Let(crate::LetGenData { name, val, expr }) => {
            let val = opt_intenal(*val, rename);

            match val.kind {
                // let name = loc.name
                crate::ExprKindGenData::Local(loc) => {
                    let t = rename
                        .get(loc.name)
                        .map(|e| e.to_owned())
                        .unwrap_or(loc.name);
                    assert!(rename.insert(name.to_string(), t).is_none());
                    return opt_intenal(*expr, rename);
                }
                _ => {}
            }

            let expr = opt_intenal(*expr, rename);

            if let crate::ExprKindGenData::Local(inner_local) = expr.kind {
                if &inner_local.name == name {
                    // if we encounter the case `let X = val in X` then just return `val`
                    return val;
                }
            }
            crate::with_vcx(move |vcx| vcx.mk_let_expr(name, val, expr))
        }
        crate::ExprKindGenData::FuncApp(crate::FuncAppGenData {
            target,
            args,
            result_ty,
        }) => {
            let n_args = opt_slice(args, rename);
            crate::with_vcx(move |vcx| vcx.mk_func_app(target, &n_args, *result_ty))
        }

        crate::ExprKindGenData::PredicateApp(crate::PredicateAppGenData { target, args, perm }) => {
            let n_args = opt_slice(args, rename);

            crate::with_vcx(move |vcx| {
                vcx.mk_predicate_app_expr(vcx.alloc(crate::PredicateAppGenData {
                    target,
                    perm: *perm,
                    args: vcx.alloc_slice(&n_args),
                }))
            })
        }

        crate::ExprKindGenData::Forall(crate::ForallGenData {
            qvars,
            triggers,
            body,
        }) => {
            let body = opt_intenal(body, rename);

            crate::with_vcx(move |vcx| vcx.mk_forall_expr(qvars, triggers, body))
        }

        crate::ExprKindGenData::Ternary(crate::TernaryGenData { cond, then, else_ }) => {
            let cond = opt_intenal(*cond, rename);
            let then = opt_intenal(*then, rename);
            let else_ = opt_intenal(*else_, rename);

            crate::with_vcx(move |vcx| vcx.mk_ternary_expr(cond, then, else_))
        }

        crate::ExprKindGenData::BinOp(crate::BinOpGenData { kind, lhs, rhs }) => {
            let lhs = opt_intenal(lhs, rename);
            let rhs = opt_intenal(rhs, rename);

            crate::with_vcx(move |vcx| vcx.mk_bin_op_expr(kind.clone(), lhs, rhs))
        }

        crate::ExprKindGenData::UnOp(crate::UnOpGenData { kind, expr }) => {
            let expr = opt_intenal(expr, rename);
            crate::with_vcx(move |vcx| vcx.mk_unary_op_expr(kind.clone(), expr))
        }

        crate::ExprKindGenData::Field(expr, field) => {
            let expr = opt_intenal(expr, rename);
            crate::with_vcx(move |vcx| vcx.mk_field_expr(expr, field))
        }

        todo @ (crate::ExprKindGenData::Unfolding(_)
        | crate::ExprKindGenData::AccField(_)
        | crate::ExprKindGenData::Lazy(_, _)
        | crate::ExprKindGenData::Result) => expr,

        other @ (crate::ExprKindGenData::Const(_)
        | crate::ExprKindGenData::Todo(_)
        | crate::ExprKindGenData::Old(_)) => expr,
    }
}

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
