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


pub use context::*;
pub use data::*;
pub use gendata::*;
pub use genrefs::*;
pub use refs::*;
pub use reify::*;
pub use callable_idents::*;


/// Optimize a vir expresison
///
/// This is a temporary fix for the issue where variables that are quantified over and are then stored in a let binding
/// cause issues with triggering somehow.
///
/// This was also intended to make debugging easier by making the resulting viper code a bit more readable
///
/// This should be replaced with a proper solution
pub fn opt<'vir, Cur, Next>(
    expr: &'vir crate::ExprGenData<'vir, Cur, Next>,
    rename: &mut HashMap<String, String>,
) -> &'vir crate::ExprGenData<'vir, Cur, Next> {
    match expr.kind {
        crate::ExprKindGenData::Local(d) => {
            let nam = rename
                .get(d.name)
                .map(|e| e.as_str())
                .unwrap_or(d.name)
                .to_owned();
             crate::with_vcx(move |vcx| vcx.mk_local_ex(vcx.alloc_str(&nam), d.ty))
        }

        crate::ExprKindGenData::Let(crate::LetGenData { name, val, expr }) => {
            let val = opt(*val, rename);

            match val.kind {
                // let name = loc.name
                crate::ExprKindGenData::Local(loc) => {
                    let t = rename
                        .get(loc.name)
                        .map(|e| e.to_owned())
                        .unwrap_or(loc.name.to_string());
                    assert!(rename.insert(name.to_string(), t).is_none());
                    return opt(*expr, rename);
                }
                _ => {}
            }

            let expr = opt(*expr, rename);

            match expr.kind {
                crate::ExprKindGenData::Local(inner_local) => {
                    if &inner_local.name == name {
                        return val;
                    }
                }
                _ => {}
            }
            crate::with_vcx(move |vcx| {
                vcx.mk_let_expr(name, val, expr)
                // vcx.alloc(crate::ExprKindGenData::Let(vcx.alloc(crate::LetGenData {
                //     name,
                //     val,
                //     expr,
                // })))
            })
    
        }
        crate::ExprKindGenData::FuncApp(crate::FuncAppGenData {
            target,
            args,
            result_ty,
        }) => {
            let n_args = args.iter().map(|arg| opt(arg, rename)).collect::<Vec<_>>();

            crate::with_vcx(move |vcx| {
                let x = vcx.alloc(crate::ExprKindGenData::FuncApp(vcx.alloc(
                    crate::FuncAppGenData {
                        target,
                        args: vcx.alloc_slice(&n_args),
                        result_ty: *vcx.alloc(*result_ty),
                    },
                )));

                vcx.alloc(crate::ExprGenData { kind: x })
            })
        }

        crate::ExprKindGenData::PredicateApp(crate::PredicateAppGenData { target, args, perm }) => {
            let n_args = args.iter().map(|arg| opt(arg, rename)).collect::<Vec<_>>();
            crate::with_vcx(move |vcx| {
                vcx.alloc(crate::ExprGenData {
                    kind: vcx.alloc(crate::ExprKindGenData::PredicateApp(vcx.alloc(
                        crate::PredicateAppGenData {
                            target,
                            perm: *perm,
                            args: vcx.alloc_slice(&n_args),
                        },
                    ))),
                })
            })
        }

        crate::ExprKindGenData::Forall(crate::ForallGenData {
            qvars,
            triggers,
            body,
        }) => {
            let body = opt(body, rename);

            crate::with_vcx(move |vcx| {
                vcx.alloc(crate::ExprGenData {
                    kind: vcx.alloc(crate::ExprKindGenData::Forall(vcx.alloc(
                        crate::ForallGenData {
                            qvars,
                            triggers,
                            body,
                        },
                    ))),
                })
            })
        }

        crate::ExprKindGenData::Ternary(crate::TernaryGenData { cond, then, else_ }) => {
            let cond = opt(*cond, rename);
            let then = opt(*then, rename);
            let else_ = opt(*else_, rename);

            crate::with_vcx(move |vcx| {
                vcx.alloc(crate::ExprGenData {
                    kind: vcx.alloc(crate::ExprKindGenData::Ternary(
                        vcx.alloc(crate::TernaryGenData { cond, then, else_ }),
                    )),
                })
            })
        }

        crate::ExprKindGenData::BinOp(crate::BinOpGenData { kind, lhs, rhs }) => {
            let lhs = opt(lhs, rename);
            let rhs = opt(rhs, rename);

            crate::with_vcx(move |vcx| {
                vcx.alloc(crate::ExprGenData {
                    kind: vcx.alloc(crate::ExprKindGenData::BinOp(vcx.alloc(
                        crate::BinOpGenData {
                            kind: kind.clone(),
                            lhs,
                            rhs,
                        },
                    ))),
                })
            })
        }

        crate::ExprKindGenData::UnOp(crate::UnOpGenData { kind, expr }) => {
            let expr = opt(expr, rename);
            crate::with_vcx(move |vcx| {
                vcx.alloc(crate::ExprGenData {
                    kind: vcx.alloc(crate::ExprKindGenData::UnOp(vcx.alloc(
                        crate::UnOpGenData {
                            kind: kind.clone(),
                            expr,
                        },
                    ))),
                })
            })
        }

        todo @ (crate::ExprKindGenData::Unfolding(_)
        | crate::ExprKindGenData::Field(_, _)
        | crate::ExprKindGenData::Old(_)
        | crate::ExprKindGenData::AccField(_)
        | crate::ExprKindGenData::Lazy(_, _)
        | crate::ExprKindGenData::Result) => expr,

        other @ (crate::ExprKindGenData::Const(_) | crate::ExprKindGenData::Todo(_)) => expr,
    }
}

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
