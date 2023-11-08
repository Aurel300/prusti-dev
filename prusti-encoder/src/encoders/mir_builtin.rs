use prusti_rustc_interface::{
    middle::ty,
    middle::mir,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{UnknownArity, FunctionIdent, CallableIdent};

pub struct MirBuiltinEncoder;

#[derive(Clone, Debug)]
pub enum MirBuiltinEncoderError {
    Unsupported,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum MirBuiltinEncoderTask<'tcx> {
    UnOp(ty::Ty<'tcx>, mir::UnOp, ty::Ty<'tcx>),
    BinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
    CheckedBinOp(ty::Ty<'tcx>, mir::BinOp, ty::Ty<'tcx>, ty::Ty<'tcx>),
}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutputRef<'vir> {
    pub function: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny<'vir> for MirBuiltinEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirBuiltinEncoderOutput<'vir> {
    pub function: vir::Function<'vir>,
}

use std::cell::RefCell;

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirBuiltinEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirBuiltinEncoder {
    type TaskDescription<'vir> = MirBuiltinEncoderTask<'vir>;

    type OutputRef<'vir> = MirBuiltinEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirBuiltinEncoderOutput<'vir>;

    type EncodingError = MirBuiltinEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
        where F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirBuiltinEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        // TODO: this function is also useful for the type encoder, extract?
        fn int_name<'tcx>(ty: ty::Ty<'tcx>) -> &'static str {
            match ty.kind() {
                ty::TyKind::Bool => "bool",
                ty::TyKind::Int(kind) => kind.name_str(),
                ty::TyKind::Uint(kind) => kind.name_str(),
                _ => unreachable!("non-integer type"),
            }
        }

        vir::with_vcx(|vcx| {
            match *task_key {
                MirBuiltinEncoderTask::UnOp(rvalue_ty, op, operand_ty) => {
                    assert_eq!(rvalue_ty, operand_ty);
                    let e_operand_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        operand_ty,
                    ).unwrap();

                    let name = vir::vir_format!(vcx, "mir_unop_{op:?}_{}", int_name(operand_ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[e_operand_ty.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });

                    let e_rvalue_ty = &e_operand_ty;
                    let prim_rvalue_ty = e_rvalue_ty.expect_prim();
                    let snap_arg = vcx.mk_local_ex("arg");
                    let prim_arg = e_operand_ty.expect_prim().snap_to_prim.apply(vcx, [snap_arg]);
                    // `prim_to_snap(-snap_to_prim(arg))`
                    let mut val = prim_rvalue_ty.prim_to_snap.apply(vcx,
                        [vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                            kind: vir::UnOpKind::from(op),
                            expr: prim_arg,
                        })))]
                    );
                    if op == mir::UnOp::Neg && operand_ty.is_signed() {
                        // Can overflow when doing `- iN::MIN -> iN::MIN`. There
                        // is no `CheckedUnOp`, instead the compiler puts an
                        // `TerminatorKind::Assert` before in debug mode.
                        let vir::TypeData::Int { bit_width, signed: true } = prim_rvalue_ty.prim_type else {
                            unreachable!()
                        };
                        let bound = vcx.alloc(vir::ExprData::Const(vcx.alloc(vir::ConstData::Int(1 << (bit_width - 1)))));
                        let bound = vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                            kind: vir::UnOpKind::Neg,
                            expr: bound,
                        })));
                        // `snap_to_prim(arg) == -iN::MIN`
                        let cond = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                            kind: vir::BinOpKind::CmpEq,
                            lhs: prim_arg,
                            rhs: bound,
                        })));
                        // `snap_to_prim(arg) == -iN::MIN ? arg : prim_to_snap(-snap_to_prim(arg))`
                        val = vcx.alloc(vir::ExprData::Ternary(vcx.alloc(vir::TernaryData {
                            cond,
                            then: snap_arg,
                            else_: val,
                        })))
                    }

                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vcx.alloc_slice(&[vcx.mk_local_decl("arg", e_operand_ty.snapshot)]),
                            ret: e_rvalue_ty.snapshot,
                            pres: &[],
                            posts: &[],
                            expr: Some(val),
                        }),
                    }, ()))
                }

                MirBuiltinEncoderTask::BinOp(rvalue_ty, op, l_ty, r_ty) => {
                    let e_l_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        l_ty,
                    ).unwrap();
                    let e_r_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        r_ty,
                    ).unwrap();
                    let e_rvalue_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        rvalue_ty,
                    ).unwrap();
                    let prim_rvalue_ty = e_rvalue_ty.expect_prim();

                    let name = vir::vir_format!(vcx, "mir_binop_{op:?}_{}_{}", int_name(l_ty), int_name(r_ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[e_l_ty.snapshot, e_r_ty.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });
                    let val = prim_rvalue_ty.prim_to_snap.apply(vcx,
                        [vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                            kind: vir::BinOpKind::from(op),
                            lhs: e_l_ty.expect_prim().snap_to_prim.apply(vcx,
                                [vcx.mk_local_ex("arg1")],
                            ),
                            rhs: e_r_ty.expect_prim().snap_to_prim.apply(vcx,
                                [vcx.mk_local_ex("arg2")],
                            ),
                        })))]
                    );
                    use mir::BinOp::*;
                    let (pre, val) = match op {
                        // Overflow well defined as wrapping
                        Add | Sub | Mul | Shl | Shr =>
                            (None, Self::get_wrapped_val(vcx, val, prim_rvalue_ty.prim_type)),
                        // Undefined behavior to overflow (need precondition)
                        AddUnchecked | SubUnchecked | MulUnchecked | ShlUnchecked | ShrUnchecked => {
                            let wrapped_val = Self::get_wrapped_val(vcx, val, prim_rvalue_ty.prim_type);
                            let pre = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                                kind: vir::BinOpKind::CmpEq,
                                lhs: val,
                                rhs: wrapped_val,
                            })));
                            (Some(pre), val)
                        }
                        // Cannot overflow
                        Div | Rem | BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt | Offset =>
                            (None, val),
                    };
                    let pres = pre.map(|pre| vcx.alloc_slice(&[pre])).unwrap_or_default();

                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vcx.alloc_slice(&[
                                vcx.mk_local_decl("arg1", e_l_ty.snapshot),
                                vcx.mk_local_decl("arg2", e_r_ty.snapshot),
                            ]),
                            ret: e_rvalue_ty.snapshot,
                            pres,
                            posts: &[],
                            expr: Some(val),
                        }),
                    }, ()))
                }

                MirBuiltinEncoderTask::CheckedBinOp(rvalue_ty, op, l_ty, r_ty) => {
                    // `op` can only be `Add`, `Sub` or `Mul`
                    assert!(matches!(op, mir::BinOp::Add | mir::BinOp::Sub | mir::BinOp::Mul));
                    let e_l_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        l_ty,
                    ).unwrap();
                    let e_r_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        r_ty,
                    ).unwrap();

                    let name = vir::vir_format!(vcx, "mir_checkedbinop_{op:?}_{}_{}", int_name(l_ty), int_name(r_ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[e_l_ty.snapshot, e_r_ty.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });

                    let e_rvalue_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        rvalue_ty,
                    ).unwrap();
                    // The result of a checked add will always be `(T, bool)`, get the `T` type
                    let rvalue_pure_ty = rvalue_ty.tuple_fields()[0];
                    let bool_ty = rvalue_ty.tuple_fields()[1];
                    assert!(bool_ty.is_bool());

                    let e_rvalue_pure_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        rvalue_pure_ty,
                    ).unwrap();
                    let bool_cons = deps.require_ref::<crate::encoders::TypeEncoder>(
                        bool_ty,
                    ).unwrap().expect_prim().prim_to_snap;

                    // Unbounded value
                    let val_exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                        kind: vir::BinOpKind::from(op),
                        lhs: e_l_ty.expect_prim().snap_to_prim.apply(vcx,
                            [vcx.mk_local_ex("arg1")],
                        ),
                        rhs: e_r_ty.expect_prim().snap_to_prim.apply(vcx,
                            [vcx.mk_local_ex("arg2")],
                        ),
                    })));
                    let val_str = vir::vir_format!(vcx, "val");
                    let val = vcx.mk_local_ex(val_str);
                    // Wrapped value
                    let wrapped_val_exp = Self::get_wrapped_val(vcx, val, e_rvalue_pure_ty.expect_prim().prim_type);
                    let wrapped_val_str = vir::vir_format!(vcx, "wrapped_val");
                    let wrapped_val = vcx.mk_local_ex(wrapped_val_str);
                    let wrapped_val_snap = e_rvalue_pure_ty.expect_prim().prim_to_snap.apply(vcx,
                        [wrapped_val],
                    );
                    // Overflowed?
                    let overflowed = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                        kind: vir::BinOpKind::CmpNe,
                        lhs: wrapped_val,
                        rhs: val,
                    })));
                    let overflowed_snap = bool_cons.apply(vcx, [overflowed]);
                    // `tuple(prim_to_snap(wrapped_val), wrapped_val != val)`
                    let tuple = e_rvalue_ty.expect_structlike().field_snaps_to_snap.apply(vcx,
                        &[wrapped_val_snap, overflowed_snap]
                    );
                    // `let wrapped_val == (val ..) in $tuple`
                    let inner_let = vcx.alloc(vir::ExprData::Let(vcx.alloc(vir::LetGenData {
                        name: wrapped_val_str,
                        val: wrapped_val_exp,
                        expr: tuple,
                    })));

                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vcx.alloc_slice(&[
                                vcx.mk_local_decl("arg1", e_l_ty.snapshot),
                                vcx.mk_local_decl("arg2", e_r_ty.snapshot),
                            ]),
                            ret: e_rvalue_ty.snapshot,
                            pres: &[],
                            posts: &[],
                            expr: Some(vcx.alloc(vir::ExprData::Let(vcx.alloc(vir::LetGenData {
                                name: val_str,
                                val: val_exp,
                                expr: inner_let,
                            })))),
                        }),
                    }, ()))
                }
            }
        })
    }
}

impl MirBuiltinEncoder {
    fn get_wrapped_val<'vir>(vcx: &'vir vir::VirCtxt<'vir>, exp: &'vir vir::ExprData<'vir>, ty: vir::Type) -> &'vir vir::ExprData<'vir> {
        let vir::TypeData::Int { bit_width: bw, signed } = *ty else {
            panic!("Trying to get wrapped val on a non-int type.")
        };
        let mk_half =
            || vcx.alloc(vir::ExprData::Const(vcx.alloc(vir::ConstData::Int(1 << (bw - 1)))));
        let shift_amount = if signed {
            Some(mk_half())
        } else {
            None
        };
        let modulo_val = if bw == 128 {
            // `1_u128 << bw` would overflow to 0
            let half = shift_amount.unwrap_or_else(mk_half);
            vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::Add,
                lhs: half,
                rhs: half,
            }))
        } else {
            vir::ExprData::Const(vcx.alloc(vir::ConstData::Int(1 << bw)))
        };
        let mut exp = exp;
        if let Some(half) = shift_amount {
            exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::Add,
                lhs: exp,
                rhs: half,
            })));
        }
        exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
            kind: vir::BinOpKind::Mod,
            lhs: exp,
            rhs: vcx.alloc(modulo_val),
        })));
        if let Some(half) = shift_amount {
            exp = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::Sub,
                lhs: exp,
                rhs: half,
            })));
        }
        exp
    }
}
