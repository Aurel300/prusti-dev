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
    // TODO: which type? input or output? -> best to store both?
    UnOp(ty::Ty<'tcx>, mir::UnOp, ty::Ty<'tcx>),
    // BinOp(mir::BinOp, ty::Ty<'tcx>),
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
                    let e_operand_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        operand_ty,
                    ).unwrap();

                    let name = vir::vir_format!(vcx, "mir_unop_{op:?}_{}", int_name(operand_ty));
                    let arity = UnknownArity::new(vcx.alloc_slice(&[e_operand_ty.snapshot]));
                    let function = FunctionIdent::new(name, arity);
                    deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                        function,
                    });

                    let e_rvalue_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        rvalue_ty,
                    ).unwrap();
                    Ok((MirBuiltinEncoderOutput {
                        function: vcx.alloc(vir::FunctionData {
                            name,
                            args: vcx.alloc_slice(&[vcx.mk_local_decl("arg", e_operand_ty.snapshot)]),
                            ret: e_rvalue_ty.snapshot,
                            pres: &[],
                            posts: &[],
                            expr: Some(
                                e_rvalue_ty.expect_prim().prim_to_snap.apply(vcx,
                                    [vcx.alloc(vir::ExprData::UnOp(vcx.alloc(vir::UnOpData {
                                        kind: vir::UnOpKind::from(op),
                                        expr: e_operand_ty.expect_prim().snap_to_prim.apply(vcx, [vcx.mk_local_ex("arg")])
                                    })))]
                                )
                            ),
                        }),
                    }, ()))
                }

                // // TODO: should these be two different functions? precondition?
                // MirBuiltinEncoderTask::BinOp(mir::BinOp::Add | mir::BinOp::AddUnchecked, ty) => {
                //     let name = vir::vir_format!(vcx, "mir_binop_add_{}", int_name(*ty));
                //     deps.emit_output_ref::<Self>(task_key.clone(), MirBuiltinEncoderOutputRef {
                //         name,
                //     });

                //     let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(
                //         *ty,
                //     ).unwrap();
                //     Ok((MirBuiltinEncoderOutput {
                //         function: vcx.alloc(vir::FunctionData {
                //             name,
                //             args: vcx.alloc_slice(&[
                //                 vcx.mk_local_decl("arg1", ty_out.snapshot),
                //                 vcx.mk_local_decl("arg2", ty_out.snapshot),
                //             ]),
                //             ret: ty_out.snapshot,
                //             pres: &[],
                //             posts: &[],
                //             expr: Some(vcx.mk_func_app(
                //                 ty_out.from_primitive.unwrap(),
                //                 &[vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                //                     kind: vir::BinOpKind::Add,
                //                     lhs: vcx.mk_func_app(
                //                         ty_out.to_primitive.unwrap(),
                //                         &[vcx.mk_local_ex("arg1")],
                //                     ),
                //                     rhs: vcx.mk_func_app(
                //                         ty_out.to_primitive.unwrap(),
                //                         &[vcx.mk_local_ex("arg2")],
                //                     ),
                //                 })))],
                //             )),
                //         }),
                //     }, ()))
                // }

                MirBuiltinEncoderTask::CheckedBinOp(rvalue_ty, op, l_ty, r_ty) => {
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

                    let bool_cons = deps.require_ref::<crate::encoders::TypeEncoder>(
                        vcx.tcx.types.bool,
                    ).unwrap().expect_prim().prim_to_snap;
                    let e_rvalue_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        rvalue_ty,
                    ).unwrap();
                    // The result of a checked add will always be `(T, bool)`, get the `T` type
                    let rvalue_pure_ty = rvalue_ty.tuple_fields()[0];
                    let e_rvalue_pure_ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        rvalue_pure_ty,
                    ).unwrap();

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
                            expr: Some(e_rvalue_ty.expect_structlike().field_snaps_to_snap.apply(vcx,
                                &[
                                    e_rvalue_pure_ty.expect_prim().prim_to_snap.apply(vcx,
                                        [vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                                            kind: vir::BinOpKind::from(op),
                                            lhs: e_l_ty.expect_prim().snap_to_prim.apply(vcx,
                                                [vcx.mk_local_ex("arg1")],
                                            ),
                                            rhs: e_r_ty.expect_prim().snap_to_prim.apply(vcx,
                                                [vcx.mk_local_ex("arg2")],
                                            ),
                                        })))],
                                    ),
                                    // TODO: overflow condition!
                                    bool_cons.apply(vcx,
                                        [&vir::ExprData::Const(&vir::ConstData::Bool(false))],
                                    ),
                                ],
                            )),
                        }),
                    }, ()))
                }

                other => todo!("{other:?}"),
            }

        })
    }
}
