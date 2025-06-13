use prusti_rustc_interface::{
    middle::{
        mir::{
            self,
            interpret::{GlobalAlloc, Scalar},
            ConstValue,
        },
        ty,
    },
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Arity, CallableIdent};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstEncTask<'vir> {
    Mir {
        const_: mir::Const<'vir>,
        encoding_depth: usize, // current encoding depth
        def_id: DefId, // DefId of the current function
    },
}

/// Encodes constants into snapshot expressions. The evaluation of a constant
/// is assumed to be side-effect free, as enforced by the compiler. This encoder
/// handles two different kinds of constants: ones coming from the MIR and ones
/// coming from the type system.
///
/// See "Representing constants" in the rustc dev guide for an overview:
/// https://rustc-dev-guide.rust-lang.org/mir/index.html#representing-constants
pub struct ConstEnc;

use crate::encoders::{mir_pure::PureKind, MirPureEnc, MirPureEncTask};

use super::{
    lifted::{casters::CastTypePure, rust_ty_cast::RustTyCastersEnc},
    rust_ty_snapshots::RustTySnapshotsEnc,
};

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);

    type TaskDescription<'vir> = ConstEncTask<'vir>;
    type OutputFullLocal<'vir> = vir::Expr<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        match *task_key {
            ConstEncTask::Mir { const_, encoding_depth, def_id } => {
                let res = match const_ {
                    mir::Const::Val(val, ty) => {
                        let kind = deps
                            .require_local::<RustTySnapshotsEnc>(ty)?
                            .generic_snapshot
                            .specifics;
                        match val {
                            ConstValue::Scalar(Scalar::Int(int)) => {
                                let prim = kind.expect_primitive();
                                let val = int.to_bits(int.size());
                                let val = prim.expr_from_bits(ty, val);
                                vir::with_vcx(|vcx| prim.prim_to_snap.apply(vcx, [val]))
                            }
                            ConstValue::Scalar(Scalar::Ptr(ptr, _)) => vir::with_vcx(|vcx| {
                                match vcx.tcx().global_alloc(ptr.provenance.alloc_id()) {
                                    GlobalAlloc::Function { .. } => todo!(),
                                    GlobalAlloc::VTable(_, _) => todo!(),
                                    GlobalAlloc::Static(_) => todo!(),
                                    GlobalAlloc::Memory(_mem) => {
                                        // If the `unwrap` ever panics we need a different way to get the inner type
                                        // let inner_ty = ty.builtin_deref(true).map(|t| t.ty).unwrap_or(ty);
                                        let _inner_ty = ty.builtin_deref(true).unwrap();
                                        todo!()
                                    }
                                }
                            }),
                            ConstValue::ZeroSized => {
                                let s = kind.expect_structlike();
                                assert_eq!(s.field_snaps_to_snap.arity().args().len(), 0);
                                vir::with_vcx(|vcx| s.field_snaps_to_snap.apply(vcx, &[]))
                            }
                            // Encode `&str` constants to an opaque domain. If we ever want to perform string reasoning
                            // we will need to revisit this encoding, but for the moment this allows assertions to avoid
                            // crashing Prusti.
                            ConstValue::Slice { .. } if ty.peel_refs().is_str() => {
                                let ref_ty = kind.expect_immref();
                                let str_ty = ty.peel_refs();
                                let str_snap = deps
                                    .require_local::<RustTySnapshotsEnc>(str_ty)?
                                    .generic_snapshot
                                    .specifics
                                    .expect_structlike();
                                let cast = deps.require_local::<RustTyCastersEnc<CastTypePure>>(str_ty)?;
                                vir::with_vcx(|vcx| {
                                    // first, we create a string snapshot
                                    let snap = str_snap.field_snaps_to_snap.apply(vcx, &[]);
                                    // upcast it to a param
                                    let snap = cast.cast_to_generic_if_necessary(vcx, snap);
                                    // wrap it in a ref
                                    ref_ty.prim_to_snap.apply(vcx, [vcx.mk_null(), snap])
                                })
                            }
                            ConstValue::Slice { .. } => todo!("ConstValue::Slice : {:?}", const_.ty()),
                            ConstValue::Indirect { .. } => todo!("ConstValue::Indirect"),
                        }
                    }
                    mir::Const::Unevaluated(uneval, _) => vir::with_vcx(|vcx| {
                        let task = MirPureEncTask {
                            encoding_depth: encoding_depth + 1,
                            parent_def_id: uneval.def,
                            param_env: vcx.tcx().param_env(uneval.def),
                            substs: ty::List::identity_for_item(vcx.tcx(), uneval.def),
                            kind: PureKind::Constant(uneval.promoted.unwrap()),
                            caller_def_id: Some(def_id),
                        };
                        let expr = deps.require_local::<MirPureEnc>(task)?.expr;
                        use vir::Reify;
                        Ok(expr.reify(vcx, (uneval.def, &[])))
                    })?,
                    mir::Const::Ty(_, _) => vir::with_vcx(|vcx| {
                        deps
                            .require_local::<RustTySnapshotsEnc>(vcx.tcx().mk_ty_from_kind(ty::TyKind::Uint(ty::UintTy::Usize)))
                            .unwrap()
                            .generic_snapshot
                            .specifics
                            .expect_primitive()
                            .prim_to_snap.apply(vcx, [vcx.mk_uint::<0>()]) // TODO
                    }),
                };
                Ok((res, ()))
            }
            //_ => todo!(),
        }
    }
}
