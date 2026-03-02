use itertools::Itertools;
use prusti_rustc_interface::{
    const_eval::{
        const_eval::{CompileTimeMachine, mk_eval_cx_for_const_val},
        interpret::{CtfeProvenance, InterpCx, Projectable},
    },
    middle::{
        mir::{self, ConstValue},
        ty,
        ty::{TyKind, TypingEnv},
    },
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    MirPureEnc, MirPureEncTask, PureKind,
    addr::RefDataEnc,
    ty::{
        RustTyDecomposition,
        generics::{GParams, GenericParamsEnc},
        use_pure::TyUsePureEnc,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstEncTask<'vir> {
    Ty {
        const_: ty::Const<'vir>,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
    },
    Mir {
        const_: mir::Const<'vir>,
        encoding_depth: usize, // current encoding depth
        def_id: DefId,         // DefId of the current function
        span: Span,
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

impl ConstEnc {
    fn encode_ty_const<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        const_: ty::Const<'vir>,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        match const_.kind() {
            ty::ConstKind::Param(param) => {
                let params = deps.require_dep::<GenericParamsEnc>(context)?;
                Ok(params.const_expr(param))
            }
            ty::ConstKind::Value(val) => {
                let val = vir::with_vcx(|vcx| vcx.tcx().valtree_to_const_val(val));
                Self::encode_const_val(deps, val, ty, context, None)
            }
            k => todo!("const kind {k:?}"),
        }
    }

    fn encode_const_val_tree<'vir, T>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: T,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
        ecx: &InterpCx<'vir, CompileTimeMachine<'vir>>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>>
    where
        T: Projectable<'vir, CtfeProvenance>,
    {
        let ty_task = RustTyDecomposition::from_ty(ty, context);
        let kind = deps.require_dep::<TyUsePureEnc>(ty_task)?;

        vir::with_vcx(|vcx| {
            Ok(match &kind.specifics {
                super::ty::TySpecifics::ArrayLike(_array_data) => todo!(),
                super::ty::TySpecifics::Param(_) => todo!(),
                super::ty::TySpecifics::Opaque(_) => todo!(),
                super::ty::TySpecifics::Primitive(prim) => {
                    let int = ecx
                        .read_scalar(&val)
                        .unwrap()
                        .try_to_scalar_int()
                        .expect("Expected an integer");
                    let val = int.to_bits(int.size());
                    let val = prim.expr_from_bits(ty, val);
                    (prim.prim_to_snap)(val)
                }
                super::ty::TySpecifics::ImmRef(imm_ref) => {
                    let inner_ty = ty.builtin_deref(true).unwrap();
                    let addr_to_ref = deps.require_dep::<RefDataEnc>(())?.addr_to_ref;

                    if ty.builtin_deref(true).is_some()
                        && (ty.builtin_deref(true).unwrap().is_str()
                            || ty.builtin_deref(true).unwrap().is_slice())
                    {
                        let sl_ty = ty.peel_refs();
                        let sl_ty_task = RustTyDecomposition::from_ty(sl_ty, context);
                        let sl_snap = deps.require_dep::<TyUsePureEnc>(sl_ty_task)?;
                        let sl_snap = sl_snap.expect_opaque();
                        // first, we create a slice snapshot
                        let snap = (sl_snap.arbitrary)().upcast_ty();
                        // wrap it in a ref
                        vir::with_vcx(|vcx| imm_ref.prim_to_snap(vcx.mk_null(), snap))
                    } else {
                        let ptr = ecx.read_pointer(&val).expect("Expected a pointer");

                        let rel_addr = match ptr.into_pointer_or_addr() {
                            Ok(ptr) => {
                                ((ptr.provenance.alloc_id().0.get() as u128) << 64)
                                    | ptr.prov_and_relative_offset().1.bytes() as u128
                            }
                            Err(addr) => addr.bytes() as u128,
                        };
                        imm_ref.prim_to_snap(
                            addr_to_ref(
                                vcx.mk_const_expr(vir::ConstData::Int(rel_addr))
                                    .downcast_ty(),
                            ),
                            Self::encode_const_val_tree(
                                deps,
                                ecx.deref_pointer(&val).unwrap(),
                                inner_ty,
                                context,
                                ecx,
                            )?
                            .upcast_ty(),
                        )
                    }
                }
                super::ty::TySpecifics::MutRef(mutref) => {
                    let inner_ty = ty.builtin_deref(true).unwrap();
                    let addr_to_ref = deps.require_dep::<RefDataEnc>(())?.addr_to_ref;

                    if ty.peel_refs().is_str() || ty.peel_refs().is_slice() {
                        let sl_ty = ty.peel_refs();
                        let sl_ty_task = RustTyDecomposition::from_ty(sl_ty, context);
                        let sl_snap = deps.require_dep::<TyUsePureEnc>(sl_ty_task)?;
                        let sl_snap = sl_snap.expect_opaque();
                        // first, we create a slice snapshot
                        let snap = (sl_snap.arbitrary)().upcast_ty();
                        // wrap it in a ref
                        vir::with_vcx(|vcx| mutref.prim_to_snap(vcx.mk_null(), snap))
                    } else {
                        let ptr = ecx.read_pointer(&val).expect("Expected a pointer");

                        let rel_addr = match ptr.into_pointer_or_addr() {
                            Ok(ptr) => {
                                ((ptr.provenance.alloc_id().0.get() as u128) << 64)
                                    | ptr.prov_and_relative_offset().1.bytes() as u128
                            }
                            Err(addr) => addr.bytes() as u128,
                        };

                        mutref.prim_to_snap(
                            addr_to_ref(
                                vcx.mk_const_expr(vir::ConstData::Int(rel_addr))
                                    .downcast_ty(),
                            ),
                            Self::encode_const_val_tree(
                                deps,
                                ecx.deref_pointer(&val).unwrap(),
                                inner_ty,
                                context,
                                ecx,
                            )?
                            .upcast_ty(),
                        )
                    }
                }
                super::ty::TySpecifics::StructLike(struct_data) => match ty.kind() {
                    TyKind::Tuple(tys) => struct_data.field_snaps_to_snap(
                        (0..struct_data.fields.len())
                            .map(|idx| {
                                Self::encode_const_val_tree(
                                    deps,
                                    ecx.project_field(&val, idx.into()).unwrap(),
                                    tys[idx],
                                    context,
                                    ecx,
                                )
                                .unwrap()
                                .upcast_ty()
                            })
                            .collect_vec(),
                    ),
                    TyKind::Adt(def, args) => {
                        let fields = def.all_fields().collect_vec();
                        struct_data.field_snaps_to_snap(
                            (0..struct_data.fields.len())
                                .map(|idx| {
                                    Self::encode_const_val_tree(
                                        deps,
                                        ecx.project_field(&val, idx.into()).unwrap(),
                                        fields[idx].ty(vcx.tcx(), args),
                                        context,
                                        ecx,
                                    )
                                    .unwrap()
                                    .upcast_ty()
                                })
                                .collect_vec(),
                        )
                    }
                    _ => unreachable!(),
                },
                super::ty::TySpecifics::EnumLike(enum_data) => match ty.kind() {
                    TyKind::Adt(def, args) => {
                        let fields = def.all_fields().collect_vec();
                        let variant_idx = ecx.read_discriminant(&val).unwrap();
                        let struct_data = &enum_data.variants[variant_idx.as_usize()].inner;
                        struct_data.field_snaps_to_snap(
                            (0..struct_data.fields.len())
                                .map(|idx| {
                                    Self::encode_const_val_tree(
                                        deps,
                                        ecx.project_field(&val, idx.into()).unwrap(),
                                        fields[idx].ty(vcx.tcx(), args),
                                        context,
                                        ecx,
                                    )
                                    .unwrap()
                                    .upcast_ty()
                                })
                                .collect_vec(),
                        )
                    }
                    _ => unreachable!(),
                },
                super::ty::TySpecifics::Builtin(_) => unreachable!(),
            })
        })
    }

    fn encode_const_val<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: ConstValue,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
        span: Option<Span>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        let ty_ctxt_at = vir::with_vcx(|vcx| vcx.tcx().at(span.unwrap()));
        let (ecx, v) =
            mk_eval_cx_for_const_val(ty_ctxt_at, TypingEnv::fully_monomorphized(), val, ty)
                .unwrap();

        Self::encode_const_val_tree(deps, v, ty, context, &ecx)
    }
}

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);
    const ENCODER_NAME: &'static str = "const encoder";

    type TaskDescription<'vir> = ConstEncTask<'vir>;
    type OutputFullDependency<'vir> = vir::ExprCSnap<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let res = match *task_key {
            ConstEncTask::Ty {
                const_,
                ty,
                context,
            } => Self::encode_ty_const(deps, const_, ty, context)?,
            ConstEncTask::Mir {
                const_,
                encoding_depth,
                def_id,
                span,
            } => match const_ {
                mir::Const::Val(val, ty) => {
                    Self::encode_const_val(deps, val, ty, def_id.into(), Some(span))?
                }
                mir::Const::Unevaluated(uneval, ty) => vir::with_vcx(|vcx| {
                    let resolved = {
                        let typing_env = ty::TypingEnv::post_analysis(vcx.tcx(), def_id);
                        vcx.tcx()
                            .const_eval_resolve(typing_env, uneval, vcx.tcx().def_span(def_id))
                    };
                    if let Ok(val) = resolved {
                        Self::encode_const_val(deps, val, ty, def_id.into(), Some(span))
                    } else if let Some(promoted) = uneval.promoted {
                        let task = MirPureEncTask {
                            encoding_depth: encoding_depth + 1,
                            parent_def_id: uneval.def,
                            param_env: vcx.tcx().param_env(uneval.def),
                            substs: ty::List::identity_for_item(vcx.tcx(), uneval.def),
                            kind: PureKind::Constant(promoted),
                            caller_def_id: Some(def_id),
                        };
                        let expr = deps.require_dep::<MirPureEnc>(task)?.expr;
                        use vir::Reify;
                        Ok(expr.reify(vcx, (uneval.def, &[])).downcast_ty())
                    } else {
                        todo!("const too generic")
                    }
                })?,
                mir::Const::Ty(ty, const_) => {
                    Self::encode_ty_const(deps, const_, ty, def_id.into())?
                }
            },
        };
        Ok(((), res))
    }
}
