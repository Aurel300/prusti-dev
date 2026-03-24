use prusti_rustc_interface::{
    const_eval::{
        const_eval::{CompileTimeMachine, mk_eval_cx_for_const_val},
        interpret::{CtfeProvenance, InterpCx, Projectable},
    },
    middle::{
        mir::{
            self, ConstValue,
            interpret::{GlobalAlloc, Scalar},
        },
        ty,
        ty::TypingEnv,
    },
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionGenData, FunctionIdn, VirCtxt};

use crate::encoders::{
    MirPureEnc, MirPureEncTask, PureKind,
    addr::RefDataEnc,
    ty::{
        RustTyDecomposition,
        generics::{GParams, GenericParamsEnc},
        use_pure::{TyUsePureEnc, TyUsePureImmRef, TyUsePureMutRef},
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

struct EncodeConstValData<'vir> {
    ecx: &'vir InterpCx<'vir, CompileTimeMachine<'vir>>,
    context: GParams<'vir>,
    span: Span,
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
                Self::encode_const_val_ty(deps, val, ty, context)
            }
            k => todo!("const kind {k:?}"),
        }
    }

    fn encode_const_val_ty<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: ConstValue,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self>> {
        vir::with_vcx(|vcx| {
            let ty_task = RustTyDecomposition::from_ty(ty, context);
            let kind = deps.require_dep::<TyUsePureEnc>(ty_task)?;
            Ok(match val {
                ConstValue::Scalar(Scalar::Int(int)) => {
                    let prim = kind.expect_primitive();
                    let val = int.to_bits(int.size());
                    let val = prim.expr_from_bits(ty, val);
                    (prim.prim_to_snap)(val)
                }
                ConstValue::Scalar(Scalar::Ptr(ptr, _)) => {
                    match vcx.tcx().global_alloc(ptr.provenance.alloc_id()) {
                        GlobalAlloc::Memory(_mem) => unreachable!(),
                        _ => todo!(),
                    }
                }
                ConstValue::ZeroSized => {
                    let s = kind.expect_structlike();
                    s.field_snaps_to_snap(Vec::new())
                }
                // Encode `&str` constants to an opaque domain. If we ever want to perform string reasoning
                // we will need to revisit this encoding, but for the moment this allows assertions to avoid
                // crashing Prusti.
                ConstValue::Slice { .. } if ty.peel_refs().is_str() => {
                    let ref_ty = kind.expect_immref();
                    let str_ty = ty.peel_refs();
                    let str_ty_task = RustTyDecomposition::from_ty(str_ty, context);
                    let str_snap = deps.require_dep::<TyUsePureEnc>(str_ty_task)?;
                    let str_snap = str_snap.expect_opaque();
                    // first, we create a string snapshot
                    let snap = (str_snap.arbitrary)().upcast_ty();
                    // wrap it in a ref
                    vir::with_vcx(|vcx| ref_ty.prim_to_snap(vcx.mk_null(), snap))
                }
                ConstValue::Slice { .. } => todo!("ConstValue::Slice: {ty:?}"),
                ConstValue::Indirect { .. } => todo!("ConstValue::Indirect"),
            })
        })
    }

    fn encode_ref<'vir, T, Ref>(
        ref_val: &'vir Ref,
        rec_data: &'vir EncodeConstValData<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: T,
        ty: RustTyDecomposition<'vir>,
        vcx: &'vir VirCtxt,
        prim_to_snap: fn(
            &'vir Ref,
            vir::ExprRef<'vir>,
            vir::ExprSnap<'vir>,
        ) -> vir::ExprCSnap<'vir>,
    ) -> Result<(Vec<vir::Function<'vir>>, vir::ExprCSnap<'vir>), EncodeFullError<'vir, Self>>
    where
        T: Projectable<'vir, CtfeProvenance>,
    {
        let inner_ty = ty.args.args()[1].expect_ty();
        let addr_to_ref = deps.require_dep::<RefDataEnc>(())?.addr_to_ref;

        Ok(if inner_ty.is_str() || inner_ty.is_slice() {
            let sl_ty = inner_ty.peel_refs();
            let sl_ty_task = RustTyDecomposition::from_ty(sl_ty, rec_data.context);
            let sl_snap = deps.require_dep::<TyUsePureEnc>(sl_ty_task)?;
            let sl_snap = sl_snap.expect_opaque();
            // first, we create a slice snapshot
            let snap = (sl_snap.arbitrary)().upcast_ty();
            // wrap it in a ref
            (vec![], prim_to_snap(ref_val, vcx.mk_null(), snap))
        } else {
            let ptr = rec_data.ecx.read_pointer(&val).expect("Expected a pointer");

            let rel_addr = match ptr.into_pointer_or_addr() {
                Ok(ptr) => {
                    ((ptr.provenance.alloc_id().0.get() as u128) << 64)
                        | ptr.prov_and_relative_offset().1.bytes() as u128
                }
                Err(addr) => addr.bytes() as u128,
            };
            let ecx = rec_data.ecx;
            let (snap_funs, snap) = Self::encode_const_val_tree(
                rec_data,
                deps,
                ecx.deref_pointer(&val).unwrap(),
                RustTyDecomposition::from_ty(inner_ty, rec_data.context),
            )?;
            (
                snap_funs,
                prim_to_snap(
                    ref_val,
                    addr_to_ref(
                        vcx.mk_const_expr(vir::ConstData::Int(rel_addr))
                            .downcast_ty(),
                    ),
                    snap.upcast_ty(),
                ),
            )
        })
    }

    fn encode_const_val_tree<'vir, T>(
        rec_data: &'vir EncodeConstValData<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: T,
        ty: RustTyDecomposition<'vir>,
    ) -> Result<(Vec<vir::Function<'vir>>, vir::ExprCSnap<'vir>), EncodeFullError<'vir, Self>>
    where
        T: Projectable<'vir, CtfeProvenance>,
    {
        let kind = deps.require_dep::<TyUsePureEnc>(ty)?;

        vir::with_vcx(|vcx| {
            Ok(match &kind.specifics {
                super::ty::TySpecifics::ArrayLike(array_data) => {
                    assert!(!array_data.slice);
                    let elem_ty = ty.args.args()[1].expect_ty();
                    let elem_len = ty.args.args()[0]
                        .expect_const()
                        .try_to_target_usize(vcx.tcx())
                        .unwrap();
                    let mut posts = vec![];
                    let mut funs = vec![];
                    let ecx = rec_data.ecx;
                    for idx in 0..elem_len {
                        let (snap_funs, snap) = Self::encode_const_val_tree(
                            rec_data,
                            deps,
                            ecx.project_index(&val, idx).unwrap(),
                            RustTyDecomposition::from_ty(elem_ty, rec_data.context),
                        )
                        .unwrap();
                        posts.push(
                            vcx.mk_eq_expr(
                                snap.upcast_ty(),
                                array_data.index(
                                    vcx.mk_result(kind.snapshot.downcast_ty()),
                                    vcx.mk_const_expr(vir::ConstData::Int(idx as u128))
                                        .downcast_ty(),
                                ),
                            ),
                        );
                        funs.extend(snap_funs);
                    }
                    let span_pos = vcx
                        .tcx()
                        .sess
                        .source_map()
                        .lookup_char_pos(rec_data.span.lo());
                    let gen_snap_func_idn: FunctionIdn<'_, (), vir::CSnap> = FunctionIdn::new(
                        vir::vir_format_identifier!(
                            vcx,
                            "const_{}:{}",
                            span_pos.line,
                            span_pos.col_display
                        ),
                        (),
                        kind.snapshot.downcast_ty(),
                    );
                    let gen_snap_func =
                        vcx.mk_function(gen_snap_func_idn, (), &[], vcx.alloc(posts), None, None);
                    funs.push(gen_snap_func);
                    (funs, (gen_snap_func_idn)())
                }
                super::ty::TySpecifics::Opaque(_) => todo!(),
                super::ty::TySpecifics::Primitive(prim) => {
                    let int = rec_data
                        .ecx
                        .read_scalar(&val)
                        .unwrap()
                        .try_to_scalar_int()
                        .expect("scalar should be an integer");
                    let val = int.to_bits(int.size());
                    let val = prim.expr_from_bits(*ty.ty.expect_primitive(), val);
                    (vec![], (prim.prim_to_snap)(val))
                }
                super::ty::TySpecifics::ImmRef(imm_ref) => Self::encode_ref(
                    imm_ref,
                    rec_data,
                    deps,
                    val,
                    ty,
                    vcx,
                    TyUsePureImmRef::prim_to_snap,
                )?,
                super::ty::TySpecifics::MutRef(mutref) => Self::encode_ref(
                    mutref,
                    rec_data,
                    deps,
                    val,
                    ty,
                    vcx,
                    TyUsePureMutRef::prim_to_snap,
                )?,
                super::ty::TySpecifics::StructLike(struct_data) => {
                    let mut snaps = vec![];
                    let mut funs = vec![];
                    let ecx = rec_data.ecx;
                    for (idx, field) in ty.ty.expect_structlike().fields.iter().enumerate() {
                        let (snap_funs, snap) = Self::encode_const_val_tree(
                            rec_data,
                            deps,
                            ecx.project_field(&val, idx.into()).unwrap(),
                            field.decompose_normalize(ty.args),
                        )
                        .unwrap();
                        snaps.push(snap.upcast_ty());
                        funs.extend(snap_funs);
                    }
                    (funs, struct_data.field_snaps_to_snap(snaps))
                }

                super::ty::TySpecifics::EnumLike(enum_data) => {
                    let variant_idx = rec_data.ecx.read_discriminant(&val).unwrap();
                    let mut snaps = vec![];
                    let mut funs = vec![];
                    let ecx = rec_data.ecx;
                    for (idx, field) in ty.ty.expect_enumlike().variants[variant_idx.as_usize()]
                        .inner
                        .fields
                        .iter()
                        .enumerate()
                    {
                        let (snap_funs, snap) = Self::encode_const_val_tree(
                            rec_data,
                            deps,
                            ecx.project_field(&val, idx.into()).unwrap(),
                            field.decompose_normalize(ty.args),
                        )
                        .unwrap();
                        snaps.push(snap.upcast_ty());
                        funs.extend(snap_funs);
                    }
                    (
                        funs,
                        enum_data.variants[variant_idx.as_usize()]
                            .inner
                            .field_snaps_to_snap(snaps),
                    )
                }
                _ => unreachable!(),
            })
        })
    }

    fn encode_const_val<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: ConstValue,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
        span: Span,
    ) -> Result<
        (
            Vec<&'vir FunctionGenData<'vir, (), !>>,
            vir::ExprCSnap<'vir>,
        ),
        EncodeFullError<'vir, Self>,
    > {
        let ty_ctxt_at = vir::with_vcx(|vcx| vcx.tcx().at(span));
        let (ecx, v) =
            mk_eval_cx_for_const_val(ty_ctxt_at, TypingEnv::fully_monomorphized(), val, ty)
                .unwrap();
        vir::with_vcx(|vcx| {
            let rec_data = EncodeConstValData {
                ecx: vcx.alloc(ecx),
                context,
                span,
            };
            Self::encode_const_val_tree(
                vcx.alloc(rec_data),
                deps,
                v,
                RustTyDecomposition::from_ty(ty, context),
            )
        })
    }
}

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);
    const ENCODER_NAME: &'static str = "const encoder";

    type TaskDescription<'vir> = ConstEncTask<'vir>;
    type OutputFullDependency<'vir> = vir::ExprCSnap<'vir>;
    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            for fun in output {
                program.add_function(fun);
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        Ok(match *task_key {
            ConstEncTask::Ty {
                const_,
                ty,
                context,
            } => (vec![], Self::encode_ty_const(deps, const_, ty, context)?),
            ConstEncTask::Mir {
                const_,
                encoding_depth,
                def_id,
                span,
            } => match const_ {
                mir::Const::Val(val, ty) => {
                    Self::encode_const_val(deps, val, ty, def_id.into(), span)?
                }
                mir::Const::Unevaluated(uneval, ty) => vir::with_vcx(|vcx| {
                    let resolved = {
                        let typing_env = ty::TypingEnv::post_analysis(vcx.tcx(), def_id);
                        vcx.tcx()
                            .const_eval_resolve(typing_env, uneval, vcx.tcx().def_span(def_id))
                    };
                    if let Ok(val) = resolved {
                        Self::encode_const_val(deps, val, ty, def_id.into(), span)
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
                        Ok((vec![], expr.reify(vcx, (uneval.def, &[])).downcast_ty()))
                    } else {
                        todo!("const too generic")
                    }
                })?,
                mir::Const::Ty(ty, const_) => (
                    vec![],
                    Self::encode_ty_const(deps, const_, ty, def_id.into())?,
                ),
            },
        })
    }
}
