use std::ops::Index;

use prusti_interface::environment::body::MirBody;
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

use crate::{
    encoders::{
        TyUseImpureEnc, TyUsePureEnc,
        ty::{RustTyDecomposition, use_pure::TyUsePure},
    },
    trait_support::is_function_with_body,
};

pub struct MirLocalDefEnc;

#[derive(Clone, Debug)]
pub struct MirLocalDefEncOutputRef {
    pub arg_count: usize,
}
impl task_encoder::OutputRefAny for MirLocalDefEncOutputRef {}

#[derive(Clone, Copy)]
pub struct MirLocalDefEncOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, LocalDef<'vir>>,
    pub arg_count: usize,
}

impl<'vir> MirLocalDefEncOutput<'vir> {
    /// Returns the definitions for the function return value.
    pub fn ret(&self) -> LocalDef<'vir> {
        self[mir::RETURN_PLACE]
    }

    /// The snapshot type of the fn return value. Used to construct e.g. the
    /// `FunctionIdn`.
    pub fn snap_ty_return(&self) -> vir::TypeSnap<'vir> {
        self.ret().local_snap.ty()
    }

    fn arg_locals(&self) -> impl Iterator<Item = mir::Local> + '_ {
        (1..=self.arg_count).map(mir::Local::from)
    }

    /// Creates an iterator of all fn arguments. Can be used to construct e.g.
    /// type assertions.
    pub fn args(&self) -> impl Iterator<Item = LocalDef<'vir>> + '_ {
        self.arg_locals().map(|local| self[local])
    }

    /// Creates an iterator of the snapshot type of all fn arguments. Used to
    /// construct e.g. the `FunctionIdn`.
    pub fn snap_ty_args(&self) -> impl Iterator<Item = vir::TypeSnap<'vir>> + '_ {
        self.args().map(|arg| arg.local_snap.ty())
    }

    /// Creates an iterator of the snapshot type of all fn arguments. Used to
    /// construct e.g. the `FunctionIdn`.
    pub fn local_decl_args(&self) -> impl Iterator<Item = vir::LocalDeclSnap<'vir>> + '_ {
        self.args().map(|arg| arg.local_snap)
    }
}

pub type MirLocalDefEncError = ();

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::LocalDeclRef<'vir>,
    pub local_snap: vir::LocalDeclSnap<'vir>,
    pub local_ex: vir::ExprRef<'vir>,
    pub local_trig: Option<vir::ExprBool<'vir>>,
    pub impure_snap: vir::ExprSnap<'vir>,
    pub impure_pred: vir::ExprBool<'vir>,
}

fn should_encode_locals<'vir>(vcx: &vir::VirCtxt<'vir>, def_id: DefId) -> bool {
    if crate::encoders::spec::is_function_trusted(def_id) {
        tracing::info!("function {def_id:?} is trusted, skipping local encoding");
        return false;
    }
    if def_id.as_local().is_none() {
        tracing::info!("function {def_id:?} is not a local function, skipping local encoding");
        return false;
    }
    if !is_function_with_body(vcx.tcx(), def_id) {
        tracing::info!("function {def_id:?} is not a function with body, skipping local encoding");
        return false;
    }
    true
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MirLocalDefEncTask {
    ExternSpec(DefId),
    Local { def_id: DefId, all_locals: bool },
}

impl MirLocalDefEncTask {
    fn all_locals(self) -> bool {
        match self {
            MirLocalDefEncTask::ExternSpec(_) => true,
            MirLocalDefEncTask::Local { all_locals, .. } => all_locals,
        }
    }

    fn body<'tcx>(self, vcx: &vir::VirCtxt<'tcx>) -> Option<MirBody<'tcx>> {
        match self {
            MirLocalDefEncTask::ExternSpec(def_id) => {
                let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
                Some(vcx.body_mut().get_spec_body(def_id, substs, None))
            }
            MirLocalDefEncTask::Local { def_id, .. } => {
                if should_encode_locals(vcx, def_id) {
                    let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
                    Some(vcx.body_mut().get_impure_fn_body(
                        def_id.as_local().unwrap(),
                        substs,
                        None,
                    ))
                } else {
                    None
                }
            }
        }
    }

    fn def_id(self) -> DefId {
        match self {
            MirLocalDefEncTask::ExternSpec(def_id) => def_id,
            MirLocalDefEncTask::Local { def_id, .. } => def_id,
        }
    }
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'vir> = MirLocalDefEncTask;

    type OutputRef<'vir> = MirLocalDefEncOutputRef;
    type OutputFullDependency<'vir> = MirLocalDefEncOutput<'vir>;

    type EncodingError = MirLocalDefEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        fn mk_local_def<'vir>(
            vcx: &'vir vir::VirCtxt<'vir>,
            deps: &mut TaskEncoderDependencies<'vir, MirLocalDefEnc>,
            def_id: DefId,
            local: mir::Local,
            rust_ty: ty::Ty<'vir>,
        ) -> LocalDef<'vir> {
            let rust_ty_task = RustTyDecomposition::from_ty(rust_ty, vcx.tcx(), def_id);
            let ty_impure = deps.require_dep::<TyUseImpureEnc>(rust_ty_task).unwrap();
            let ty_pure = deps.require_dep::<TyUsePureEnc>(rust_ty_task).unwrap();

            let ref_local = vir::vir_format!(vcx, "_{}p", local.index());
            let snap_local = vir::vir_format!(vcx, "_{}s", local.index());
            let local = vcx.mk_local_decl(ref_local, vir::TYPE_REF);
            let local_snap = vcx.mk_local_decl(snap_local, ty_impure.snapshot());
            let local_ex = vcx.mk_local_ex(local);
            let impure_snap = ty_impure.ref_to_snap(local_ex);
            let impure_pred = ty_impure.ref_to_pred(vcx, local_ex, None);

            fn mk_local_trig<'vir>(
                vcx: &'vir vir::VirCtxt<'vir>,
                def_id: DefId,
                deps: &mut TaskEncoderDependencies<'vir, MirLocalDefEnc>,
                rust_ty: ty::Ty<'vir>,
                local_snap: &'vir vir::LocalDeclData<'vir, vir::Snap>,
                ty_pure: TyUsePure<'vir>,
            ) -> Option<vir::ExprBool<'vir>> {
                let local_arg = vcx.mk_local_ex(local_snap);
                match rust_ty.kind() {
                    ty::TyKind::Ref(_, referent_ty, _) => {
                        let referent_ty_task =
                            RustTyDecomposition::from_ty(*referent_ty, vcx.tcx(), def_id);
                        let referent_ty_pure =
                            deps.require_dep::<TyUsePureEnc>(referent_ty_task).unwrap();
                        let val_expr = ty_pure
                            .expect_immref()
                            .value_access(local_arg.downcast_ty());
                        Some(referent_ty_pure.trig_fn().call()(val_expr))
                    }
                    ty::TyKind::Adt(..) => Some(ty_pure.trig_fn().call()(local_arg)),
                    _ => None,
                }
            }

            let local_trig = mk_local_trig(vcx, def_id, deps, rust_ty, local_snap, ty_pure);

            LocalDef {
                local,
                local_snap,
                local_ex,
                local_trig,
                impure_snap,
                impure_pred,
            }
        }

        vir::with_vcx(|vcx| {
            // TODO: refactor this a bit: split into one encoder for arguments (only)
            //   and one for locals (only)
            let data = if let Some(body) = task_key.body(vcx) {
                deps.emit_output_ref(
                    *task_key,
                    MirLocalDefEncOutputRef {
                        arg_count: body.arg_count,
                    },
                )?;
                let locals = IndexVec::from_fn_n(
                    |local: mir::Local| {
                        let rust_ty = body.local_decls[local].ty;
                        mk_local_def(vcx, deps, task_key.def_id(), local, rust_ty)
                    },
                    if task_key.all_locals() {
                        body.local_decls.len()
                    } else {
                        // return + arguments
                        1 + body.arg_count
                    },
                );
                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let typing_env = ty::TypingEnv::post_analysis(vcx.tcx(), task_key.def_id());
                let sig = vcx.tcx().instantiate_and_normalize_erasing_regions(
                    ty::GenericArgs::identity_for_item(vcx.tcx(), task_key.def_id()),
                    typing_env,
                    vcx.tcx().fn_sig(task_key.def_id()),
                );
                let sig = sig.skip_binder();
                deps.emit_output_ref(
                    *task_key,
                    MirLocalDefEncOutputRef {
                        arg_count: sig.inputs().len(),
                    },
                )?;

                let locals = (0..sig.inputs_and_output.len())
                    .map(mir::Local::from)
                    .map(|local: mir::Local| {
                        let rust_ty = if local == mir::RETURN_PLACE {
                            sig.output()
                        } else {
                            sig.inputs()[local.index() - 1]
                        };
                        Ok(mk_local_def(vcx, deps, task_key.def_id(), local, rust_ty))
                    })
                    .collect::<Result<IndexVec<_, _>, _>>()?;

                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok(((), data))
        })
    }
}

impl<'vir> Index<mir::Local> for MirLocalDefEncOutput<'vir> {
    type Output = LocalDef<'vir>;
    fn index(&self, index: mir::Local) -> &Self::Output {
        &self.locals[index]
    }
}
