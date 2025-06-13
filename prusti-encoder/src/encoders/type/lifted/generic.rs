use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::with_vcx;

use crate::encoders::GenericEnc;

/// Lifting of a Rust type parameter in a function to a Viper value of type
/// `Type`. This is represented as a [`vir::LocalDecl`], because unsubstituted generic
/// parameters will always correspond to a method or function parameter in the
/// Viper encoding.
#[derive(Clone, Copy, Debug)]
pub struct LiftedGeneric<'vir>(pub vir::LocalDecl<'vir>);

impl<'vir> LiftedGeneric<'vir> {
    pub fn decl(&self) -> vir::LocalDecl<'vir> {
        self.0
    }
    pub fn ty(&self) -> vir::Type<'vir> {
        self.0.ty
    }
    pub fn expr<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir vir::VirCtxt<'_>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        vcx.mk_local_ex(self.0.name, self.0.ty)
    }
}

impl<'vir> OutputRefAny for LiftedGeneric<'vir> {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LiftedGenericEncTask<'vir> {
    Param(ty::ParamTy),
    Const(ty::Const<'vir>),
}

pub struct LiftedGenericEnc;

impl TaskEncoder for LiftedGenericEnc {
    task_encoder::encoder_cache!(LiftedGenericEnc);

    type TaskDescription<'tcx> = LiftedGenericEncTask<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputRef<'vir> = LiftedGeneric<'vir>;

    type OutputFullLocal<'vir> = ();

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        with_vcx(|vcx| {
            let output_ref = LiftedGeneric(match task_key {
                LiftedGenericEncTask::Param(param) => vcx.mk_local_decl(
                    vcx.alloc_str(param.name.as_str()),
                    deps.require_ref::<GenericEnc>(())?.type_snapshot,
                ),
                LiftedGenericEncTask::Const(c) => match c.kind() {
                    ty::ConstKind::Param(param) => vcx.mk_local_decl(
                        vcx.alloc_str(param.name.as_str()),
                        deps.require_ref::<GenericEnc>(())?.type_snapshot,
                    ),
                    _ => todo!("lifted generic const {c:?}")
                }
                // LiftedGenericEncTask::Const(c) => todo!("lifted generic const {c:?}"),
            });
            deps.emit_output_ref(*task_key, output_ref)?;
            Ok(((), ()))
        })
    }
}
