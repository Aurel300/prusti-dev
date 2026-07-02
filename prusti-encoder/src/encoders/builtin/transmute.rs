use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn, HasType, MethodIdn};

use crate::encoders::{
    ConstEnc, Pure, TyUseImpureEnc,
    r#const::ConstEncTask,
    ty::{
        RustTy, RustTyDecomposition, RustTyNormalized, TySpecifics,
        generics::{GArgsCastEnc, GParams, GenericParamsEnc, TyExprEnc},
        interpretation::float::FloatDomain,
        pure::{TyPure, TyPurePrimData, TyPurePrimDataKind},
        use_pure::{TyUsePure, TyUsePureEnc},
    },
};

pub struct TransmuteUseEnc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TransmuteUseTask<'vir> {
    pub src: RustTyDecomposition<'vir>,
    pub dst: RustTyDecomposition<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TransmuteUseOutput<'vir> {
    method_idn: MethodIdn<'vir, (vir::Ref, vir::TyVal, vir::Ref, vir::TyVal)>,
    src_ty: vir::ExprTyVal<'vir>,
    dst_ty: vir::ExprTyVal<'vir>,
}

impl<'vir> TransmuteUseOutput<'vir> {
    pub fn transmute(
        self,
        src: vir::ExprRef<'vir>,
        dst: vir::ExprRef<'vir>,
    ) -> vir::StmtKindData<'vir> {
        (self.method_idn)(src, self.src_ty, dst, self.dst_ty)
    }
}

impl TaskEncoder for TransmuteUseEnc {
    task_encoder::encoder_cache!(TransmuteUseEnc);
    const ENCODER_NAME: &'static str = "transmute use encoder";
    type TaskDescription<'vir> = TransmuteUseTask<'vir>;
    type OutputFullDependency<'vir> = TransmuteUseOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let task_key: TransmuteUseTask<'vir> = *task_key;
        let method_idn = deps.require_dep::<TransmuteEnc>(())?;
        let src_ty = deps.require_dep::<TyExprEnc>(task_key.src)?;
        let dst_ty = deps.require_dep::<TyExprEnc>(task_key.dst)?;
        Ok((
            (),
            TransmuteUseOutput {
                method_idn,
                src_ty,
                dst_ty,
            },
        ))
    }
}

struct TransmuteEnc;

impl TaskEncoder for TransmuteEnc {
    task_encoder::encoder_cache!(TransmuteEnc);
    const ENCODER_NAME: &'static str = "transmute encoder";
    type TaskDescription<'vir> = ();

    type OutputFullDependency<'vir> =
        vir::MethodIdn<'vir, (vir::Ref, vir::TyVal, vir::Ref, vir::TyVal)>;
    type OutputFullLocal<'vir> = vir::Method<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        todo!()
    }
}
