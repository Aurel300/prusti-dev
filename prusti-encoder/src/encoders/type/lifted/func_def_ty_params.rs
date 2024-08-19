use prusti_rustc_interface::middle::ty::{self, ParamTy, Ty, TyKind};
use std::collections::HashSet;
use task_encoder::{EncodeFullResult, TaskEncoder};

use crate::generic_args_support::get_unique_param_tys_in_order;

use super::generic::{LiftedGeneric, LiftedGenericEnc};

/// Encodes the type parameters of a (possibly monomorphised) function
/// definition. It takes as input a type substitution and returns the list of
/// type parameters required for the function definition. For non-monomorphised
/// functions, the type substitution will always be the identity substitution,
/// and for monomorphised functions, the type substitution will be the
/// substitution at the call site. The logic for both cases is the same: all
/// unique type parameters are extracted from the substitution.
pub struct LiftedTyParamsEnc;

impl TaskEncoder for LiftedTyParamsEnc {
    task_encoder::encoder_cache!(LiftedTyParamsEnc);
    type TaskDescription<'tcx> = ty::GenericArgsRef<'tcx>;

    type OutputFullLocal<'vir> = &'vir [LiftedGeneric<'vir>];

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let ty_args = get_unique_param_tys_in_order(task_key)
                .map(|ty| deps.require_ref::<LiftedGenericEnc>(ty).unwrap())
                .collect::<Vec<_>>();
            Ok((vcx.alloc_slice(&ty_args), ()))
        })
    }
}
