use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::FunctionIdn;

use super::{RustTy, generics::GenericParamsEnc, pure::TyPureEnc};

/// Emits the canonical zero-sized-value function `s_T_zst(<T's params>): s_T` for
/// a (base) type `T`. All values of a ZST are equal, so this uninterpreted
/// function names that single value. It is required on demand (keyed on the base
/// `RustTy`) from `TyUsePureEnc` only for decompositions whose `is_zst` is set —
/// see [`super::RustTyDecomposition::is_zst`] — so it is never emitted for types
/// that are not (known to be) zero-sized. Keeping it in its own encoder (rather
/// than in the snapshot) is what lets the snapshot stay keyed purely on the base
/// type: `is_zst` is an instantiation property and must not vary the snapshot's
/// task key (that would emit the `s_T` domain twice).
pub struct TyZstEnc;

impl TaskEncoder for TyZstEnc {
    task_encoder::encoder_cache!(TyZstEnc);
    const ENCODER_NAME: &'static str = "type zst encoder";

    type TaskDescription<'vir> = RustTy<'vir>;
    type OutputFullDependency<'vir> =
        FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let ty = *task_key;
        // The snapshot domain (for the result type `s_T`) and the type's params.
        let ty_pure = deps.require_ref::<TyPureEnc>(ty)?;
        let params = deps.require_dep::<GenericParamsEnc>(ty.params)?;
        vir::with_vcx(|vcx| {
            let self_type = (ty_pure.domain)();
            let fn_idn = FunctionIdn::new(
                vir::ViperIdent::new(vir::vir_format!(vcx, "s_{}_zst", ty.name())),
                (params.ty_args(), params.const_args()),
                self_type,
            );
            // An uninterpreted, body-less function: the canonical ZST value.
            let function = vcx.mk_function(
                fn_idn,
                (params.ty_decls(), params.const_decls()),
                &[],
                &[],
                None,
                None,
            );
            Ok((function, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for function in Self::all_outputs_local_no_errors(program) {
            program.add_function(function);
        }
    }
}
