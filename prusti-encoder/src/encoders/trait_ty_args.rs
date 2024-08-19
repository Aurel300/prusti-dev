use prusti_rustc_interface::middle::ty::TraitRef;
use task_encoder::TaskEncoder;

use crate::encoders::lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc};

/// Encodes the type arguments of a trait (e.g the `U` in `Into<U>`). The result
/// of this encoder should be used as the type arguments for
/// [super::r#trait::TraitEncOutputRef::implements].
pub struct TraitTyArgsEnc;

impl TaskEncoder for TraitTyArgsEnc {
    task_encoder::encoder_cache!(TraitTyArgsEnc);
    type TaskDescription<'tcx> = TraitRef<'tcx>;

    type OutputFullLocal<'vir> = &'vir [vir::Expr<'vir>];

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let args = vcx.alloc_slice(
                &task_key
                    .args
                    .types()
                    .skip(1)
                    .map(|ty| {
                        deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(ty)
                            .unwrap()
                            .expr(vcx)
                    })
                    .collect::<Vec<_>>(),
            );
            Ok((args, ()))
        })
    }
}
