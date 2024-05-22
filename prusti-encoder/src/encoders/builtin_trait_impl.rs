use prusti_rustc_interface::middle::ty::TraitRef;
use task_encoder::TaskEncoder;
use vir::vir_format_identifier;

use crate::encoders::lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc};

use super::{TraitEnc, TraitTyArgsEnc};

pub struct BuiltinTraitImplEnc;

impl TaskEncoder for BuiltinTraitImplEnc {
    task_encoder::encoder_cache!(BuiltinTraitImplEnc);
    type TaskDescription<'tcx> = TraitRef<'tcx>;

    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let encoded_trait = deps.require_ref::<TraitEnc>(task_key.def_id)?;
        vir::with_vcx(|vcx| {
            let lifted_ty_expr = deps
                .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(task_key.self_ty())?
                .expr(vcx);
            let axiom = vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "builtin_implements_{}_{:?}_axiom",
                    vcx.tcx().def_path_str(task_key.def_id),
                    task_key.args
                ),
                encoded_trait.implements(
                    lifted_ty_expr,
                    deps.require_local::<TraitTyArgsEnc>(*task_key)?
                ),
            );
            let domain = vcx.mk_domain(
                vir_format_identifier!(
                    vcx,
                    "builtin_implements_{}_{:?}_domain",
                    vcx.tcx().def_path_str(task_key.def_id),
                    task_key.args
                ),
                &[],
                vcx.alloc_slice(&[axiom]),
                &[],
            );
            Ok((domain, ()))
        })
    }
}
