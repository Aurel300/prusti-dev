use prusti_rustc_interface::middle::ty::TraitRef;
use task_encoder::TaskEncoder;
use vir::vir_format_identifier;

use crate::{
    encoders::lifted::ty::{EncodeGenericsAsLifted, LiftedTyEnc},
    generic_args_support::get_unique_param_tys_in_order,
};

use super::{
    lifted::generic::LiftedGenericEnc,
    TraitEnc, TraitTyArgsEnc,
};

/// Encodes axioms for types that implement traits via the compiler's "builtin"
/// logic, i.e. not via a user-defined `impl`. For example, `u32` implements the
/// `Sized` trait because it is builtin. User-defined types may also implement a
/// trait in this manner, for example, an ADT composed of sized types also
/// automatically implements `Sized`
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
            let ty_params = get_unique_param_tys_in_order(task_key.args).collect::<Vec<_>>();
            let implements_expr = encoded_trait.implements(
                lifted_ty_expr,
                deps.require_local::<TraitTyArgsEnc>(*task_key)?,
            );
            let implements_expr = if ty_params.len() > 0 {
                vcx.mk_forall_expr(
                    vcx.alloc_slice(
                        &ty_params
                            .iter()
                            .map(|p| deps.require_ref::<LiftedGenericEnc>(*p).unwrap().decl())
                            .collect::<Vec<_>>(),
                    ),
                    vcx.alloc_slice(&[vcx.mk_trigger(vcx.alloc_slice(&[implements_expr]))]),
                    implements_expr
                )
            } else {
                implements_expr
            };
            let axiom = vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "builtin_implements_{}_{:?}_axiom",
                    vcx.tcx().def_path_str(task_key.def_id),
                    task_key.args
                ),
                implements_expr,
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
