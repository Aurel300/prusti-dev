use prusti_rustc_interface::{middle::ty::AssocKind, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Domain, vir_format_identifier};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc, traits::TraitEnc},
};

pub struct TraitImplEnc;

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for dom in TraitImplEnc::all_outputs_local_no_errors() {
            program.add_domain(dom);
        }
    }

    type TaskDescription<'vir> = (DefId, GParams<'vir>);
    type OutputFullLocal<'vir> = Domain<'vir>;

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let params = deps.require_dep::<GenericParamsEnc>(GParams::from(task_key.0))?;

            let trait_ref = tcx
                .impl_trait_ref(task_key.0)
                .unwrap()
                .instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_dep::<TraitEnc>(trait_did)?;

            let args = deps
                .require_dep::<GArgsTyEnc>(GArgs::new(GParams::from(task_key.0), trait_ref.args))?;

            let mut axs = Vec::new();

            let struct_ty = tcx.type_of(task_key.0).instantiate_identity();

            let impl_fun = trait_data.impl_fun;
            let trait_ty_decls = params
                .ty_decls()
                .iter()
                .map(|dec| dec.upcast_ty())
                .collect::<Vec<_>>();
            let trait_tys = args.get_ty();
            axs.push(vcx.mk_domain_axiom(
                vir_format_identifier!(vcx, "{}_impl_{}", trait_data.trait_name, struct_ty),
                vir::expr! {forall ..[trait_ty_decls] :: {[impl_fun(trait_tys)]} [impl_fun(trait_tys)]},
            ));

            tcx.associated_items(task_key.0)
                .in_definition_order()
                .filter(|item| matches!(item.kind, AssocKind::Type { data: _ }))
                .for_each(|impl_item| {
                    trait_data
                        .type_did_fun_mapping
                        .iter()
                        .filter(|(assoc_did, _)| Some(*assoc_did) == impl_item.trait_item_def_id)
                        .for_each(|(_, assoc_fun)| {
                            let params = deps
                                .require_dep::<GenericParamsEnc>(GParams::from(impl_item.def_id))
                                .unwrap();
                            let assoc_type_expr = params.ty_expr(
                                deps,
                                RustTyDecomposition::from_ty(
                                    tcx.type_of(impl_item.def_id).instantiate_identity(),
                                    tcx,
                                    GParams::from(impl_item.def_id),
                                ),
                            );
                            axs.push(vcx.mk_domain_axiom(
                                vir_format_identifier!(
                                    vcx,
                                    "{}_Assoc_{}_{}",
                                    trait_data.trait_name,
                                    tcx.item_name(impl_item.def_id),
                                    struct_ty
                                ),
                                vir::expr! {forall ..[trait_ty_decls] :: {[assoc_fun(trait_tys)]} ([assoc_fun(trait_tys)]) == (assoc_type_expr)},
                            ))
                        });
                });

            let dom = vcx.mk_domain(
                vir_format_identifier!(
                    vcx,
                    "t_{}_{}",
                    trait_data.trait_name,
                    tcx.type_of(task_key.0).instantiate_identity().to_string()
                ),
                &[],
                vcx.alloc_slice(&axs),
                &[],
                None,
            );

            Ok((dom, ()))
        })
    }
}
