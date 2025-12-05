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

    type TaskDescription<'vir> = DefId;
    type OutputFullLocal<'vir> = Domain<'vir>;

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let ctx = GParams::from(*task_key);

            let params = deps.require_dep::<GenericParamsEnc>(ctx)?;

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_dep::<TraitEnc>(trait_did)?;

            // for some reason, just using all args (which includes the struct at index 0)
            // leads to a cycle for simple test cases -> split up and add struct manually
            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(ctx, &trait_ref.args[1..]))?;

            let struct_ty = tcx.type_of(task_key).instantiate_identity();
            let struct_ty_expr =
                params.ty_expr(deps, RustTyDecomposition::from_ty(struct_ty, tcx, ctx));

            let mut vec = Vec::new();
            vec.push(struct_ty_expr);
            vec.append(&mut args.get_ty().to_owned());

            let mut axs = Vec::new();

            let struct_ty = tcx.type_of(task_key).instantiate_identity();

            let impl_fun = trait_data.impl_fun;
            let trait_ty_decls = params
                .ty_decls()
                .iter()
                .map(|dec| dec.upcast_ty())
                .collect::<Vec<_>>();
            let trait_tys = vcx.alloc_slice(&vec);
            axs.push(
                vcx.mk_domain_axiom(
                vir_format_identifier!(vcx, "{}_impl_{}", trait_data.trait_name, struct_ty),
                if trait_ty_decls.is_empty() {
                    vir::expr! {[impl_fun(trait_tys)]}
                } else {
                    vir::expr! {forall ..[trait_ty_decls] :: {[impl_fun(trait_tys)]} [impl_fun(trait_tys)]}
                }
            ));

            tcx.associated_items(*task_key)
                .in_definition_order()
                .filter(|item| matches!(item.kind, AssocKind::Type { data: _ }))
                .for_each(|impl_item| {
                    trait_data
                        .type_did_fun_mapping
                        .iter()
                        .filter(|(assoc_did, _)| Some(*assoc_did) == impl_item.trait_item_def_id)
                        .for_each(|(_, assoc_fun)| {
                            // construct arguments for assoc_item function
                            // parameters of the trait are substituted 
                            // by the arguments used in the impl
                            // parameters of the associated type are kept

                            // parameters of assoc item include already substituted arguments
                            let assoc_params = deps
                                .require_dep::<GenericParamsEnc>(GParams::from(impl_item.def_id))
                                .unwrap();

                            // the type we want to resolve the type alias to
                            let assoc_type_expr = assoc_params.ty_expr(
                                deps,
                                RustTyDecomposition::from_ty(
                                    tcx.type_of(impl_item.def_id).instantiate_identity(),
                                    tcx,
                                    GParams::from(impl_item.def_id),
                                ),
                            );
                            let assoc_decls = assoc_params
                                .ty_decls()
                                .iter()
                                .map(|dec| dec.upcast_ty())
                                .collect::<Vec<_>>();

                            // Combine substituted trait params with the params of the associated type
                            let mut trait_ty_decls = trait_ty_decls.clone();
                            trait_ty_decls.extend_from_slice(&assoc_decls[params.ty_exprs().len()..]);

                            // Combine substituted trait params decls with the params of the associated type
                            let mut vec = vec.clone();
                            vec.extend_from_slice(&assoc_params.ty_exprs()[params.ty_exprs().len()..]);
                            let trait_tys = vcx.alloc_slice(&vec);

                            axs.push(vcx.mk_domain_axiom(
                                vir_format_identifier!(
                                    vcx,
                                    "{}_Assoc_{}_{}",
                                    trait_data.trait_name,
                                    tcx.item_name(impl_item.def_id),
                                    struct_ty
                                ),
                                if trait_ty_decls.is_empty() {
                                    vir::expr! {([assoc_fun(trait_tys)]) == (assoc_type_expr)}
                                } else {
                                    vir::expr! {forall ..[trait_ty_decls] :: {[assoc_fun(trait_tys)]} ([assoc_fun(trait_tys)]) == (assoc_type_expr)}
                                }
                            ));
                        });
                });

            let dom = vcx.mk_domain(
                vir_format_identifier!(
                    vcx,
                    "t_{}_{}",
                    trait_data.trait_name,
                    tcx.type_of(*task_key).instantiate_identity().to_string()
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
