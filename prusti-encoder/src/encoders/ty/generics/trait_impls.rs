use std::iter;

use prusti_rustc_interface::{middle::ty::AssocKind, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Domain, vir_format_identifier};

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

            let all_impls = tcx.trait_impls_in_crate(task_key.krate);
            let idx = all_impls.iter().position(|did| did == task_key).unwrap();

            let ctx = GParams::from(*task_key);
            let params = deps.require_dep::<GenericParamsEnc>(ctx)?;

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_dep::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(GParams::from(*task_key), trait_ref.args))?;

            let mut axioms = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, *task_key);
            let implementing_ty = implementing_ty.ty.name();

            let impl_fun = trait_data.impl_fun;
            let trait_ty_decls = params.ty_decls().to_vec();
            let trait_tys = args.get_ty();

            axioms.push(
                vcx.mk_domain_axiom(
                    vir_format_identifier!(vcx, "{}_impl_{idx}_{implementing_ty}", trait_data.trait_name),
                    vir::expr! {forall ..[trait_ty_decls] :: {[impl_fun(trait_tys)]} [impl_fun(trait_tys)]}
                )
            );

            for impl_item in tcx.associated_items(task_key).in_definition_order() {
                let trait_item_def_id = impl_item.trait_item_def_id.unwrap();
                let impl_item_def_id = impl_item.def_id;
                let item_name = tcx.item_name(impl_item_def_id);
                match impl_item.kind {
                    AssocKind::Type { .. } => {
                        let assoc_fun = trait_data.assoc_types.get(&trait_item_def_id).unwrap();
                        // construct arguments for assoc_item function
                        // parameters of the trait are substituted
                        // by the arguments used in the impl
                        // parameters of the associated type are kept

                        // parameters of assoc item include already substituted arguments
                        let assoc_params = deps
                            .require_dep::<GenericParamsEnc>(GParams::from(impl_item_def_id))
                            .unwrap();

                        // the type we want to resolve the type alias to
                        let assoc_type_expr = assoc_params.ty_expr(
                            deps,
                            RustTyDecomposition::from_ty(
                                tcx.type_of(impl_item_def_id).instantiate_identity(),
                                GParams::from(impl_item_def_id),
                            ),
                        );
                        let assoc_decls = assoc_params.ty_decls();

                        // Combine substituted trait ty decls with the decls of the associated type
                        let mut trait_ty_decls = trait_ty_decls.clone();
                        trait_ty_decls.extend_from_slice(&assoc_decls[params.ty_exprs().len()..]);

                        // Combine substituted trait params with the params of the associated type
                        let trait_tys = vcx.alloc_slice(&iter::empty().chain(args.get_ty().to_owned()).chain(assoc_params.ty_exprs()[params.ty_exprs().len()..].to_owned()).collect::<Vec<_>>());
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{trait_name}_assoc_type_{implementing_ty}_{idx}_{item_name}"),
                            vir::expr! {forall ..[trait_ty_decls] :: {[assoc_fun(trait_tys)]} ([assoc_fun(trait_tys)]) == (assoc_type_expr)},
                        ));
                    }
                    AssocKind::Fn { ../*name, has_self*/ } => {
                        // TODO
                    },
                    AssocKind::Const { .. } => (), // noop?
                }
            }

            Ok((
                vcx.mk_domain(
                    vir_format_identifier!(vcx, "t_{trait_name}_{implementing_ty}_{idx}"),
                    &[],
                    vcx.alloc_slice(&axioms),
                    &[],
                    None,
                ),
                (),
            ))
        })
    }
}
