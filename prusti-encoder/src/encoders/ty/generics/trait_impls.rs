use std::iter;

use prusti_interface::{PrustiError, specs::specifications::SpecQuery};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Domain, Method, MethodIdn, vir_format_identifier};

use crate::{
    encoders::{
        FunctionCallEnc, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, Pure, mir_fn::{CallTaskDescription, RustSignature}, pure::spec::MirSpecEncMode, ty::{
            RustTyDecomposition,
            generics::{GArgs, GArgsCastEnc, GArgsTyEnc, GParams, GenericParamsEnc, traits::TraitEnc},
        }
    },
    trait_support::is_function_with_body,
};

pub struct TraitImplEnc;

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for (dom, methods) in Self::all_outputs_local_no_errors() {
            program.add_domain(dom);
            for method in methods {
                program.add_method(method);
            }
        }
    }

    type TaskDescription<'vir> = DefId;
    type OutputFullLocal<'vir> = (Domain<'vir>, Vec<Method<'vir>>);

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
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(ctx, trait_ref.args))?;

            let mut axioms = Vec::new();
            let mut methods = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, *task_key);
            let implementing_ty = implementing_ty.ty.name();

            let impl_fun = trait_data.impl_fun;
            let trait_ty_decls = params.ty_decls().to_vec();
            let trait_const_decls = params.const_decls().to_vec();
            let trait_tys = args.get_ty();
            let trait_consts = args.get_const();

            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(vcx, "{trait_name}_impl_{implementing_ty}_{idx}_does_impl"),
                vir::expr! {forall ..[trait_ty_decls] :: {[impl_fun(trait_tys, trait_consts)]} [impl_fun(trait_tys, trait_consts)]},
            ));

            for impl_item in tcx.associated_items(task_key).in_definition_order() {
                let trait_item_def_id = impl_item.trait_item_def_id.unwrap();
                let impl_item_def_id = impl_item.def_id;
                let impl_span = vcx.tcx().def_span(impl_item_def_id);
                let item_name = tcx.item_name(impl_item_def_id);

                // construct arguments for assoc_item function
                // parameters of the trait are substituted
                // by the arguments used in the impl
                // parameters of the associated type are kept

                // parameters of assoc item include already substituted arguments
                let impl_item_params = GParams::from(impl_item_def_id);
                let assoc_params = deps
                    .require_dep::<GenericParamsEnc>(impl_item_params)
                    .unwrap();

                let assoc_ty_decls = assoc_params.ty_decls();
                let assoc_const_decls = assoc_params.const_decls();

                // Combine substituted trait ty decls with the decls of the associated type
                let mut trait_ty_decls = trait_ty_decls.clone();
                trait_ty_decls.extend_from_slice(&assoc_ty_decls[params.ty_exprs().len()..]);
                let mut trait_const_decls = trait_const_decls.clone();
                trait_const_decls
                    .extend_from_slice(&assoc_const_decls[params.const_exprs().len()..]);

                // Combine substituted trait params with the params of the associated type
                let trait_tys = vcx.alloc_slice(
                    &iter::empty()
                        .chain(args.get_ty().to_owned())
                        .chain(assoc_params.ty_exprs()[params.ty_exprs().len()..].to_owned())
                        .collect::<Vec<_>>(),
                );
                let trait_consts = vcx.alloc_slice(
                    &iter::empty()
                        .chain(args.get_const().to_owned())
                        .chain(assoc_params.const_exprs()[params.const_exprs().len()..].to_owned())
                        .collect::<Vec<_>>(),
                );

                match impl_item.kind {
                    ty::AssocKind::Type { .. } => {
                        let assoc_type = trait_data.assoc_types.get(&trait_item_def_id).unwrap();

                        // the type we want to resolve the type alias to
                        let assoc_type_expr = assoc_params.ty_expr(
                            deps,
                            RustTyDecomposition::from_ty(
                                tcx.type_of(impl_item_def_id).instantiate_identity(),
                                impl_item_params,
                            ),
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{trait_name}_impl_{implementing_ty}_{idx}_assoc_type_{item_name}"),
                            vir::expr! {forall ..[trait_ty_decls], ..[trait_const_decls] :: {[assoc_type(trait_tys, trait_consts)]} ([assoc_type(trait_tys, trait_consts)]) == (assoc_type_expr)},
                        ));
                    }
                    ty::AssocKind::Fn { .. } => {
                        let trait_data_dep = deps.require_ref::<TraitEnc>(trait_did)?;
                        let assoc_fn = trait_data_dep.assoc_funcs.get(&trait_item_def_id).unwrap();
                        let local_defs =
                            deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                                def_id: impl_item_def_id,
                                all_locals: false,
                            })?;
                        let arg_count = local_defs.arg_count + 1;
                        //let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
                        //let return_type = local_defs.snap_ty_return();
                        let generics = deps.require_dep::<GenericParamsEnc>(impl_item_params)?;
                        let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
                        let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
                        let func_ret = local_defs.local_decl_ret();

                        let trait_item_is_pure = crate::encoders::with_proc_spec(
                            SpecQuery::GetProcKind(
                                trait_item_def_id,
                                ty::List::identity_for_item(vcx.tcx(), trait_item_def_id),
                            ),
                            |spec| spec.kind.is_pure().unwrap_or_default(),
                        )
                        .unwrap_or_default();
                        let impl_item_is_pure = crate::encoders::with_proc_spec(
                            SpecQuery::GetProcKind(
                                impl_item_def_id,
                                ty::List::identity_for_item(vcx.tcx(), impl_item_def_id),
                            ),
                            |spec| spec.kind.is_pure().unwrap_or_default(),
                        )
                        .unwrap_or_default();

                        let trait_item_has_body =
                            is_function_with_body(vcx.tcx(), trait_item_def_id);
                        let impl_item_has_body = is_function_with_body(vcx.tcx(), impl_item_def_id);

                        //let trait_item_spec = deps.require_dep_spanned::<MirSpecEnc>((trait_item_def_id, impl_item_def_id, MirSpecEncMode::PureWithoutResult), impl_span)?;
                        let impl_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                            (
                                impl_item_def_id,
                                impl_item_def_id,
                                MirSpecEncMode::PureWithoutResult,
                            ),
                            impl_span,
                        )?;
                        let pres = vcx.mk_conj(&impl_item_spec.pres);

                        let signature = RustSignature::new(trait_item_def_id);
                        let gargs = GArgs::new(impl_item_params, trait_ref.args);
                        // TODO: trait_ref.args here is probably insufficient: what if the method itself is generic?

                        let pre_func_call = assoc_fn.pre_func.call()(
                            vcx.alloc_slice(
                                &func_args
                                    .iter()
                                    .zip(signature.inputs)
                                    .map(|(arg, ty)| {
                                        let normalized = ty.decompose_compare_normalize(impl_item_params, gargs);
                                        let caster = deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                                        caster.cast_to_callee_ctx(vcx.mk_local_ex(arg))
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            trait_tys,
                            trait_consts,
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_impl_{implementing_ty}_{idx}_fn_pre_{item_name}",
                            ),
                            vir::expr! {
                                forall ..[func_args], ..[trait_ty_decls] :: {[pre_func_call]}
                                    (pres) ==> (pre_func_call)
                            },
                        ));
                        let mut posts = impl_item_spec.posts;
                        if impl_item_has_body && impl_item_is_pure {
                            let pure_func = deps.require_dep::<FunctionCallEnc>(
                                CallTaskDescription::new(
                                    impl_item_def_id,
                                    ty::List::identity_for_item(vcx.tcx(), impl_item_def_id),
                                    impl_item_def_id,
                                )
                                .resolve_trait_calls(false),
                            )?;
                            let pure_func_app = pure_func.call_pure(
                                func_args
                                    .iter()
                                    .zip(signature.inputs)
                                    .map(|(arg, ty)| {
                                        // TODO: test if this works
                                        let normalized = ty.decompose_compare_normalize(impl_item_params, gargs);
                                        let caster = deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                                        caster.cast_to_callee_ctx(vcx.mk_local_ex(arg))
                                    })
                                    .collect::<Vec<_>>(),
                            );
                            posts.push(vir::expr! {
                                ([func_ret]) == ([pure_func_app])
                            });
                        }
                        let posts = vcx.mk_conj(&posts);
                        let post_func_call = assoc_fn.post_func.call()(
                            {
                                let normalized = signature.output.decompose_compare_normalize(impl_item_params, gargs);
                                let caster = deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                                caster.cast_to_callee_ctx(vcx.mk_local_ex(func_ret))
                            },
                            vcx.alloc_slice(
                                &func_args
                                    .iter()
                                    .zip(signature.inputs)
                                    .map(|(arg, ty)| {
                                        let normalized = ty.decompose_compare_normalize(impl_item_params, gargs);
                                        let caster = deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                                        caster.cast_to_callee_ctx(vcx.mk_local_ex(arg))
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            trait_tys,
                            trait_consts,
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_impl_{implementing_ty}_{idx}_fn_post_{item_name}",
                            ),
                            vir::expr! {
                                forall [func_ret], ..[func_args], ..[trait_ty_decls] :: {[post_func_call]}
                                    (post_func_call) ==> (posts)
                            },
                        ));

                        let trait_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                            (trait_item_def_id, impl_item_def_id, MirSpecEncMode::Impure),
                            impl_span,
                        )?;
                        let impl_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                            (impl_item_def_id, impl_item_def_id, MirSpecEncMode::Impure),
                            impl_span,
                        )?;

                        let mut pre_weaken_pres = Vec::new();
                        let mut args = Vec::with_capacity(arg_count + impl_item_params.count());
                        for arg_idx in (0..arg_count).map(mir::Local::from) {
                            let name_p = local_defs[arg_idx].local.name;
                            args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                            if arg_idx != mir::RETURN_PLACE {
                                pre_weaken_pres.push(local_defs[arg_idx].impure_pred);
                            }
                        }
                        // TODO: wands

                        pre_weaken_pres.extend(trait_item_spec.pres.clone());

                        methods.push(vcx.mk_method(
                            MethodIdn::<(vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>::new(
                                vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}_fn_pre_weaken_{item_name}"),
                                (ref_args, assoc_params.ty_args(), generics.const_args()),
                            ),
                            (args.as_slice(), assoc_params.ty_decls(), generics.const_decls()),
                            &[],
                            vcx.alloc_slice(&pre_weaken_pres),
                            &[],
                            Some(vcx.alloc_slice(&[
                                vcx.mk_cfg_block(
                                    &vir::CfgBlockLabelData::Start,
                                    &[],
                                    vcx.alloc_slice(&impl_item_spec.pres.iter()
                                        .map(|pre| vcx.with_span(impl_span, |vcx| {
                                            // TODO: make span point precisely to the precondition we cannot show
                                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                                Some(vec![PrustiError::verification("trait implementation is not a behavioral subtype (precondition is not weakened)", impl_span.into())])
                                            });
                                            vcx.mk_exhale_stmt(pre)
                                        }))
                                        .collect::<Vec<_>>()),
                                    vcx.alloc(vir::TerminatorStmtData::Exit),
                                )
                            ])),
                        ));

                        let mut post_strengthen_pres = Vec::new();
                        let mut args = Vec::with_capacity(arg_count + impl_item_params.count());
                        for arg_idx in (0..arg_count).map(mir::Local::from) {
                            let name_p = local_defs[arg_idx].local.name;
                            args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                            if arg_idx != mir::RETURN_PLACE {
                                post_strengthen_pres.push(local_defs[arg_idx].impure_pred);
                            }
                        }
                        // TODO: wands

                        post_strengthen_pres.extend(trait_item_spec.pres);

                        // exceptionally, we also put the allocated result in the precondition
                        post_strengthen_pres.push(local_defs[mir::RETURN_PLACE].impure_pred);

                        // here we inhale the impl postconditions, since they
                        // can contain "old" variables
                        let mut stmts = Vec::new();
                        for post in &impl_item_spec.posts {
                            stmts.push(vcx.mk_inhale_stmt(post));
                        }
                        if impl_item_has_body && impl_item_is_pure {
                            let pure_func = deps.require_dep::<FunctionCallEnc>(
                                CallTaskDescription::new(
                                    impl_item_def_id,
                                    ty::List::identity_for_item(vcx.tcx(), impl_item_def_id),
                                    impl_item_def_id,
                                )
                                .resolve_trait_calls(false),
                            )?;
                            let pure_func_app = pure_func.call_pure(
                                local_defs
                                    .args()
                                    .map(|arg| arg.impure_snap)
                                    .collect::<Vec<_>>(),
                            );
                            stmts.push(vcx.mk_inhale_stmt(vir::expr! {
                                ([local_defs[mir::RETURN_PLACE].impure_snap]) == ([pure_func_app])
                            }));
                        }
                        for post in trait_item_spec.posts {
                            vcx.with_span(impl_span, |vcx| {
                                // TODO: make span point precisely to the postcondition we cannot show
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification("trait implementation is not a behavioral subtype (postcondition is not strengthened)", impl_span.into())])
                                });
                                stmts.push(vcx.mk_exhale_stmt(post));
                            });
                        }
                        if trait_item_has_body && trait_item_is_pure {
                            let pure_func = deps.require_dep::<FunctionCallEnc>(
                                CallTaskDescription::new(
                                    impl_item_def_id,
                                    trait_ref.args,
                                    trait_item_def_id,
                                )
                                .resolve_trait_calls(false),
                            )?;
                            let pure_func_app = pure_func.call_pure(
                                local_defs
                                    .args()
                                    .map(|arg| arg.impure_snap)
                                    .collect::<Vec<_>>(),
                            );
                            vcx.with_span(impl_span, |vcx| {
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification("trait implementation is not a behavioral subtype (body is not strengthened)", impl_span.into())])
                                });
                                stmts.push(vcx.mk_exhale_stmt(vir::expr! {
                                    ([local_defs[mir::RETURN_PLACE].impure_snap]) == ([pure_func_app])
                                }));
                            });
                        }

                        methods.push(vcx.mk_method(
                            MethodIdn::<(vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>::new(
                                vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}_fn_post_strengthen_{item_name}"),
                                (ref_args, assoc_params.ty_args(), generics.const_args()),
                            ),
                            (args.as_slice(), assoc_params.ty_decls(), generics.const_decls()),
                            &[],
                            vcx.alloc_slice(&post_strengthen_pres),
                            &[],
                            Some(vcx.alloc_slice(&[
                                vcx.mk_cfg_block(
                                    &vir::CfgBlockLabelData::Start,
                                    &[],
                                    vcx.alloc_slice(&stmts),
                                    vcx.alloc(vir::TerminatorStmtData::Exit),
                                )
                            ])),
                        ));
                    }
                    ty::AssocKind::Const { .. } => (), // noop?
                }
            }

            Ok((
                (
                    vcx.mk_domain(
                        vir_format_identifier!(
                            vcx,
                            "trait_{trait_name}_impl_{implementing_ty}_{idx}"
                        ),
                        &[],
                        vcx.alloc_slice(&axioms),
                        &[],
                        None,
                    ),
                    methods,
                ),
                (),
            ))
        })
    }
}
