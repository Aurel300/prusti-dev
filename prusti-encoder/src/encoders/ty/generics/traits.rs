use std::collections::HashMap;

use prusti_interface::specs::is_spec_fn;
use prusti_rustc_interface::{middle::{mir, ty::AssocKind}, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, MethodIdn, vir_format_identifier};

use crate::encoders::{MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, pure::spec::MirSpecEncMode, ty::generics::{GParams, GenericParamsEnc}};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitData<'vir> {
    pub trait_name: &'vir str,
    pub assoc_types: HashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>>,
    pub assoc_funcs: HashMap<DefId, TraitAssocFnData<'vir>>,
    pub impl_fun: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitAssocFnData<'vir> {
    pub pre_func: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub post_func: FunctionIdn<'vir, (vir::Snap, vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub call_stub: MethodIdn<'vir, (vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>,
}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputFullDependency<'vir> = TraitData<'vir>;
    type OutputFullLocal<'vir> = (
        vir::Domain<'vir>,
        Vec<vir::Method<'vir>>,
    );

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for (dom, methods) in Self::all_outputs_local_no_errors() {
            program.add_domain(dom);
            for method in methods {
                program.add_method(method);
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let trait_params = GParams::from(*task_key);
            let trait_generics = deps.require_dep::<GenericParamsEnc>(trait_params)?;

            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());
            let mut axioms = Vec::new();
            let mut funcs = Vec::new();
            let mut methods = Vec::new();
            let mut assoc_types = HashMap::new();
            let mut assoc_funcs = HashMap::new();
            for item in tcx.associated_items(task_key).in_definition_order() {
                let def_id = item.def_id;
                let span = vcx.tcx().def_span(def_id);

                // Prusti specifications on trait methods emit additional spec-
                // only fn items (with default implementations). We need to
                // ignore these items.
                if is_spec_fn(tcx, def_id) {
                    continue;
                }

                // item_generics also includes parameters of trait itself
                let item_params = GParams::from(def_id);
                let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
                let item_name = tcx.item_name(def_id);

                match item.kind {
                    AssocKind::Type { .. } => {
                        let type_func = FunctionIdn::new(
                            vir_format_identifier!(vcx, "{trait_name}_assoc_type_{item_name}"),
                            (item_generics.ty_args(), item_generics.const_args()),
                            vir::TYPE_TYVAL,
                        );
                        assoc_types.insert(def_id, type_func);
                        funcs.push(vcx.mk_domain_function(type_func, false, None));
                    }
                    AssocKind::Fn { .. } => {
                        let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                            def_id,
                            all_locals: false,
                        })?;
                        let arg_count = local_defs.arg_count + 1;
                        let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
                        let return_type = local_defs.snap_ty_return();
                        let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
                        let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
                        let func_ret = local_defs.local_decl_ret();

                        let pre_func = FunctionIdn::new(
                            vir_format_identifier!(vcx, "{trait_name}_fn_pre_{item_name}"),
                            (arg_types, item_generics.ty_args(), item_generics.const_args()),
                            vir::TYPE_BOOL,
                        );
                        let post_func = FunctionIdn::new(
                            vir_format_identifier!(vcx, "{trait_name}_fn_post_{item_name}"),
                            // TODO: old(arg) types (if applicable)
                            (return_type, arg_types, item_generics.ty_args(), item_generics.const_args()),
                            vir::TYPE_BOOL,
                        );
                        // TODO: spec functions for each pledge
                        let call_stub = MethodIdn::new(
                            vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                            (ref_args, item_generics.ty_args(), item_generics.const_args()),
                        );
                        assoc_funcs.insert(def_id, TraitAssocFnData {
                            pre_func,
                            post_func,
                            call_stub,
                        });
                        funcs.push(vcx.mk_domain_function(pre_func, false, None));
                        funcs.push(vcx.mk_domain_function(post_func, false, None));

                        let spec = deps.require_dep_spanned::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::PureWithoutResult), span)?;
                        let pres = vcx.mk_conj(&spec.pres);
                        let pre_func_call = pre_func.call()(
                            vcx.alloc_slice(&func_args.iter().map(|arg| vcx.mk_local_ex(arg)).collect::<Vec<_>>()),
                            item_generics.ty_exprs(),
                            item_generics.const_exprs(),
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_fn_pre_{item_name}_base",
                            ),
                            vir::expr! {
                                forall ..[func_args], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[pre_func_call]}
                                    (pres) ==> (pre_func_call)
                            },
                        ));
                        let posts = vcx.mk_conj(&spec.posts);
                        let post_func_call = post_func.call()(
                            vcx.mk_local_ex(func_ret),
                            vcx.alloc_slice(&func_args.iter().map(|arg| vcx.mk_local_ex(arg)).collect::<Vec<_>>()),
                            item_generics.ty_exprs(),
                            item_generics.const_exprs(),
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_fn_post_{item_name}_base",
                            ),
                            vir::expr! {
                                forall [func_ret], ..[func_args], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[post_func_call]}
                                    (post_func_call) ==> (posts)
                            },
                        ));

                        let mut stub_pres = Vec::new();
                        let mut stub_posts = Vec::new();
                        let mut args = Vec::with_capacity(arg_count + item_params.count());
                        for arg_idx in (0..arg_count).map(mir::Local::from) {
                            let name_p = local_defs[arg_idx].local.name;
                            args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                            if arg_idx != mir::RETURN_PLACE {
                                stub_pres.push(local_defs[arg_idx].impure_pred);
                            }
                        }
                        stub_posts.push(local_defs[mir::RETURN_PLACE].impure_pred);
                        // TODO: wands

                        stub_pres.push(pre_func.call()(
                            vcx.alloc_slice(&local_defs.args().map(|arg| arg.impure_snap).collect::<Vec<_>>()),
                            item_generics.ty_exprs(),
                            item_generics.const_exprs(),
                        ));
                        // TODO: mutable arguments should also have a post-state
                        stub_posts.push(post_func.call()(
                            local_defs.ret().impure_snap,
                            vcx.alloc_slice(&local_defs.args().map(|arg| vcx.mk_old_expr(arg.impure_snap)).collect::<Vec<_>>()),
                            item_generics.ty_exprs(),
                            item_generics.const_exprs(),
                        ));

                        methods.push(vcx.mk_method(
                            call_stub,
                            (args.as_slice(), item_generics.ty_decls(), item_generics.const_decls()),
                            &[],
                            vcx.alloc_slice(&stub_pres),
                            vcx.alloc_slice(&stub_posts),
                            None,
                        ));

                        // TODO: no method stub should be emitted for pure functions
                    },
                    AssocKind::Const { .. } => (), // noop?
                }
            }

            let impl_fun = FunctionIdn::new(
                vir_format_identifier!(vcx, "impl_{trait_name}"),
                (trait_generics.ty_args(), trait_generics.const_args()),
                vir::TYPE_BOOL,
            );
            funcs.push(vcx.mk_domain_function(impl_fun, false, None));

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{trait_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&funcs),
                None,
            );

            Ok((
                (
                    trait_domain,
                    methods,
                ),
                TraitData {
                    trait_name,
                    assoc_types,
                    assoc_funcs,
                    impl_fun,
                },
            ))
        })
    }
}
