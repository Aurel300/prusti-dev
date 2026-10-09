use pcg::borrow_pcg::FunctionData;
use prusti_interface::{PrustiError, specs::is_spec_fn};
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty},
    span::{Span, def_id::DefId},
};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::{CastType, FunctionIdn, MethodIdn, ViperIdent, vir_format_identifier};

use crate::{
    encoders::{
        MirLocalDefEnc, MirLocalDefEncOutput, MirLocalDefEncTask, MirSpecEnc, MutRefCurrentSnap,
        WandEnc, WandEncTask, mut_ref_args,
        pure::spec::{EncodedPledge, MirSpecEncMode, PledgeArgs},
        ty::{
            RustTyDecomposition,
            generics::{GArgs, GParams, GenericParamsEnc, r#trait::TraitEnc, trait_impls},
            lifted::TyConstructorEnc,
            use_inhabited::TyUseInhabitedEnc,
        },
    },
    trait_support::is_function_with_body,
};

pub struct TraitFnEnc;

#[derive(Debug, Clone, Copy)]
pub struct TraitFnEncOutputRef<'vir> {
    pub pre_func: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    /// Takes the result, then the arguments in the pre-state, then the
    /// arguments in the post-state (which differ for mutable references, see
    /// `PledgeArgs::two_state`).
    pub post_func:
        FunctionIdn<'vir, (vir::Snap, vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    /// The pledges: like `post_func`, but with the result just before the
    /// expiry of the borrows in it, and the arguments after it.
    pub pledge_func:
        FunctionIdn<'vir, (vir::Snap, vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub call_stub_impure: Option<MethodIdn<'vir, (vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>>,
    pub call_stub_pure_caller:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
    pub call_stub_pure_function:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
}

impl<'vir> OutputRefAny for TraitFnEncOutputRef<'vir> {}

impl TaskEncoder for TraitFnEnc {
    task_encoder::encoder_cache!(TraitFnEnc);
    const ENCODER_NAME: &'static str = "trait fn encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitFnEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = (
        vir::Domain<'vir>,
        Vec<vir::Function<'vir>>,
        Vec<vir::Method<'vir>>,
    );

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for (dom, funcs, methods) in Self::all_outputs_local_no_errors(program) {
            program.add_domain(dom);
            for func in funcs {
                program.add_function(func);
            }
            for method in methods {
                program.add_method(method);
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let assoc_item = tcx
                .opt_associated_item(*task_key)
                .expect("task key should be the associated item of a trait");
            let def_id = assoc_item.def_id;
            let span = vcx.tcx().def_span(def_id);
            assert!(matches!(assoc_item.kind, ty::AssocKind::Fn { .. }));
            assert_eq!(def_id, *task_key);

            // Prusti specifications on trait methods emit additional spec-
            // only fn items (with default implementations). These should never
            // be passed here, even though they are part of the trait as far as
            // Rust typing is concerned.
            assert!(!is_spec_fn(tcx, def_id));

            let trait_def_id = assoc_item
                .trait_container(tcx)
                .expect("task key should be the associated item of a trait");

            let trait_name = ViperIdent::from_def_id(vcx, trait_def_id);

            let mut axioms = Vec::new();
            let mut funcs = Vec::new();
            let mut dom_funcs = Vec::new();
            let mut methods = Vec::new();

            // item_generics also includes parameters of trait itself
            let item_params = GParams::from(def_id);
            let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
            let item_name = ViperIdent::from_def_id(vcx, def_id);

            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: false,
            })?;
            let arg_count = local_defs.arg_count + 1;
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);

            let is_pure = crate::encoders::is_function_pure(
                def_id,
                GArgs::new(item_params, item_params.rust_params()),
            );

            let pre_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_pre_{item_name}"),
                (
                    arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );
            // The arguments in the pre-state, then in the post-state.
            let two_state_arg_types = vcx.alloc_slice(&[arg_types, arg_types].concat());
            let post_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_post_{item_name}"),
                (
                    return_type,
                    two_state_arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );
            let pledge_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_pledge_{item_name}"),
                (
                    return_type,
                    two_state_arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );

            let call_stub_impure = (!is_pure).then(|| {
                MethodIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                    (
                        ref_args,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                )
            });
            let call_stub_pure_caller = is_pure.then(|| {
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_cfn_stub_{item_name}"),
                    (
                        arg_types,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                    return_type,
                )
            });
            let call_stub_pure_function = is_pure.then(|| {
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                    (
                        arg_types,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                    return_type,
                )
            });
            deps.emit_output_ref(
                *task_key,
                TraitFnEncOutputRef {
                    pre_func,
                    post_func,
                    pledge_func,
                    call_stub_impure,
                    call_stub_pure_caller,
                    call_stub_pure_function,
                },
            )?;
            // The stubs' semantics are given by the impls' axioms; require the
            // trait so that its impls' condition/axiom triggers are registered
            // (foreign traits are not encoded by `encode_all_in_crate`).
            deps.require_ref::<TraitEnc>(trait_def_id)?;
            dom_funcs.push(vcx.mk_domain_function(pre_func, false, None));
            dom_funcs.push(vcx.mk_domain_function(post_func, false, None));
            dom_funcs.push(vcx.mk_domain_function(pledge_func, false, None));

            // The stub emitted below is only useful together with the axioms
            // bridging the abstract pre/post functions to concrete impl
            // specs. Unlock, per impl of the trait, the axioms of just the
            // item implementing this function once the impl's constructor
            // keys are requested - the same gating as the impl's condition
            // (see `TraitEnc`), but calling a trait function must not pull in
            // the trait's whole machinery. An impl that inherits a pure
            // default body instead unlocks the axiom stating that body at its
            // trait refs. Only final definitions are assumed (see
            // `final_leaf_def`).
            let has_body = is_function_with_body(vcx.tcx(), def_id);
            for impl_did in trait_impls::implementing_impls(tcx, trait_def_id) {
                let Some(leaf) = trait_impls::final_leaf_def(tcx, impl_did, def_id) else {
                    continue;
                };
                let keys = trait_impls::impl_unlock_keys(impl_did);
                let impl_span = tcx.def_span(impl_did);
                if !leaf.defining_node.is_from_trait() {
                    let item_did = leaf.item.def_id;
                    TyConstructorEnc::on_all_requested(keys, move || {
                        let _ = trait_impls::TraitImplItemEnc::encode(
                            (impl_did, item_did),
                            false,
                            impl_span,
                        );
                    });
                } else if has_body && is_pure {
                    TyConstructorEnc::on_all_requested(keys, move || {
                        let _ = trait_impls::TraitImplDefaultFnEnc::encode(
                            (impl_did, def_id),
                            false,
                            impl_span,
                        );
                    });
                }
            }

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let func_arg_exprs = vcx.alloc_slice(
                &func_args
                    .iter()
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
            );
            let func_ret = local_defs.local_decl_ret();

            let spec = deps.require_dep_spanned::<MirSpecEnc>(
                (def_id, def_id, MirSpecEncMode::PureWithoutResult),
                span,
            )?;
            let pres = vcx.mk_conj(&spec.pre_exprs().collect::<Vec<_>>());
            let pre_func_call = pre_func.call()(
                func_arg_exprs,
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
            // A default body is not part of the trait's contract: impls may
            // override it with a different result.
            let posts = vcx.mk_conj(&spec.post_exprs().collect::<Vec<_>>());
            let func_args_post = local_defs.local_decl_args_post().collect::<Vec<_>>();
            let two_state_arg_exprs = vcx.alloc_slice(
                &func_args
                    .iter()
                    .chain(&func_args_post)
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
            );
            let post_func_call = post_func.call()(
                vcx.mk_local_ex(func_ret),
                two_state_arg_exprs,
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );
            // Impls may weaken the preconditions, so a call can be valid
            // outside them; the trait's postconditions are only promised
            // where they held. `post_func` receives the arguments' pre-state.
            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{trait_name}_fn_post_{item_name}_base",
                ),
                vir::expr! {
                    forall [func_ret], ..[func_args], ..[func_args_post], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[post_func_call]}
                        (post_func_call) ==> ((pres) ==> (posts))
                },
            ));
            // The same for the pledges (the expiry obligations of
            // `assert_on_expiry` are not supported through traits).
            let pledge_args = PledgeArgs::two_state(
                vcx.mk_local_ex(func_ret),
                &func_args
                    .iter()
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
                &func_args_post
                    .iter()
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
                &mut_ref_args(tcx, def_id),
            );
            let pledges = pledges_for_axiom(
                vcx,
                deps,
                def_id,
                def_id,
                &spec.pledges,
                &local_defs,
                pledge_args,
                true,
            )?;
            let pledges = vcx.mk_conj(
                &pledges
                    .iter()
                    .map(|(pledge, _)| *pledge)
                    .collect::<Vec<_>>(),
            );
            let pledge_func_call = pledge_func.call()(
                vcx.mk_local_ex(func_ret),
                two_state_arg_exprs,
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );
            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{trait_name}_fn_pledge_{item_name}_base",
                ),
                vir::expr! {
                    forall [func_ret], ..[func_args], ..[func_args_post], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[pledge_func_call]}
                        (pledge_func_call) ==> ((pres) ==> (pledges))
                },
            ));

            if is_pure {
                let mut stub_pres = Vec::new();
                let mut stub_posts = Vec::new();
                stub_pres.push(pre_func.call()(
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| vcx.mk_local_ex(arg.local_snap))
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                // A pure function has no mutable reference arguments, so their
                // post-state is their pre-state.
                let arg_snaps = local_defs
                    .args()
                    .map(|arg| vcx.mk_local_ex(arg.local_snap))
                    .collect::<Vec<_>>();
                stub_posts.push(post_func.call()(
                    vcx.mk_result(local_defs.snap_ty_return()),
                    vcx.alloc_slice(&[arg_snaps.as_slice(), arg_snaps.as_slice()].concat()),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));

                // If the call succeeds, then its return type is definitely inhabited
                // We need this postcondition to generate impure wrapper fns
                // See tests/verify/pass/extern-spec/module-arg.rs
                let ret_ty = tcx
                    .instantiate_and_normalize_erasing_regions(
                        ty::GenericArgs::identity_for_item(tcx, def_id),
                        ty::TypingEnv::post_analysis(tcx, def_id),
                        tcx.fn_sig(def_id),
                    )
                    .skip_binder()
                    .output();
                let ret_ty = RustTyDecomposition::from_ty(ret_ty, def_id);
                stub_posts.push(deps.require_ref::<TyUseInhabitedEnc>(ret_ty)?.inhabited());
                // stub_posts.push(local_defs.ret().inhabited);

                let wrapped_call = call_stub_pure_function.unwrap().call()(
                    func_arg_exprs,
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                );
                funcs.push(vcx.mk_function(
                    call_stub_pure_caller.unwrap(),
                    (
                        &func_args,
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    vcx.alloc_slice(&stub_pres),
                    vcx.alloc_slice(&stub_posts),
                    Some(&vir::DecreasesGenData::Star),
                    Some(wrapped_call),
                ));
                funcs.push(vcx.mk_function(
                    call_stub_pure_function.unwrap(),
                    (
                        &func_args,
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&stub_posts),
                    None,
                    None,
                ));
            } else {
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
                // Like a regular method, the stub takes (and returns) what the
                // arguments and the result point to, and the wands that give
                // back what the result borrows. The deep snapshots passed to
                // the pre- and postcondition functions below read it.
                let wands = deps.require_dep::<WandEnc>(WandEncTask {
                    data: FunctionData::new(def_id),
                })?;
                stub_pres.extend(wands.indirect_pres(vcx, &local_defs, deps));
                stub_posts.extend(wands.indirect_posts(vcx, &local_defs, deps));
                stub_posts.extend(wands.wand_posts(vcx, &local_defs, deps));

                stub_pres.push(pre_func.call()(
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| arg.impure_snap)
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                // The arguments in the post-state: the referent of a mutable
                // reference that is given back has its value then. One that is
                // blocked by the result has no value in the post-state, so it
                // gets the (unconstrained) shallow snapshot.
                let mut_args = mut_ref_args(tcx, def_id);
                let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                let pre_args = local_defs
                    .args()
                    .map(|arg| vcx.mk_old_expr(arg.impure_snap))
                    .collect::<Vec<_>>();
                let mut post_args = Vec::with_capacity(pre_args.len());
                for (idx, (arg, pre)) in local_defs.args().zip(&pre_args).enumerate() {
                    let local = mir::Local::from_usize(idx + 1);
                    post_args.push(if !mut_args.get(idx).copied().unwrap_or(false) {
                        *pre
                    } else if wands.is_blocked_arg(local) {
                        vcx.mk_old_expr(arg.impure_shallow_snap)
                    } else {
                        let ty = RustTyDecomposition::from_ty(sig.inputs()[idx], def_id);
                        MutRefCurrentSnap::new(deps, ty)?.snap(*pre)
                    });
                }
                stub_posts.push(post_func.call()(
                    local_defs.ret().impure_snap,
                    vcx.alloc_slice(&[pre_args.as_slice(), post_args.as_slice()].concat()),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));

                methods.push(vcx.mk_method(
                    call_stub_impure.unwrap(),
                    (
                        args.as_slice(),
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&stub_pres),
                    vcx.alloc_slice(&stub_posts),
                    None,
                ));
            }

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_fns_{trait_name}_{item_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&dom_funcs),
                None,
            );

            Ok(((trait_domain, funcs, methods), ()))
        })
    }
}

/// The `pledges` of `def_id` (the trait function `trait_fn` or an impl of it),
/// reified with `pledge_args` for the axioms of `fn_pledge`.
///
/// A call through the trait gives `fn_pledge` the final values only of the
/// mutable reference arguments that the result's borrow gives back (see
/// `trait_fn_pledge`); for the others, the referent is not held when the
/// borrow expires. A pledge reading the final value of such an argument is
/// ill-formed (as it is for a call that is not through a trait, where it
/// reads a referent the wand does not hold), so it is left out (and reported
/// if `report`). Each pledge is returned with its span.
#[allow(clippy::too_many_arguments)]
pub(crate) fn pledges_for_axiom<'vir, E: TaskEncoder>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, E>,
    trait_fn: DefId,
    def_id: DefId,
    pledges: &[EncodedPledge<'vir>],
    local_defs: &MirLocalDefEncOutput<'vir>,
    pledge_args: PledgeArgs<'vir>,
    report: bool,
) -> Result<Vec<(vir::ExprBool<'vir>, Span)>, EncodeFullError<'vir, E>> {
    let mut_args = mut_ref_args(vcx.tcx(), def_id);
    let given_back = if pledges.is_empty() || !mut_args.contains(&true) {
        None
    } else {
        deps.require_dep::<WandEnc>(WandEncTask {
            data: FunctionData::new(trait_fn),
        })?
        .single_wand_given_back_args()
    };
    // The post-state variables of the arguments whose final value a pledge
    // must not read.
    let not_given_back = local_defs
        .args()
        .enumerate()
        .filter(|(idx, _)| {
            let local = mir::Local::from_usize(idx + 1);
            mut_args.get(*idx).copied().unwrap_or(false)
                && given_back
                    .as_ref()
                    .is_some_and(|given_back| !given_back.contains(&local))
        })
        .map(|(_, arg)| arg.local_snap_post.name)
        .collect::<FxHashSet<_>>();
    let mut exprs = Vec::with_capacity(pledges.len());
    for pledge in pledges {
        let expr = pledge.expiry_postcondition.expr(pledge_args);
        let mut locals = FxHashSet::default();
        vir::collect_locals(expr.as_dyn(), &mut locals);
        let span = pledge.expiry_postcondition.span();
        if locals.iter().any(|local| not_given_back.contains(local)) {
            if report {
                vcx.emit_early_error(PrustiError::incorrect(
                    "a pledge cannot refer to the final value of a mutable reference argument \
                     that the result does not borrow from"
                        .to_string(),
                    span.into(),
                ));
            }
            continue;
        }
        exprs.push((expr, span));
    }
    Ok(exprs)
}
