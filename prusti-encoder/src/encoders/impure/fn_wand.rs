use crate::encoders::{
    EncodeResult, ImpureEncVisitor, MirLocalDefEnc, MirLocalDefEncOutput, MirLocalDefEncTask,
    MirSpecEnc, Pure, TyUseImpureEnc, TyUsePureEnc,
    mir_fn::RustSignature,
    mir_pure::ExprInput,
    pure::spec::{EncodedPledge, MirSpecEncMode, PledgeArgs, PledgeExpr, callee_ctx_key},
    ty::{
        RustTyDecomposition,
        generics::{
            GArgCaster, GArgs, GArgsCastEnc, GArgsTyEnc, GParams, GenericParamsEnc,
            trait_fn::TraitFnEnc,
        },
        indirect::{IndirectPredicatesEnc, projection_for_generalized_idx},
        use_impure::TyUseImpure,
        use_pure::TyUsePure,
    },
};
use pcg::borrow_pcg::{
    FunctionData, FunctionShape, FunctionShapeInput, FunctionShapeNode, FunctionShapeOutput,
    MakeFunctionShapeError, region_projection::Generalized, state::BorrowsState,
    unblock_graph::UnblockGraph,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

/// Encodes the magic wands given a function signature.
pub struct WandEnc;

#[derive(Clone, Debug)]
pub enum WandEncError {
    Unsupported(String),
}

impl<'vir, E: TaskEncoder> ImpureEncVisitor<'vir, '_, E> {
    pub fn package_wands(
        &mut self,
        final_borrow_state: &BorrowsState<'_, 'vir>,
    ) -> EncodeResult<'vir, Vec<vir::Stmt<'vir>>, E> {
        let mut wand_packages = Vec::new();
        let label = self.new_label("package_post");
        let result = self.local_defs[mir::RETURN_PLACE].impure_snap;
        let result = self.vcx.mk_local_labelled_old_expr(result, label);
        let args = self
            .local_defs
            .args()
            .map(|a| self.vcx.mk_old_expr(a.impure_snap));
        let args = PledgeExpr::pledge_args(result, args);
        let args = self.wands.with_callee_ctx_args(args, None, self.deps);

        for wand_data in self.wands.viper_wands() {
            let Some(wand) = self
                .wands
                .mk_wand(&wand_data, args, None, None, self.vcx, self.deps)
            else {
                continue;
            };
            let mut package_script = Vec::new();
            for rhs in wand_data.rhs.iter() {
                let ug = UnblockGraph::for_node(
                    mir::Place::from(rhs.mir_local()),
                    final_borrow_state,
                    self.pcg_ctxt(),
                );
                let actions = ug.actions(self.pcg_ctxt()).unwrap();
                let unblock = self.block(|visitor| {
                    visitor.pcs_unblock_actions(final_borrow_state, &actions, Some(label))
                })?;
                package_script.extend(unblock);
            }

            if !wand_data.pledges.is_empty() {
                // Statements in the package script only see resources already
                // in the package state. A resource that is not obtained from
                // the LHS (e.g. an argument the result does not borrow from)
                // is only moved there when consumed, which for the RHS happens
                // after the script. Asserting the RHS resources moves them in
                // early, so that the pledge exhales below can read them.
                let resources = wand_data
                    .rhs
                    .iter()
                    .filter_map(|g| {
                        self.wands.encode_predicates_for_function_shape_node(
                            self.vcx,
                            self.deps,
                            *g,
                            None,
                            |i| args[i],
                        )
                    })
                    .collect::<Vec<_>>();
                package_script.push(self.vcx.mk_assert_stmt(self.vcx.mk_conj(&resources)));
            }

            for EncodedPledge {
                expiry_postcondition,
                ..
            } in &wand_data.pledges
            {
                let span = expiry_postcondition.span();
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "pledge postcondition might not hold",
                            span.into(),
                        )])
                    });
                    package_script.push(vcx.mk_exhale_stmt(expiry_postcondition.expr(args)));
                });
            }
            wand_packages.push(
                self.vcx
                    .mk_package_stmt(wand, self.vcx.alloc_slice(&package_script)),
            );
        }
        Ok(wand_packages)
    }
}

type EncodedPledges<'vir> = Vec<EncodedPledge<'vir>>;

/// Builds the deep snapshot that a mutable reference has once its referent
/// holds the value currently in the heap, from the reference's snapshot in an
/// earlier state (which gives its address and metadata). Reads the referent's
/// predicate, which must be held.
#[derive(Clone, Copy)]
pub(crate) struct MutRefCurrentSnap<'vir> {
    ref_ty: TyUsePure<'vir>,
    referent_caster: GArgCaster<'vir, Pure>,
    referent_ty: TyUseImpure<'vir>,
}

impl<'vir> MutRefCurrentSnap<'vir> {
    /// `ref_ty` must be a mutable reference type.
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        ref_ty: RustTyDecomposition<'vir>,
    ) -> Result<Self, EncodeFullError<'vir, E>> {
        let inner = ref_ty.ty.expect_mutref();
        let normalized = inner
            .referent
            .decompose_compare_normalize(ref_ty.ty.params, ref_ty.args);
        let referent = inner
            .referent
            .decompose_context(ref_ty.ty.params, ref_ty.args);
        Ok(Self {
            ref_ty: deps.require_dep::<TyUsePureEnc>(ref_ty)?,
            referent_caster: deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?,
            referent_ty: deps.require_dep::<TyUseImpureEnc>(referent)?,
        })
    }

    pub(crate) fn snap<Curr, Next>(
        &self,
        earlier: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.snap_reading(earlier, |value| value)
    }

    /// Like `snap`, but with the referent's value in the state of the
    /// left-hand side of the enclosing wand, i.e. when the borrow expires.
    pub(crate) fn snap_at_expiry<Curr, Next>(
        &self,
        earlier: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.snap_reading(earlier, |value| {
            vir::with_vcx(|vcx| vcx.mk_old_lhs_expr(value))
        })
    }

    fn snap_reading<Curr, Next>(
        &self,
        earlier: vir::ExprGenSnap<'vir, Curr, Next>,
        in_state: impl FnOnce(vir::ExprGenSnap<'vir, Curr, Next>) -> vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let ref_ty = self.ref_ty.expect_mutref();
        let earlier = earlier.downcast_ty();
        let addr = ref_ty.deref_access(earlier);
        let metadata = ref_ty.metadata_access(earlier);
        let value = self
            .referent_caster
            .cast_to_caller_ctx(in_state(self.referent_ty.ref_to_deep_snap(addr)));
        ref_ty.prim_to_snap(addr, metadata, value).upcast_ty()
    }
}

/// Not tied to a caller or callee context. `indirect_pres`, `indirect_posts`,
/// `wand_posts`, and `package_wands` are identity-substituted and intended for
/// use in the callee's own contract; `apply_wands` is for caller use and
/// re-substitutes via a [`WandCallContext`].
#[derive(Clone)]
pub struct WandEncOutput<'vir> {
    /// Information about the corresponding function.
    function_data: FunctionData<'vir>,

    /// The lifetime projections of all arguments to the function.
    inputs: Vec<FunctionShapeInput<Generalized>>,

    /// The lifetime projections of all function outputs (according to the
    /// corresponding [`FunctionShape`]). This *includes* lifetime projections
    /// of nested lifetimes in the function arguments.
    outputs: Vec<FunctionShapeOutput<Generalized>>,

    /// Encoded VIR expressions for the magic wands.
    wands: Vec<WandData<'vir>>,
}

/// Substitution context for instantiating a wand at a call site. When `None`,
/// the wand is encoded using the callee's identity substitution (appropriate
/// when emitting wands inside the function being defined). When `Some`, the
/// wand is re-encoded with the call-site substitutions and the caller's
/// generic parameters, so that placeholders like `Self` or other callee
/// generics are replaced by concrete types from the caller's perspective.
pub type WandCallContext<'vir> = Option<GArgs<'vir>>;

impl<'vir> WandEncOutput<'vir> {
    pub(crate) fn fn_sig(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        call_ctx: WandCallContext<'vir>,
    ) -> ty::FnSig<'vir> {
        match call_ctx {
            // TODO: change pcg's `fn_sig` to take `&[GenericArg]` instead of `GenericArgsRef`
            Some(ctx) => self
                .function_data
                .fn_sig(vcx.tcx(), vcx.tcx().mk_args(ctx.args())),
            None => self.function_data.identity_fn_sig(vcx.tcx()),
        }
    }

    pub(crate) fn g_params(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        call_ctx: WandCallContext<'vir>,
    ) -> GParams<'vir> {
        match call_ctx {
            Some(ctx) => ctx.context(),
            None => GParams::new(
                self.function_data.identity_substs(vcx.tcx()),
                self.function_data.param_env(vcx.tcx()),
                false,
            ),
        }
    }

    /// The (unreified) predicates associated with the given node, or `None` if
    /// there are no resources associated with it.
    #[allow(clippy::type_complexity)]
    fn predicates_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: FunctionShapeNode<Generalized>,
        call_ctx: WandCallContext<'vir>,
    ) -> Option<Vec<vir::ExprGenBool<'vir, vir::ExprSnap<'vir>, vir::ExprKind<'vir>>>> {
        let arg_ty = g.ty(self.fn_sig(vcx, call_ctx));
        let decomp = RustTyDecomposition::from_ty(arg_ty, self.g_params(vcx, call_ctx));
        let region_proj =
            projection_for_generalized_idx(arg_ty, g.region_idx(), decomp, vcx.tcx())?;
        let predicates = deps
            .require_dep::<IndirectPredicatesEnc>(region_proj)
            .unwrap()
            .predicate_applications;
        (!predicates.is_empty()).then_some(predicates)
    }

    fn encode_predicates_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode<Generalized>>,
        call_ctx: WandCallContext<'vir>,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
    ) -> Option<vir::ExprBool<'vir>> {
        use vir::Reify;
        let g = g.into();
        let predicates = self.predicates_for_function_shape_node(vcx, deps, g, call_ctx)?;

        let local = g.mir_local();
        let local_snap = snap(local);
        Some(
            vcx.mk_conj(
                &predicates
                    .iter()
                    .map(|p| p.reify(vcx, local_snap))
                    .collect::<Vec<_>>(),
            ),
        )
    }

    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.inputs().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, None, |i| {
                local_defs[i].impure_shallow_snap
            })
        })
    }

    pub fn indirect_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        // The encoded predicates for the input lifetime projections that are
        // not blocked by any of the result lifetime projections. These will be
        // encoded as part of the postcondition of the function (in contrast,
        // the predicates for the blocked inputs will appear on the right-hand
        // side of a magic wand in the postcondition).
        let unblocked_input_posts = self
            .inputs()
            .filter(|i| !self.blocked_inputs().contains(i))
            .filter_map(|lp| {
                self.encode_predicates_for_function_shape_node(vcx, deps, lp, None, |i| {
                    vcx.mk_old_expr(local_defs[i].impure_shallow_snap)
                })
            })
            .collect::<Vec<_>>()
            .into_iter();

        let output_posts = self.indirect_output_posts(vcx, local_defs, deps);
        unblocked_input_posts.chain(output_posts)
    }

    /// The part of `indirect_posts` for what the result points to.
    pub fn indirect_output_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.outputs().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, None, |i| {
                local_defs[i].impure_shallow_snap
            })
        })
    }

    pub fn wand_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        let wand_result =
            vcx.mk_local_decl("wand_result", local_defs[mir::RETURN_PLACE].local_snap.ty());
        let wand_result_expr = vcx.mk_local_ex(wand_result);
        let args = local_defs
            .args()
            .map(|arg| vcx.mk_old_expr(arg.impure_snap));
        let args = PledgeExpr::pledge_args(wand_result_expr, args);

        // TODO: wands for late-bound regions
        self.viper_wands().into_iter().filter_map(move |wand_data| {
            let wand = self.mk_wand(&wand_data, args, None, None, vcx, deps)?;
            Some(vcx.mk_let_expr(
                wand_result,
                local_defs[mir::RETURN_PLACE].impure_snap,
                vcx.mk_wand_expr(wand),
            ))
        })
    }

    pub fn apply_wands<E: TaskEncoder>(
        &self,
        arguments: &[vir::ExprSnap<'vir>],
        label_pre: &'vir str,
        label_post: &'vir str,
        call_ctx: GArgs<'vir>,
        visitor: &mut ImpureEncVisitor<'vir, '_, E>,
    ) {
        let result = visitor
            .vcx
            .mk_local_labelled_old_expr(arguments[mir::RETURN_PLACE.as_usize()], label_post);
        let args = (1..arguments.len()).map(|l| {
            visitor
                .vcx
                .mk_local_labelled_old_expr(arguments[l], label_pre)
        });
        let args = PledgeExpr::pledge_args(result, args);
        for wand_data in self.viper_wands() {
            let Some(wand) = self.mk_wand(
                &wand_data,
                args,
                Some(label_pre),
                Some(call_ctx),
                visitor.vcx,
                visitor.deps,
            ) else {
                continue;
            };
            visitor.stmt(visitor.vcx.mk_apply_stmt(wand));
        }
    }

    fn mk_wand<E: TaskEncoder>(
        &self,
        wand_data: &WandData<'vir>,
        pledge_args: PledgeArgs<'vir>,
        pledge_old_label: Option<&'vir str>,
        call_ctx: WandCallContext<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Option<vir::Wand<'vir>> {
        debug_assert!(!wand_data.lhs.is_empty());
        let generics = self.generics_subst(call_ctx, vcx, deps);
        let pledge_args = self.with_callee_ctx_args(pledge_args, call_ctx, deps);
        let pledge_expr = |pledge: &PledgeExpr<'vir>| match pledge_old_label {
            Some(label) => {
                vcx.with_local_subst(generics, || pledge.expr_at_label(pledge_args, label))
            }
            None => pledge.expr(pledge_args),
        };
        let rhs = wand_data.rhs.iter().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, *g, call_ctx, |i| {
                pledge_args[i]
            })
        });
        let rhs = rhs
            .chain(
                wand_data
                    .pledges
                    .iter()
                    .map(|pledge| pledge_expr(&pledge.expiry_postcondition)),
            )
            .collect::<Vec<_>>();
        if rhs.is_empty() {
            // We skip emitting the wand when there is nothing on the RHS, i.e.,
            // nothing would be unblocked by applying this wand, nor are there
            // any pledge postconditions.
            return None;
        }
        let rhs = vcx.mk_conj(&rhs);
        let lhs = wand_data.lhs.iter().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, *g, call_ctx, |i| {
                pledge_args[i]
            })
        });
        let lhs = lhs
            .chain(
                wand_data
                    .pledges
                    .iter()
                    .filter_map(|pledge| pledge.expiry_obligation.as_ref().map(pledge_expr)),
            )
            .collect::<Vec<_>>();
        let lhs = vcx.mk_conj(&lhs);
        Some(vcx.mk_wand(lhs, rhs))
    }

    /// Adds the arguments and the result cast to the callee's generic context
    /// (see `PledgeArgs::with_callee_ctx`). At a call site, they are given in
    /// the caller's context, from which they are cast with the call's generic
    /// arguments; in the callee itself, they are already in its context.
    fn with_callee_ctx_args<E: TaskEncoder>(
        &self,
        pledge_args: PledgeArgs<'vir>,
        call_ctx: WandCallContext<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> PledgeArgs<'vir> {
        let Some(call_args) = call_ctx else {
            return pledge_args.with_callee_ctx(|_, expr| expr);
        };
        let signature = RustSignature::new(self.function_data.def_id());
        let arg_count = pledge_args.arg_count();
        pledge_args.with_callee_ctx(|local, expr| {
            let ty = if local.index() > arg_count {
                signature.output
            } else {
                signature.inputs[local.index() - 1]
            };
            let normalized = ty.decompose_compare_normalize(signature.gparams, call_args);
            deps.require_dep::<GArgsCastEnc<Pure>>(normalized)
                .unwrap()
                .cast_to_callee_ctx(expr)
        })
    }

    /// The pledges are encoded once, at the callee's identity substitution,
    /// so they refer to the callee's generic parameters. At a call site, these
    /// are replaced by the call's generic arguments, as Viper does for the
    /// callee's postcondition (from which the caller holds the wand).
    fn generics_subst<E: TaskEncoder>(
        &self,
        call_ctx: WandCallContext<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> &'vir FxHashMap<&'vir str, vir::ExprDyn<'vir>> {
        let Some(call_args) = call_ctx else {
            return vcx.alloc(FxHashMap::default());
        };
        let params = deps
            .require_dep::<GenericParamsEnc>(self.g_params(vcx, None))
            .unwrap();
        let args = deps.require_dep::<GArgsTyEnc>(call_args).unwrap();
        let tys = params
            .ty_decls()
            .iter()
            .zip(args.get_ty::<(), !>())
            .map(|(decl, arg)| (decl.name, arg.as_dyn()));
        let consts = params
            .const_decls()
            .iter()
            .zip(args.get_const::<(), !>())
            .map(|(decl, arg)| (decl.name, arg.as_dyn()));
        vcx.alloc(tys.chain(consts).collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WandEncTask<'tcx> {
    pub data: FunctionData<'tcx>,
}

impl<'tcx> WandEncTask<'tcx> {
    pub fn def_id(&self) -> DefId {
        self.data.def_id()
    }

    pub fn function_shape(
        &self,
        vcx: &vir::VirCtxt<'tcx>,
    ) -> Result<FunctionShape<Generalized>, MakeFunctionShapeError> {
        self.data.shape(vcx.tcx())
    }
}

pub type WandRhsKey = FunctionShapeInput<Generalized>;
pub type WandLhsKey = FunctionShapeNode<Generalized>;

#[derive(Clone, Debug)]
pub struct WandData<'vir> {
    /// Lifetime projections on the right-hand side of the wand. Guaranteed to be
    /// non-empty.
    rhs: Vec<WandRhsKey>,
    /// Lifetime projections on the left-hand side of the wand. Guaranteed to be
    /// non-empty.
    lhs: Vec<WandLhsKey>,
    pledges: EncodedPledges<'vir>,
}

impl<'vir> WandData<'vir> {
    pub fn new(lhs: Vec<WandLhsKey>, rhs: Vec<WandRhsKey>, pledges: EncodedPledges<'vir>) -> Self {
        debug_assert!(!lhs.is_empty());
        debug_assert!(!rhs.is_empty());
        Self { rhs, lhs, pledges }
    }
}

impl TaskEncoder for WandEnc {
    task_encoder::encoder_cache!(WandEnc);

    type TaskDescription<'vir> = WandEncTask<'vir>;

    type TaskKey<'vir> = WandEncTask<'vir>;

    type OutputFullDependency<'vir> = WandEncOutput<'vir>;

    type EncodingError = WandEncError;

    const ENCODER_NAME: &'static str = "wand encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn describe_error(error: Self::EncodingError) -> String {
        match error {
            WandEncError::Unsupported(message) => message,
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let def_id = task_key.def_id();

            let shape = task_key.function_shape(vcx).map_err(|e| {
                EncodeFullError::EncodingError(
                    WandEncError::Unsupported(format!("function shape: {e:?}")),
                    None,
                )
            })?;

            let coupled_edges = shape.coupled_edges();
            let edges: FxHashSet<_> = shape.edges().map(|e| (e.input(), e.output())).collect();

            let (inputs, outputs) = shape.take_inputs_and_outputs();
            let spec = deps.require_dep::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::Impure))?;
            if coupled_edges.is_empty() {
                assert!(spec.pledges.is_empty());
                return Ok((
                    (),
                    WandEncOutput {
                        function_data: task_key.data,
                        inputs,
                        outputs,
                        wands: vec![],
                    },
                ));
            }
            let pledges = spec.pledges;
            let wands: Vec<WandData<'vir>> = coupled_edges
                .into_iter()
                .filter_map(|hyper_edge| {
                    let (sources, mut targets) = hyper_edge.into_tuple();
                    // We don't want to emit an identity wand, like P --* P. This can happen when
                    // PCG returns self-edges, like for fn(x: &'a mut &'b i32) where 'b is in
                    // invariant position and we therefore have an edge x|'b -> x|'b.
                    // Currently, these edges also prevent us from emitting indirect postconditions.
                    // TODO: we might want to emit these identity wands in the future to attach functional
                    // specifications to them. We still need to emit the resources on the wand's LHS.
                    let mut sources_as_nodes = sources
                        .iter()
                        .map(|&s| s.to_function_shape_node())
                        .collect::<Vec<_>>();
                    sources_as_nodes.sort();
                    targets.sort();
                    if sources_as_nodes == targets {
                        return None;
                    }
                    Some(WandData::new(targets, sources, pledges.clone()))
                })
                .collect();
            let mut output: WandEncOutput<'vir> = WandEncOutput {
                function_data: task_key.data,
                inputs,
                outputs,
                wands: Vec::new(),
            };
            output.wands = output
                .select_wands(wands, !pledges.is_empty(), &edges, vcx, deps)
                .map_err(|err| EncodeFullError::EncodingError(err, None))?;
            // A call through a trait cannot know the pledges of the impl it
            // resolves to; like the postconditions, they are abstracted by a
            // function of the trait, which the impls' axioms define. It is
            // only attached if the expiry it refers to is unambiguous.
            if let [wand] = output.wands.as_mut_slice()
                && let Some(assoc_item) = vcx.tcx().opt_associated_item(def_id)
                && assoc_item.trait_container(vcx.tcx()).is_some()
            {
                let pledge = trait_fn_pledge(vcx, deps, def_id, &wand.rhs)?;
                wand.pledges.push(pledge);
            }
            Ok(((), output))
        })
    }
}

impl<'vir> WandEncOutput<'vir> {
    /// Selects the wands to emit among those of the coupled edges, rejecting
    /// the shapes that cannot be encoded precisely.
    fn select_wands<E: TaskEncoder>(
        &self,
        wands: Vec<WandData<'vir>>,
        has_pledges: bool,
        edges: &FxHashSet<(WandRhsKey, WandLhsKey)>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Result<Vec<WandData<'vir>>, WandEncError> {
        let mut has_resources = |g: FunctionShapeNode<Generalized>| {
            self.predicates_for_function_shape_node(vcx, deps, g, None)
                .is_some()
        };
        // A wand is only needed if it gives back a resource, or to carry the
        // pledges if none does (e.g. for shared references).
        let (mut wands, resourceless): (Vec<_>, Vec<_>) = wands
            .into_iter()
            .partition(|wand_data| wand_data.rhs.iter().any(|g| has_resources((*g).into())));
        // A wand gives back its sources only once all of its targets have
        // expired. That matches the signature only if each source with
        // resources flows into each target with resources.
        for wand_data in &wands {
            let sources = wand_data
                .rhs
                .iter()
                .filter(|g| has_resources((**g).into()))
                .collect::<Vec<_>>();
            let targets = wand_data
                .lhs
                .iter()
                .filter(|g| has_resources(**g))
                .collect::<Vec<_>>();
            let precise = sources.iter().all(|source| {
                let mut targets = targets.iter();
                targets.all(|target| edges.contains(&(**source, **target)))
            });
            if !precise {
                return Err(WandEncError::Unsupported(
                    "borrows in the result that expire separately but depend on a common \
                     argument are not supported"
                        .to_string(),
                ));
            }
        }
        if has_pledges {
            if wands.is_empty() {
                wands.extend(resourceless.into_iter().take(1));
            } else if wands.len() > 1 {
                // It is unclear which expiry the pledges refer to.
                return Err(WandEncError::Unsupported(
                    "pledges on a function whose result contains borrows that expire \
                     separately are not supported"
                        .to_string(),
                ));
            }
        }
        Ok(wands)
    }

    pub fn viper_wands(&self) -> Vec<WandData<'vir>> {
        self.wands.clone()
    }

    /// All lifetime projections in the arguments that are blocked by any of the
    /// lifetime projections in the function's result.
    pub fn blocked_inputs(&self) -> FxHashSet<FunctionShapeInput<Generalized>> {
        self.wands
            .iter()
            .flat_map(|wand| wand.rhs.iter().copied())
            .collect()
    }

    /// If the function has exactly one wand, the arguments (some of) whose
    /// referents it gives back. A call through a trait passes the pledges
    /// only the final values of these (see `trait_fn_pledge`).
    pub fn single_wand_given_back_args(&self) -> Option<FxHashSet<mir::Local>> {
        match self.wands.as_slice() {
            [wand] => Some(wand.rhs.iter().map(|input| input.mir_local()).collect()),
            _ => None,
        }
    }

    /// Whether (a lifetime projection of) argument `local` is blocked by the
    /// result, i.e. what it points to is only given back by a wand.
    pub fn is_blocked_arg(&self, local: mir::Local) -> bool {
        self.blocked_inputs()
            .iter()
            .any(|input| input.mir_local() == local)
    }

    pub fn inputs(&self) -> impl Iterator<Item = FunctionShapeInput<Generalized>> + '_ {
        self.inputs.iter().copied()
    }

    pub fn outputs(&self) -> impl Iterator<Item = FunctionShapeOutput<Generalized>> + '_ {
        self.outputs.iter().copied()
    }
}

/// The pledge of a trait function, `fn_pledge(result, args, args_after)`
/// (see `TraitFnEnc`), where `args_after` are the arguments after the expiry:
/// for a mutable reference given back by the wand (one of `rhs`), its
/// referent's value then; for any other argument, its value before the call.
///
/// Only the arguments are looked up when reifying, so that the callee's
/// generics in the rest of the expression are substituted at a call site.
fn trait_fn_pledge<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, WandEnc>,
    def_id: DefId,
    rhs: &[WandRhsKey],
) -> Result<EncodedPledge<'vir>, EncodeFullError<'vir, WandEnc>> {
    let pledge_func = deps.require_ref::<TraitFnEnc>(def_id)?.pledge_func;
    let params = GParams::from(def_id);
    let generics = deps.require_dep::<GArgsTyEnc>(GArgs::new(params, params.rust_params()))?;
    let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
        def_id,
        all_locals: false,
    })?;
    let sig = vcx
        .tcx()
        .fn_sig(def_id)
        .instantiate_identity()
        .skip_binder();
    let arg = |local: mir::Local, ty: vir::TypeSnap<'vir>| {
        vcx.mk_lazy_expr(
            "trait_fn_pledge_arg",
            ty,
            Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[&callee_ctx_key(local)].kind),
        )
    };
    let pre = local_defs
        .args()
        .enumerate()
        .map(|(idx, def)| arg(mir::Local::from_usize(idx + 1), def.local_snap.ty()))
        .collect::<Vec<_>>();
    // The result just before the expiry: if it is a mutable reference, its
    // referent is read in the state of the wand's left-hand side.
    let result = arg(
        mir::Local::from_usize(pre.len() + 1),
        local_defs.snap_ty_return(),
    );
    let result = if matches!(
        sig.output().kind(),
        ty::TyKind::Ref(.., ty::Mutability::Mut)
    ) {
        let decomp = RustTyDecomposition::from_ty(sig.output(), def_id);
        MutRefCurrentSnap::new(deps, decomp)?.snap_at_expiry(result)
    } else {
        result
    };
    // A mutable reference that is not given back by this wand (so its
    // referent is not held here) is taken to be unchanged. The pledges cannot
    // observe this: one reading its final value is rejected (see
    // `pledges_for_axiom`).
    let mut after = Vec::with_capacity(pre.len());
    for (idx, (ty, pre)) in sig.inputs().iter().zip(&pre).enumerate() {
        let local = mir::Local::from_usize(idx + 1);
        let given_back = rhs.iter().any(|input| input.mir_local() == local);
        after.push(
            if given_back && matches!(ty.kind(), ty::TyKind::Ref(.., ty::Mutability::Mut)) {
                let decomp = RustTyDecomposition::from_ty(*ty, def_id);
                MutRefCurrentSnap::new(deps, decomp)?.snap(*pre)
            } else {
                *pre
            },
        );
    }
    let args = vcx.alloc_slice(&[pre.as_slice(), after.as_slice()].concat());
    let expr = pledge_func.call()(result, args, generics.get_ty(), generics.get_const());
    Ok(EncodedPledge {
        expiry_obligation: None,
        expiry_postcondition: PledgeExpr::new(def_id, expr),
    })
}
