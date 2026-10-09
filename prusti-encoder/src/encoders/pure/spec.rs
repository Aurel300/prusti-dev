use std::borrow::Borrow;

use prusti_interface::{
    PrustiError,
    specs::{
        specifications::find_trait_method_substs,
        typed::{ExternSpecKind, Pledge},
    },
};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::{Span, def_id::DefId},
};

use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType, Reify};

use crate::encoders::{
    MirLocalDefEncTask, MirPureEnc,
    mir_pure::{ExprInput, MirPureEncOutput, PureKind},
    ty::generics::{GArgs, GParams},
};
pub struct MirSpecEnc;

/// The VIR expression and span corresponding to either the lhs or rhs of a
/// pledge. It will be conjoined to the permission expression of the
/// corresponding side of the wand for the encoded pledge.
#[derive(Debug, Clone, Copy)]
pub struct PledgeExpr<'vir> {
    did: DefId,
    expr: vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>,
}

#[derive(Debug, Clone, Copy)]
pub struct PledgeArgs<'vir>(&'vir FxHashMap<mir::Local, vir::ExprSnap<'vir>>, mir::Local);

impl<'vir> std::ops::Index<mir::Local> for PledgeArgs<'vir> {
    type Output = vir::ExprSnap<'vir>;

    fn index(&self, index: mir::Local) -> &Self::Output {
        if index == mir::RETURN_PLACE {
            &self.0[&self.1]
        } else {
            &self.0[&index]
        }
    }
}

/// Offset of the keys under which the pre-state snapshots of the arguments
/// are passed to a specification over two states.
const PRE_STATE_KEY_OFFSET: usize = 1 << 20;

/// The key under which the pre-state snapshot of argument `local` is passed
/// to a specification over two states. Looked up for an argument in `old`;
/// if absent, the argument's regular snapshot is used.
pub fn pre_state_key(local: mir::Local) -> mir::Local {
    mir::Local::from_usize(PRE_STATE_KEY_OFFSET + local.index())
}

/// Offset of the keys under which the arguments and the result are passed
/// cast to the callee's generic context, see `PledgeArgs::with_callee_ctx`.
const CALLEE_CTX_KEY_OFFSET: usize = 2 << 20;

/// The key under which argument (or result) `local` is passed cast to the
/// callee's generic context, see `PledgeArgs::with_callee_ctx`.
pub fn callee_ctx_key(local: mir::Local) -> mir::Local {
    mir::Local::from_usize(CALLEE_CTX_KEY_OFFSET + local.index())
}

impl<'vir> PledgeArgs<'vir> {
    /// The number of arguments (without the result).
    pub fn arg_count(&self) -> usize {
        self.1.index() - 1
    }

    /// These arguments, additionally each passed cast by `cast` under
    /// `callee_ctx_key`; the result is passed under the key of the local
    /// after the last argument.
    pub fn with_callee_ctx(
        self,
        mut cast: impl FnMut(mir::Local, vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir>,
    ) -> Self {
        let mut all_args = self.0.clone();
        for idx in 1..=self.1.index() {
            let local = mir::Local::from_usize(idx);
            all_args.insert(callee_ctx_key(local), cast(local, self.0[&local]));
        }
        vir::with_vcx(|vcx| PledgeArgs(vcx.alloc(all_args), self.1))
    }

    /// Arguments for a specification over snapshots of two states: the
    /// pre-state `pre` and a later state `post` (the post-state of the call,
    /// or the state after a pledge's expiry). Outside of `old`, the mutable
    /// reference arguments refer to the later state, so that e.g. `*x` is the
    /// final value of the referent; all other arguments (and all arguments
    /// inside `old`) refer to the pre-state.
    pub fn two_state(
        result: vir::ExprSnap<'vir>,
        pre: &[vir::ExprSnap<'vir>],
        post: &[vir::ExprSnap<'vir>],
        mut_args: &[bool],
    ) -> Self {
        assert_eq!(pre.len(), post.len());
        let mut all_args: FxHashMap<mir::Local, vir::ExprSnap<'vir>> = FxHashMap::default();
        for (idx, (pre, post)) in pre.iter().zip(post).enumerate() {
            let local = mir::Local::from_usize(idx + 1);
            let is_mut = mut_args.get(idx).copied().unwrap_or(false);
            all_args.insert(local, if is_mut { *post } else { *pre });
            all_args.insert(pre_state_key(local), *pre);
        }
        let result_local = mir::Local::from_usize(pre.len() + 1);
        all_args.insert(result_local, result);
        vir::with_vcx(|vcx| PledgeArgs(vcx.alloc(all_args), result_local))
    }
}

impl<'vir> PledgeExpr<'vir> {
    pub fn new(
        did: DefId,
        expr: vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>,
    ) -> Self {
        Self { did, expr }
    }

    pub fn pledge_args<T: Borrow<vir::ExprSnap<'vir>>>(
        result: vir::ExprSnap<'vir>,
        args: impl IntoIterator<Item = T>,
    ) -> PledgeArgs<'vir> {
        let mut all_args: FxHashMap<mir::Local, _> = args
            .into_iter()
            .enumerate()
            .map(|(idx, a)| ((idx + 1).into(), *a.borrow()))
            .collect();
        let result_local = (all_args.len() + 1).into();
        all_args.insert(result_local, result);
        vir::with_vcx(|vcx| PledgeArgs(vcx.alloc(all_args), result_local))
    }

    pub fn expr(&self, args: PledgeArgs<'vir>) -> vir::ExprBool<'vir> {
        vir::with_vcx(|vcx| {
            self.expr
                .reify(vcx, (self.did, args.0, vir::OldLabel::None))
        })
    }

    pub fn expr_at_label(&self, args: PledgeArgs<'vir>, label: &'vir str) -> vir::ExprBool<'vir> {
        vir::with_vcx(|vcx| {
            self.expr
                .reify(vcx, (self.did, args.0, vir::OldLabel::Label(label)))
        })
    }

    pub fn span(&self) -> Span {
        vir::with_vcx(|vcx| vcx.tcx().def_span(self.did))
    }
}

/// VIR expressions for a pledge, including a user-written `assert_on_expiry`
/// predicate if present.
#[derive(Clone, Copy, Debug)]
pub struct EncodedPledge<'vir> {
    /// The VIR expression and span corresponding to the `assert_on_expiry`
    /// predicate, if present.
    pub expiry_obligation: Option<PledgeExpr<'vir>>,
    /// The pure rhs of the wand.
    pub expiry_postcondition: PledgeExpr<'vir>,
}

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    /// Each precondition paired with the source span of its spec item.
    pub pres: Vec<(vir::ExprBool<'vir>, Span)>,
    /// Each postcondition paired with the source span of its spec item.
    pub posts: Vec<(vir::ExprBool<'vir>, Span)>,
    pub pledges: Vec<EncodedPledge<'vir>>,
    pub pre_args: &'vir FxHashMap<mir::Local, vir::ExprSnap<'vir>>,
    #[allow(dead_code)]
    pub post_args: &'vir FxHashMap<mir::Local, vir::ExprSnap<'vir>>,
}

impl<'vir> MirSpecEncOutput<'vir> {
    /// The precondition expressions, discarding their spans.
    pub fn pre_exprs(&self) -> impl Iterator<Item = vir::ExprBool<'vir>> + '_ {
        self.pres.iter().map(|(pre, _)| *pre)
    }

    /// The postcondition expressions, discarding their spans.
    pub fn post_exprs(&self) -> impl Iterator<Item = vir::ExprBool<'vir>> + '_ {
        self.posts.iter().map(|(post, _)| *post)
    }
}

/// State shared by every spec encoded within one `MirSpecEnc` task.
#[derive(Clone, Copy)]
struct SpecEncCtx<'vir> {
    extern_spec: Option<ExternSpecKind>,
    enc_mode: MirSpecEncMode,
    context_def_id: DefId,
    substs: ty::GenericArgsRef<'vir>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MirSpecEncMode {
    /// Assumes the arguments and the result are available in local variables
    /// `_1p`, ... `_np`, and `_0p`, respectively, all of type `Ref``, i.e.,
    /// their snapshot is taken first.
    Impure,

    /// Assumes the arguments are available in local varialbes `_1s`, ... `_ns`,
    /// all of snapshot types, and the result is the result of the current
    /// function, i.e., `result` in Viper syntax.
    PureWithResult,

    /// Assumes the arguments and the result are available in local variables
    /// `_1s`, ... `_ns`, and `_0s`, respectively, all of snapshot types. In
    /// the postconditions, the mutable reference arguments are instead
    /// `_1s_post`, ... `_ns_post`, their snapshots in the post-state (see
    /// `PledgeArgs::two_state`). The pledges are left to be reified by the
    /// user, also with `PledgeArgs::two_state`.
    PureWithoutResult,
}

impl TaskEncoder for MirSpecEnc {
    task_encoder::encoder_cache!(MirSpecEnc);
    const ENCODER_NAME: &'static str = "MIR spec encoder";

    type TaskDescription<'tcx> = (
        DefId, // The function annotated with specs
        DefId, // Context, i.e., where the specs are emitted
        MirSpecEncMode,
    );

    type OutputFullDependency<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, context_def_id, enc_mode) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let base_params = GParams::from(def_id);
            let context_params = GParams::from(context_def_id);
            let substs =
                find_trait_method_substs(vcx.tcx(), context_def_id, context_params.rust_params())
                    .map(|s| s.1)
                    .unwrap_or(base_params.rust_params());
            let substs = vcx.tcx().mk_args(substs);
            let substs_for = |inherited: bool| {
                // if the spec is not inherited and we are currently building the spec for the actual function we're encoding,
                // do not use substitution
                if !inherited && def_id == context_def_id {
                    vcx.tcx().mk_args_from_iter(
                        context_params
                            .rust_params()
                            .iter()
                            .filter(|arg| arg.as_region().is_none()),
                    )
                } else {
                    substs
                }
            };

            let local_defs = deps.require_dep::<crate::encoders::local_def::MirLocalDefEnc>(
                MirLocalDefEncTask::LocalSubsts {
                    def_id,
                    context_def_id,
                    substs: if def_id == context_def_id {
                        context_params.rust_params()
                    } else {
                        substs
                    },
                    all_locals: false,
                },
            )?;
            let specs = deps
                .require_dep::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;
            let (pres, pres_inherited) = crate::encoders::spec_items(&specs.pres);
            let (posts, posts_inherited) = crate::encoders::spec_items(&specs.posts);
            let (pledges, pledges_inherited) = crate::encoders::spec_items(&specs.pledges);
            let pre_ctx = SpecEncCtx {
                extern_spec: specs.extern_spec,
                enc_mode,
                context_def_id,
                substs: substs_for(pres_inherited),
            };
            let post_ctx = SpecEncCtx {
                extern_spec: specs.extern_spec,
                enc_mode,
                context_def_id,
                substs: substs_for(posts_inherited),
            };
            let pledge_ctx = SpecEncCtx {
                extern_spec: specs.extern_spec,
                enc_mode,
                context_def_id,
                substs: substs_for(pledges_inherited),
            };

            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: FxHashMap<mir::Local, _> = match enc_mode {
                MirSpecEncMode::Impure => local_iter
                    .map(|local| (local, local_defs[local].impure_snap))
                    .collect(),
                MirSpecEncMode::PureWithResult => {
                    let result_ty = local_defs[mir::RETURN_PLACE].local_snap.ty();
                    local_iter
                        .map(|local| (local, vcx.mk_local_ex(local_defs[local].local_snap)))
                        .chain([((local_defs.arg_count + 1).into(), vcx.mk_result(result_ty))])
                        .collect()
                }
                MirSpecEncMode::PureWithoutResult => local_iter
                    .map(|local| (local, vcx.mk_local_ex(local_defs[local].local_snap)))
                    .chain([(
                        (local_defs.arg_count + 1).into(),
                        vcx.mk_local_ex(local_defs[mir::RETURN_PLACE].local_snap),
                    )])
                    .collect(),
            };
            let all_args = vcx.alloc(all_args);
            let pre_args = all_args; // it should be ok to provide more keys than required

            // Encode each functional precondition; if one cannot be encoded (e.g.
            // it uses an unsupported feature), report the error at *that spec's*
            // span and skip only it, keeping the permission contract and the other
            // specs intact.
            let pres: Vec<(vir::ExprBool<'_>, Span)> = pres
                .iter()
                .filter_map(|spec_def_id| {
                    let spec = Self::encode_pure(vcx, deps, pre_ctx, *spec_def_id, "precondition")?;
                    let expr = spec.expr.downcast_ty::<vir::Bool>();
                    let span = vcx.tcx().def_span(*spec_def_id);
                    // Reify *inside* the span scope: the nodes created by the
                    // reification pick up the ambient span, which makes error
                    // positions inside this precondition point at the spec.
                    let expr = vcx.with_span(span, |vcx| {
                        expr.reify(vcx, (*spec_def_id, pre_args, vir::OldLabel::None))
                    });
                    Some((expr, span))
                })
                .collect();

            let post_args = match enc_mode {
                MirSpecEncMode::Impure => {
                    let post_args: FxHashMap<mir::Local, vir::ExprSnap<'vir>> = pre_args
                        .iter()
                        .map(|(local, arg)| (*local, vcx.mk_old_expr(arg)))
                        .chain([(
                            (local_defs.arg_count + 1).into(),
                            local_defs[mir::RETURN_PLACE].impure_snap,
                        )])
                        .collect();
                    vcx.alloc(post_args)
                }
                MirSpecEncMode::PureWithResult => all_args,
                MirSpecEncMode::PureWithoutResult => {
                    let snap = |decl| vcx.mk_local_ex(decl);
                    let pre = local_defs.local_decl_args().map(snap).collect::<Vec<_>>();
                    let post = local_defs
                        .local_decl_args_post()
                        .map(snap)
                        .collect::<Vec<_>>();
                    let result = snap(local_defs.local_decl_ret());
                    let mut_args = crate::encoders::mut_ref_args(vcx.tcx(), def_id);
                    PledgeArgs::two_state(result, &pre, &post, &mut_args).0
                }
            };
            let posts: Vec<(vir::ExprBool<'_>, Span)> = posts
                .iter()
                .filter_map(|spec_def_id| {
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |vcx| {
                        let spec =
                            Self::encode_pure(vcx, deps, post_ctx, *spec_def_id, "postcondition")?;
                        vcx.handle_error("postcondition.violated:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "postcondition might not hold",
                                span.into(),
                            )])
                        });
                        let expr = spec.expr.downcast_ty::<vir::Bool>();
                        let expr = expr.reify(vcx, (*spec_def_id, post_args, vir::OldLabel::None));
                        let expr = expr.realloc_span();
                        Some((expr, span))
                    })
                })
                .collect();
            let pledges = pledges
                .iter()
                .filter_map(
                    |Pledge {
                         lhs: lhs_def_id,
                         rhs: rhs_def_id,
                         ..
                     }| {
                        // Optional expiry obligation (lhs). If it cannot be encoded,
                        // report at its span and skip the whole pledge.
                        let lhs_expr = match *lhs_def_id {
                            Some(lhs_def_id) => {
                                let spec = Self::encode_pure(
                                    vcx,
                                    deps,
                                    pledge_ctx,
                                    lhs_def_id,
                                    "pledge lhs",
                                )?;
                                let lhs = spec.expr.downcast_ty::<vir::Bool>();
                                Some(PledgeExpr::new(lhs_def_id, lhs))
                            }
                            None => None,
                        };
                        let spec =
                            Self::encode_pure(vcx, deps, pledge_ctx, *rhs_def_id, "pledge rhs")?;
                        let rhs = spec.expr.downcast_ty::<vir::Bool>();
                        let rhs_span = vcx.tcx().def_span(rhs_def_id);
                        let rhs_expr = vcx.with_span(rhs_span, move |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "pledge postcondition might not hold",
                                    rhs_span.into(),
                                )])
                            });
                            rhs
                        });
                        let rhs_expr = PledgeExpr::new(*rhs_def_id, rhs_expr);
                        Some(EncodedPledge {
                            expiry_obligation: lhs_expr,
                            expiry_postcondition: rhs_expr,
                        })
                    },
                )
                .collect::<Vec<_>>();
            let data = MirSpecEncOutput {
                pres,
                posts,
                pledges,
                pre_args,
                post_args,
            };
            Ok(((), data))
        })
    }
}

impl MirSpecEnc {
    fn encode_pure<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        ctx: SpecEncCtx<'vir>,
        def_id: DefId,
        type_: &str,
    ) -> Option<MirPureEncOutput<'vir>> {
        let span = vcx.tcx().def_span(def_id);
        let spec = deps.require_dep::<MirPureEnc>(crate::encoders::MirPureEncTask {
            encoding_depth: 0,
            kind: PureKind::Spec {
                context: ctx.context_def_id,
                mode: ctx.enc_mode,
            },
            parent_def_id: def_id,
            gargs: GArgs::new(
                GParams::new_maybe_extern(ctx.context_def_id, ctx.extern_spec),
                ctx.substs,
            ),
        });
        spec.inspect_err(|err| {
            let (message, err_span) = crate::encoders::mir_fn::dep_error(err);
            vcx.emit_early_error(PrustiError::unsupported(
                format!("cannot encode {type_}: {message}"),
                err_span.unwrap_or(span).into(),
            ))
        })
        .ok()
    }
}
