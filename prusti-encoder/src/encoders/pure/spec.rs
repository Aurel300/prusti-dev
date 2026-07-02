use std::borrow::Borrow;

use prusti_interface::{
    PrustiError,
    specs::{specifications::find_trait_method_substs, typed::Pledge},
};
use prusti_rustc_interface::{
    middle::mir,
    span::{Span, def_id::DefId},
};

use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType, Reify};

use crate::encoders::{
    MirLocalDefEncTask, MirPureEnc,
    mir_pure::{ExprInput, PureKind},
    ty::{RustTyDecomposition, generics::GParams, use_pure::TyUsePureEnc},
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
        vir::with_vcx(|vcx| self.expr.reify(vcx, (self.did, args.0)))
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
    pub pres: Vec<vir::ExprBool<'vir>>,
    pub posts: Vec<vir::ExprBool<'vir>>,
    pub pledges: Vec<EncodedPledge<'vir>>,
    pub pre_args: &'vir FxHashMap<mir::Local, vir::ExprSnap<'vir>>,
    #[allow(dead_code)]
    pub post_args: &'vir FxHashMap<mir::Local, vir::ExprSnap<'vir>>,
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
    /// `_1s`, ... `_ns`, and `_0s`, respectively, all of snapshot types.
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

            let to_bool = deps
                .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(
                    vcx.tcx().types.bool,
                ))?
                .expect_native()
                .snap_to_prim;

            // Encode each functional precondition; if one cannot be encoded (e.g.
            // it uses an unsupported feature), report the error at *that spec's*
            // span and skip only it, keeping the permission contract and the other
            // specs intact.
            let pres = specs
                .pres
                .iter()
                .filter_map(|spec_def_id| {
                    let span = vcx.tcx().def_span(spec_def_id);
                    match deps.require_dep::<crate::encoders::MirPureEnc>(
                        crate::encoders::MirPureEncTask {
                            encoding_depth: 0,
                            kind: PureKind::Spec(specs.extern_spec),
                            parent_def_id: *spec_def_id,
                            param_env: vcx.tcx().param_env(spec_def_id),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(context_def_id),
                        },
                    ) {
                        Ok(out) => {
                            let expr = out.expr.downcast_ty();
                            let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                            Some(vcx.with_span(span, |_| to_bool(expr).downcast_ty()))
                        }
                        Err(err) => {
                            vcx.emit_early_error(PrustiError::unsupported(
                                format!(
                                    "cannot encode precondition: {}",
                                    crate::encoders::mir_fn::dep_error_message(&err),
                                ),
                                span.into(),
                            ));
                            None
                        }
                    }
                })
                .collect::<Vec<vir::ExprBool<'_>>>();

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
                MirSpecEncMode::PureWithResult | MirSpecEncMode::PureWithoutResult => all_args,
            };
            let posts = specs
                .posts
                .iter()
                .filter_map(|spec_def_id| {
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |vcx| {
                        let out = match deps.require_dep::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(context_def_id),
                            },
                        ) {
                            Ok(out) => out,
                            Err(err) => {
                                vcx.emit_early_error(PrustiError::unsupported(
                                    format!(
                                        "cannot encode postcondition: {}",
                                        crate::encoders::mir_fn::dep_error_message(&err),
                                    ),
                                    span.into(),
                                ));
                                return None;
                            }
                        };
                        vcx.handle_error("postcondition.violated:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "postcondition might not hold",
                                span.into(),
                            )])
                        });
                        let expr = out.expr.downcast_ty();
                        let expr = expr.reify(vcx, (*spec_def_id, post_args));
                        Some(to_bool(expr).downcast_ty())
                    })
                })
                .collect::<Vec<vir::ExprBool<'_>>>();
            let pledges = specs
                .pledges
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
                                let span = vcx.tcx().def_span(lhs_def_id);
                                match deps.require_dep::<crate::encoders::MirPureEnc>(
                                    crate::encoders::MirPureEncTask {
                                        encoding_depth: 0,
                                        kind: PureKind::Spec(specs.extern_spec),
                                        parent_def_id: lhs_def_id,
                                        param_env: vcx.tcx().param_env(lhs_def_id),
                                        substs,
                                        caller_def_id: Some(context_def_id),
                                    },
                                ) {
                                    Ok(out) => {
                                        let lhs = out.expr.downcast_ty::<vir::CSnap>();
                                        Some(PledgeExpr::new(
                                            lhs_def_id,
                                            to_bool.call()(lhs).downcast_ty(),
                                        ))
                                    }
                                    Err(err) => {
                                        vcx.emit_early_error(PrustiError::unsupported(
                                            format!(
                                                "cannot encode pledge: {}",
                                                crate::encoders::mir_fn::dep_error_message(&err),
                                            ),
                                            span.into(),
                                        ));
                                        return None;
                                    }
                                }
                            }
                            None => None,
                        };
                        let rhs_span = vcx.tcx().def_span(rhs_def_id);
                        let rhs = match deps.require_dep::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: *rhs_def_id,
                                param_env: vcx.tcx().param_env(rhs_def_id),
                                substs,
                                caller_def_id: Some(context_def_id),
                            },
                        ) {
                            Ok(out) => out.expr.downcast_ty(),
                            Err(err) => {
                                vcx.emit_early_error(PrustiError::unsupported(
                                    format!(
                                        "cannot encode pledge: {}",
                                        crate::encoders::mir_fn::dep_error_message(&err),
                                    ),
                                    rhs_span.into(),
                                ));
                                return None;
                            }
                        };
                        let rhs_expr = vcx.with_span(rhs_span, move |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "pledge postcondition might not hold",
                                    rhs_span.into(),
                                )])
                            });
                            to_bool.call()(rhs).downcast_ty()
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
