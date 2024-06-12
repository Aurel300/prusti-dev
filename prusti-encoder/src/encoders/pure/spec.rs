use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};
use vir::Reify;

use crate::encoders::{
    predicate, mir_pure::PureKind, rust_ty_predicates::RustTyPredicatesEnc, MirPureEnc, most_generic_ty
};
pub struct MirSpecEnc;

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    pub pres: Vec<vir::Expr<'vir>>,
    pub posts: Vec<vir::Expr<'vir>>,
    pub pre_args: &'vir [vir::Expr<'vir>],
    pub post_args: &'vir [vir::Expr<'vir>],
}

impl TaskEncoder for MirSpecEnc {
    task_encoder::encoder_cache!(MirSpecEnc);

    type TaskDescription<'tcx> = (
        DefId,                    // The function annotated with specs
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
        bool,                     // If to encode as pure or not
    );

    type OutputFullLocal<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, substs, caller_def_id, pure) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        let local_defs = deps
            .require_local::<crate::encoders::local_def::MirLocalDefEnc>((
                def_id,
                substs,
                caller_def_id,
            ))?;
        let specs = deps
            .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;

        vir::with_vcx(|vcx| {
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<_> = if pure {
                let result_ty = local_defs.locals[mir::RETURN_PLACE].ty;
                local_iter
                    .map(|local| {
                        vcx.mk_local_ex(
                            local_defs.locals[local].local.name,
                            local_defs.locals[local].ty.snapshot,
                        )
                    })
                    .chain([vcx.mk_result(result_ty.snapshot)])
                    .collect()
            } else {
                local_iter
                    .map(|local| local_defs.locals[local].impure_snap)
                    .collect()
            };
            let all_args = vcx.alloc_slice(&all_args);
            let pre_args = if pure {
                &all_args[..all_args.len() - 1]
            } else {
                all_args
            };

            let to_bool = deps
                .require_ref::<RustTyPredicatesEnc>(vcx.tcx().types.bool)?
                .generic_predicate
                .expect_prim()
                .snap_to_prim;

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec,
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr;
                    let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                    to_bool.apply(vcx, [expr])
                })
                .collect::<Vec<vir::Expr<'_>>>();

            let is_async = vcx.tcx().generator_is_async(def_id);

            // TODO: check what happens for a pure async fn
            let post_args = if pure {
                all_args
            } else if !is_async {
                let post_args: Vec<_> = pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs.locals[mir::RETURN_PLACE].impure_snap])
                    .collect();
                vcx.alloc_slice(&post_args)
            } else {
                // on async functions, there is a mismatch between the signature of the declared
                // async fn (and thus the spec function) and the poll method, whose parameters are
                // the return place, the future, and the `ResumeTy`
                // hence, we need to adapt the arguments available in the postconditions to be
                // the old-expressions of the future's ghost fields as well as the return place
                // TODO: once the automatically added invariants (that the ghost fields don't
                // change) are added, these no longer need to be old-expressions
                let ghost_fields = {
                    let generator_ty = local_defs.locals[mir::Local::from(1_u32)].ty;
                    let predicate::PredicateEncData::StructLike(gen_domain_data) = generator_ty.specifics else {
                        panic!("expected generator domain to be struct-like");
                    };
                    gen_domain_data.snap_data.field_access
                };
                let generator_snap = local_defs.locals[mir::Local::from(1_u32)].impure_snap;
                let post_args = ghost_fields
                    .iter()
                    .map(|field| {
                        let field_read = field.read.apply(vcx, [generator_snap]);
                        vcx.mk_old_expr(field_read)
                    })
                    .chain([local_defs.locals[mir::RETURN_PLACE].impure_snap])
                    .collect::<Vec<_>>();
                vcx.alloc_slice(&post_args)
            };

            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec,
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr;
                    let expr = expr.reify(vcx, (*spec_def_id, post_args));
                    to_bool.apply(vcx, [expr])
                })
                .collect::<Vec<vir::Expr<'_>>>();
            let data = MirSpecEncOutput {
                pres,
                posts,
                pre_args,
                post_args,
            };
            Ok((data, ()))
        })
    }
}
