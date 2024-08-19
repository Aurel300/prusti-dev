use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{ClauseKind, PredicateKind},
};
use task_encoder::TaskEncoder;
use vir::{vir_format_identifier, BinOpKind};

use crate::{
    encoders::lifted::{
        generic::LiftedGenericEnc,
        ty::{EncodeGenericsAsLifted, LiftedTyEnc},
    },
    generic_args_support::{extract_ty_params, unique},
};

use super::{TraitEnc, TraitTyArgsEnc};

/// Encodes axioms for traits implementations via user-written `impl` blocks.
pub struct UserDefinedTraitImplEnc;

impl TaskEncoder for UserDefinedTraitImplEnc {
    task_encoder::encoder_cache!(UserDefinedTraitImplEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let ty = vcx.tcx().type_of(task_key).skip_binder();
            let ty_params = unique(extract_ty_params(ty)).collect::<Vec<_>>();
            let trait_ref = vcx.tcx().impl_trait_ref(task_key).unwrap().skip_binder();
            let encoded_trait_ref = deps.require_ref::<TraitEnc>(trait_ref.def_id)?;
            let lifted_ty_expr = deps
                .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(ty)?
                .expr(vcx);
            let implements_expr = encoded_trait_ref.implements(
                lifted_ty_expr,
                deps.require_local::<TraitTyArgsEnc>(trait_ref).unwrap(),
            );

            let constraints = vcx.tcx().predicates_of(task_key);
            let mut encoded_ty_constraints = vec![];
            for (constraint, _) in constraints.predicates {
                match constraint.as_predicate().kind().skip_binder() {
                    PredicateKind::Clause(ClauseKind::Trait(trait_clause)) => {
                        let predicate_trait_ref =
                            deps.require_ref::<TraitEnc>(trait_clause.def_id())?;
                        let type_to_implement = deps
                            .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(
                                trait_clause.self_ty(),
                            )?
                            .expr(vcx);
                        let implements_expr = predicate_trait_ref.implements(
                            type_to_implement,
                            deps.require_local::<TraitTyArgsEnc>(trait_clause.trait_ref)
                                .unwrap(),
                        );
                        encoded_ty_constraints.push(implements_expr);
                    }
                    _ => todo!(),
                }
            }

            let mut reqs_iter = encoded_ty_constraints.into_iter();

            let conditional_implements_expr = if let Some(first) = reqs_iter.next() {
                let precondition = reqs_iter.fold(first, |acc, req| {
                    vcx.mk_bin_op_expr(BinOpKind::And, acc, req)
                });
                vcx.mk_bin_op_expr(BinOpKind::Implies, precondition, implements_expr)
            } else {
                implements_expr
            };

            let axiom_expr = if ty_params.is_empty() {
                conditional_implements_expr
            } else {
                let generics = ty_params
                    .iter()
                    .map(|param| deps.require_ref::<LiftedGenericEnc>(*param).unwrap())
                    .collect::<Vec<_>>();
                let decls = generics.iter().map(|g| g.decl()).collect::<Vec<_>>();
                vcx.mk_forall_expr(
                    vcx.alloc_slice(&decls),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[implements_expr])]),
                    conditional_implements_expr,
                )
            };
            let axiom = vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{}_implements_{}_axiom",
                    ty,
                    vcx.tcx().def_path_str(trait_ref.def_id)
                ),
                axiom_expr,
            );
            let domain = vcx.mk_domain(
                vir_format_identifier!(
                    vcx,
                    "{}_implements_{}_domain",
                    ty,
                    vcx.tcx().def_path_str(trait_ref.def_id)
                ),
                &[],
                vcx.alloc_slice(&[axiom]),
                &[],
            );
            Ok((domain, ()))
        })
    }
}
