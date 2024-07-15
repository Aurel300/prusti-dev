#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(never_type)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;
mod encoder_traits;
pub mod request;
pub mod ide;


use prusti_interface::{environment::{EnvBody, EnvQuery}, PrustiError};
use prusti_rustc_interface::{
    middle::ty,
    hir,
    hir::def_id::DefId,
    span::Span,
    data_structures::fx::FxHashMap,
};
use prusti_utils::config;
use task_encoder::TaskEncoder;

use crate::encoders::{lifted::{
    casters::{CastTypeImpure, CastTypePure, CastersEnc},
    ty_constructor::TyConstructorEnc
}, MirPolyImpureEnc};
use crate::ide::encoding_info::SpanOfCallContracts;

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    query: EnvQuery<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
    // this is None if the verification is not selective - all procedures should be encoded.
    // if the verification is selective, only the procedures in this vector should be encoded with body
    procedures: Option<&Vec<DefId>>,
    contract_spans_map: &mut FxHashMap<DefId, SpanOfCallContracts>,
) -> request::RequestWithContext {

    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate
    let source_map = tcx.sess.source_map();
    for def_id in tcx.hir().body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn |
            hir::def::DefKind::AssocFn => {
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                        let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                        let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();

                        if config::show_ide_info() {
                            // TODO: only handles inherent spec items
                            contract_spans_map
                                .entry(def_id)
                                .and_modify(|contract_spans| {
                                    let mut spans: Vec<Span> = Vec::new();
                                    // the `get` method has a comment about how it is a bad API, but does it matter
                                    // if we know if the result is inkerent, inherited or refined here?
                                    // if let Some((_, pre_def_ids)) = proc_spec.pres.get() {
                                    if let Some(pre_def_ids) = proc_spec.pres.expect_empty_or_inherent() {
                                        let mut pre_spans = pre_def_ids
                                            .iter()
                                            .map(|pre_def_id| query.get_def_span(pre_def_id))
                                            .collect::<Vec<Span>>();
                                        spans.append(&mut pre_spans);
                                    }
                                    if let Some(post_def_ids) = proc_spec.posts.expect_empty_or_inherent() {
                                        let mut post_spans = post_def_ids
                                            .iter()
                                            .map(|pre_def_id| query.get_def_span(pre_def_id))
                                            .collect::<Vec<Span>>();
                                        spans.append(&mut post_spans);
                                    }
                                    if let Some(pledges) = proc_spec.pledges.expect_empty_or_inherent() {
                                        let mut pledge_spans = pledges
                                            .iter()
                                            .map(|pledge| {
                                                let rhs = query.get_def_span(pledge.rhs);
                                                if let Some(lhs) = pledge.lhs { query.get_def_span(lhs).to(rhs) }
                                                else { rhs }
                                            }).collect::<Vec<Span>>();
                                        spans.append(&mut pledge_spans);
                                    }
                                    if let Some(Some(purity_def_id)) = proc_spec.purity.expect_empty_or_inherent() {
                                        spans.push(query.get_def_span(purity_def_id));
                                    }
                                    if let Some(Some(terminates_def_id)) = proc_spec.terminates.expect_empty_or_inherent() {
                                        spans.push(query.get_def_span(terminates_def_id.to_def_id()));
                                    }
                                    contract_spans.set_contract_spans(spans, source_map);
                                });
                        }

                        (is_pure, is_trusted)
                }).unwrap_or_default();

                if procedures.map_or(true, |procs| procs.contains(&def_id)) && !(is_trusted && is_pure) {
                    let res = MirPolyImpureEnc::encode(def_id, false);
                    assert!(res.is_ok());
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    fn header(code: &mut String, title: &str) {
        code.push_str("// -----------------------------\n");
        code.push_str(&format!("// {}\n", title));
        code.push_str("// -----------------------------\n");
    }
    let mut viper_code = String::new();

    let mut program_fields = vec![];
    let mut program_domains = vec![];
    let mut program_predicates = vec![];
    let mut program_functions = vec![];
    let mut program_methods = vec![];

    // We output results from both monomorphic and polymorphic encoding of
    // functions, because even when Prusti is configured to use the monomorphic
    // it will still use `MirPolyImpureEnc` directly sometimes (see usages
    // earlier in this file).
    header(&mut viper_code, "methods");
    for output in crate::encoders::MirMonoImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
        program_methods.push(output.method);
    }
    for output in crate::encoders::MirPolyImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
        program_methods.push(output.method);
    }

    header(&mut viper_code, "functions");
    for output in crate::encoders::PureFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "MIR builtins");
    for output in crate::encoders::MirBuiltinEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
        program_functions.push(output.function);
    }

    header(&mut viper_code, "generics");
    for output in crate::encoders::GenericEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.type_snapshot));
        viper_code.push_str(&format!("{:?}\n", output.param_snapshot));
        program_domains.push(output.type_snapshot);
        program_domains.push(output.param_snapshot);
    }

    header(&mut viper_code, "pure generic casts");
    for cast_functions in CastersEnc::<CastTypePure>::all_outputs() {
        for cast_function in cast_functions {
            viper_code.push_str(&format!("{:?}\n", cast_function));
            program_functions.push(cast_function);
        }
    }

    header(&mut viper_code, "impure generic casts");
    for cast_methods in CastersEnc::<CastTypeImpure>:: all_outputs() {
        for cast_method in cast_methods {
            viper_code.push_str(&format!("{:?}\n", cast_method));
            program_methods.push(cast_method);
        }
    }

    header(&mut viper_code, "snapshots");
    for output in crate::encoders::DomainEnc_all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output));
        program_domains.push(output);
    }

    header(&mut viper_code, "type constructors");
    for output in TyConstructorEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.domain));
        program_domains.push(output.domain);
    }

    header(&mut viper_code, "types");
    for output in crate::encoders::PredicateEnc::all_outputs() {
        for field in output.fields {
            viper_code.push_str(&format!("{:?}", field));
            program_fields.push(field);
        }
        for field_projection in output.ref_to_field_refs {
            viper_code.push_str(&format!("{:?}", field_projection));
            program_functions.push(field_projection);
        }
        viper_code.push_str(&format!("{:?}\n", output.unreachable_to_snap));
        program_functions.push(output.unreachable_to_snap);
        viper_code.push_str(&format!("{:?}\n", output.function_snap));
        program_functions.push(output.function_snap);
        for pred in output.predicates {
            viper_code.push_str(&format!("{:?}\n", pred));
            program_predicates.push(pred);
        }
        viper_code.push_str(&format!("{:?}\n", output.method_assign));
        program_methods.push(output.method_assign);
    }

    // std::fs::write("local-testing/simple.vpr", viper_code).unwrap();

    let program = vir::with_vcx(|vcx| vcx.mk_program(
        vcx.alloc_slice(&program_fields),
        vcx.alloc_slice(&program_domains),
        vcx.alloc_slice(&program_predicates),
        vcx.alloc_slice(&program_functions),
        vcx.alloc_slice(&program_methods),
    ));

    /*
    let source_path = std::path::Path::new("source/path"); // TODO: env.name.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    */

    request::RequestWithContext {
        program: program.to_ref(),
    }
}

pub fn backtranslate_error(
    error_kind: &str,
    offending_pos_id: usize,
    reason_pos_id: Option<usize>,
) -> Option<Vec<PrustiError>> {
    vir::with_vcx(|vcx| vcx.backtranslate(
        error_kind,
        offending_pos_id,
        reason_pos_id,
    ))
}
