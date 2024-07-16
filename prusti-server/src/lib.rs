// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![warn(clippy::disallowed_types)]
#![feature(rustc_private)]

use ::log::{debug, error, info};
use crate::{
    spawn_server_thread, PrustiClient, ServerMessage, VerificationRequest,
    VerificationRequestProcessing, ViperBackendConfig,
};
use prusti_utils::{config, Stopwatch};
use prusti_interface::{
    data::VerificationResult,
    environment::EnvDiagnostic,
    specs::typed,
    PrustiError,
};
use prusti_rustc_interface::{
    span::DUMMY_SP,
    errors::MultiSpan,
};
use viper::{self, PersistentCache, Viper};
use crate::ide::ide_verification_result::IdeVerificationResult;

mod client;
mod process_verification;
mod server;
mod server_message;
mod verification_request;
mod backend;
pub mod ide;

pub use backend::*;
pub use client::*;
pub use process_verification::*;
pub use server::*;
pub use server_message::*;
pub use verification_request::*;

// Futures returned by `Client` need to be executed in a compatible tokio runtime.
pub use tokio;
use tokio::runtime::Builder;
use rustc_hash::FxHashMap;
use serde_json::json;
use async_stream::stream;
use futures_util::{pin_mut, Stream, StreamExt};

/// Verify a list of programs.
/// Returns a list of (program_name, verification_result) tuples.
pub fn verify_programs(
    env_diagnostic: &EnvDiagnostic<'_>,
    programs: Vec<vir::ProgramRef>
    ) -> VerificationResult {
    let verification_requests = programs.into_iter().map(|mut program| {
        let rust_program_name = program.get_rust_name().to_string();
        let program_name = program.get_name().to_string();
        // Prepend the Rust file name to the program.
        program.set_name(&format!("{rust_program_name}_{program_name}"));
        let backend = config::viper_backend().parse().unwrap();
        let request = VerificationRequest {
            program,
            backend_config: ViperBackendConfig::new(backend),
        };
        (program_name, request)
    });

    let mut stopwatch = Stopwatch::start("prusti-server", "verifying Viper program");
    // runtime used either for client connecting to server sequentially
    // or to sequentially verify the requests -> single thread is sufficient
    // why single thread if everything is asynchronous? VerificationRequestProcessing in
    // prusti-server/src/process_verification.rs only has a single thread and the underlying
    // viper instance already uses as many cores as possible
    let rt = Builder::new_current_thread()
        .thread_name("prusti-viper")
        .enable_all()
        .build()
        .expect("failed to construct Tokio runtime");
        
    let overall_result = rt.block_on(async {
        if let Some(server_address) = config::server_address() {
            let verification_messages = verify_requests_server(verification_requests.collect(), server_address);
            handle_stream(env_diagnostic, verification_messages).await
        } else {
            let vrp = VerificationRequestProcessing::new();
            let verification_messages = verify_requests_local(verification_requests.collect(), &vrp);
            handle_stream(env_diagnostic, verification_messages).await
        }
    });
    stopwatch.finish();
    overall_result
}

async fn handle_stream(
    env_diagnostic: &EnvDiagnostic<'_>,
    verification_messages: impl Stream<Item = (String, ServerMessage)>,
) -> VerificationResult {
    let mut overall_result = VerificationResult::Success;
    // we want quantifier_pos_ID + program_name + q_name as identifier because there are
    // different q_names for the same ID and each program reports independent results
    // key: (pos_id, program_name), key to result: q_name result: num_instantiations
    let mut quantifier_instantiations: FxHashMap<(u64, String), FxHashMap<String, u64>> =
        FxHashMap::default();

    let mut prusti_errors: Vec<_> = vec![];

    pin_mut!(verification_messages);

    while let Some((program_name, server_msg)) = verification_messages.next().await {
        match server_msg {
            ServerMessage::Termination(result) => handle_termination_message(env_diagnostic, program_name, result, &mut prusti_errors, &mut overall_result),
            ServerMessage::QuantifierInstantiation {
                q_name,
                insts,
                pos_id,
            } => handle_quantifier_instantiation_message(env_diagnostic, program_name, q_name, insts, pos_id, &mut quantifier_instantiations),
            ServerMessage::QuantifierChosenTriggers {
                viper_quant,
                triggers,
                pos_id,
            } => handle_quantifier_chosen_triggers_message(env_diagnostic, program_name, viper_quant, triggers, pos_id),
            ServerMessage::BlockReached {
                viper_method,
                vir_label,
                path_id,
            } => handle_block_processing_message(env_diagnostic, program_name, viper_method, vir_label, path_id, None),
            ServerMessage::PathProcessed {
                viper_method,
                vir_label,
                path_id,
                result,
            } => handle_block_processing_message(env_diagnostic, program_name, viper_method, vir_label, path_id, Some(result)),
        }
    }

    // if we are in an ide, we already emit the errors asynchronously, otherwise we wait for
    // all of them because we want the errors to be reported sortedly
    if !config::show_ide_info() {
        prusti_errors.sort();

        for prusti_error in prusti_errors {
            debug!("Prusti error: {:?}", prusti_error);
            prusti_error.emit(env_diagnostic);
        }
    }

    overall_result
}

fn handle_termination_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    program_name: String,
    result: viper::VerificationResult,
    prusti_errors: &mut Vec<PrustiError>,
    overall_result: &mut VerificationResult
) {
    debug!("Received termination message with result {result:?} in verification of {program_name}");
    if config::show_ide_info() {
        PrustiError::message(
            format!(
                "ideVerificationResult{}",
                serde_json::to_string(&IdeVerificationResult::from(&result))
                    .unwrap()
            ),
            DUMMY_SP.into(),
        )
        .emit(env_diagnostic);
    }
    match result.kind {
        // nothing to do
        viper::VerificationResultKind::Success => (),
        viper::VerificationResultKind::ConsistencyErrors(errors) => {
            for error in errors {
                PrustiError::internal(
                    format!("consistency error in {program_name}: {error:?}"),
                    DUMMY_SP.into(),
                )
                .emit(env_diagnostic);
            }
            *overall_result = VerificationResult::Failure;
        }
        viper::VerificationResultKind::Failure(errors) => {
            errors
                .into_iter()
                .flat_map(|error| prusti_encoder::backtranslate_error(
                    &error.full_id,
                    error.offending_pos_id.unwrap().parse::<usize>().unwrap(),
                    error.reason_pos_id.and_then(|id| id.parse::<usize>().ok()),
                )
                .expect("verification error could not be backtranslated")
                .into_iter())
                .for_each(|prusti_error| prusti_error.emit(env_diagnostic));
            // for verification_error in errors {
            //     debug!(
            //         "Verification error in {}: {:?}",
            //         program_name.clone(),
            //         verification_error
            //     );
            *overall_result = VerificationResult::Failure;
        }
        viper::VerificationResultKind::JavaException(exception) => {
            error!("Java exception: {}", exception.get_stack_trace());
            PrustiError::internal(
                format!("in {program_name}: {exception}"),
                DUMMY_SP.into(),
            )
            .emit(env_diagnostic);
            *overall_result = VerificationResult::Failure;
        }
    }
}

fn handle_quantifier_instantiation_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    program_name: String,
    q_name: String,
    insts: u64,
    pos_id: u64,
    quantifier_instantiations: &mut FxHashMap<(u64, String), FxHashMap<String, u64>>
) {
    if config::report_viper_messages() {
        debug!("Received #{insts} quantifier instantiations of {q_name} for position id {pos_id} in verification of {program_name}");
        // match self.encoder.error_manager().position_manager().get_span_from_id(pos_id) {
        //     Some(span) => {
        //         let key = (pos_id, program_name.clone());
        //         if !quantifier_instantiations.contains_key(&key) {
        //             quantifier_instantiations.insert(key.clone(), FxHashMap::default());
        //         }
        //         let map = quantifier_instantiations.get_mut(&key).unwrap();
        //         // for some reason, the aux quantifiers by the same z3 instance (same uniqueId
        //         // in silicon) can have different amount of instantiations.
        //         // e.g. we receive a message with 100 instantiations for a certain quantifier
        //         // and afterwards a message with 20 instantiations for the same one.
        //         // All verifying the same viper program and by the same z3 instance.
        //         // Since I don see a better way to take this into account than taking the
        //         // maximum, that is exactly what we do here.
        //         let old_inst = map.get(&q_name).unwrap_or(&0);
        //         map.insert(q_name, std::cmp::max(insts, *old_inst));
        //         let mut n: u64 = 0;
        //         for (q_name, insts) in map.iter() {
        //             debug!("Key: {q_name}, Value: {insts}");
        //             n += *insts;
        //         }
        //         PrustiError::message(
        //             format!("quantifierInstantiationsMessage{}",
        //                 json!({"instantiations": n, "method": program_name}),
        //             ), span.clone()
        //         ).emit(env_diagnostic);
        //     },
        //     None => error!("#{insts} quantifier instantiations of {q_name} for unknown position id {pos_id} in verification of {program_name}"),
        // }
    }
}

fn handle_quantifier_chosen_triggers_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    program_name: String,
    viper_quant: String,
    triggers: String,
    pos_id: u64
) {
    if config::report_viper_messages() && pos_id != 0 {
        debug!("Received quantifier triggers {triggers} for quantifier {viper_quant} for position id {pos_id} in verification of {program_name}");
        // match self.encoder.error_manager().position_manager().get_span_from_id(pos_id) {
        //     Some(span) => {
        //         PrustiError::message(
        //             format!("quantifierChosenTriggersMessage{}",
        //                 json!({"viper_quant": viper_quant, "triggers": triggers}),
        //             ), span.clone()
        //         ).emit(&self.env.diagnostic);
        //     },
        //     None => error!("Invalid position id {pos_id} for viper quantifier {viper_quant} in verification of {program_name}"),
        // }
    }
}

// TODO: may or may not need program name translation
fn viper_method_to_rust_method(_viper_method: &String, program_name: &String) -> Option<String> {
    Some(program_name.clone())
}

// TODO
fn vir_label_to_pos(_vir_label: &String) -> Option<MultiSpan> {
    Some(MultiSpan::from_span(DUMMY_SP.into()))
}

fn handle_block_processing_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    program_name: String,
    viper_method: String,
    vir_label: String,
    path_id: i32,
    result: Option<String>,
) {
    if config::report_viper_messages() && config::report_block_messages() {
        let processed = result != None;
        debug!("Received {}: {{ method: {viper_method} ({program_name}) message, vir_label: {vir_label}, path_id: {path_id} }}",
                if processed {"path processed"} else {"block reached"});
        if let Some(method_name) = viper_method_to_rust_method(&viper_method, & program_name) { 
            if let Some(span) = vir_label_to_pos(&vir_label) {
                PrustiError::message(
                    format!("{}{}",
                        if processed {"pathProcessedMessage"} else {"blockReachedMessage"},
                        if processed {json!({"method": method_name, "path_id": path_id, "result": result.unwrap()})}
                        // FIXME: outputting vir_label only because it makes the messages different, otherwise the errors get merged.
                        // should be removed once backtranslation of labels is implemented so the resulting spans are different.
                        else         {json!({"method": method_name, "path_id": path_id, "label": vir_label})},
                    ), span.clone()
                ).emit(env_diagnostic);
            } else { error!("Could not map vir label {vir_label} to a position in verification of method {method_name} in {program_name}") }
        } else { error!("Could not map viper method {viper_method} to a Rust method in verification of {program_name}") }
    }
}

fn verify_requests_server(
    verification_requests: Vec<(String, VerificationRequest)>,
    server_address: String,
) -> impl Stream<Item = (String, ServerMessage)> {
    let server_address = if server_address == "MOCK" {
        spawn_server_thread().to_string()
    } else {
        server_address
    };
    info!("Connecting to Prusti server at {}", server_address);
    let verification_stream = stream! {
        for (program_name, request) in verification_requests {
            yield PrustiClient::verify(server_address.clone(), request).await.map(move |msg| (program_name.clone(), msg));
        }
    };
    verification_stream.flatten()
}

fn verify_requests_local<'a>(
    verification_requests: Vec<(String, VerificationRequest)>,
    vrp: &'a VerificationRequestProcessing,
) -> impl Stream<Item = (String, ServerMessage)> + 'a {
    let verification_stream = stream! {
        for (program_name, request) in verification_requests {
            yield vrp.verify(request).map(move |msg| (program_name.clone(), msg));
        }
    };
    verification_stream.flatten()
}
