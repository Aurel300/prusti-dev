// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![warn(clippy::disallowed_types)]
#![feature(rustc_private)]

// use log::info;
use ::log::{debug, error, info};
use crate::{
    spawn_server_thread, PrustiClient, ServerMessage, VerificationRequest,
    VerificationRequestProcessing, ViperBackendConfig,
};
use prusti_utils::{config, Stopwatch};
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::EnvDiagnostic,
    specs::typed,
    PrustiError,
};
use prusti_rustc_interface::{
    span::DUMMY_SP,
    errors::MultiSpan,
};
use viper::{self, PersistentCache, Viper};
use once_cell::sync::Lazy;

mod client;
mod process_verification;
mod server;
mod server_message;
mod verification_request;
mod backend;

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
    let mut prusti_errors: Vec<_> = vec![];

    pin_mut!(verification_messages);

    while let Some((program_name, server_msg)) = verification_messages.next().await {
        match server_msg {
            ServerMessage::Termination(result) => handle_termination_message(env_diagnostic, program_name, result, &mut prusti_errors, &mut overall_result),
        }
    }

    overall_result
}

fn handle_termination_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    // &self,
    program_name: String,
    result: viper::VerificationResult,
    prusti_errors: &mut Vec<PrustiError>,
    overall_result: &mut VerificationResult
) {
    debug!("Received termination message with result {result:?} in verification of {program_name}");
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
            for verification_error in errors {
                debug!(
                    "Verification error in {}: {:?}",
                    program_name.clone(),
                    verification_error
                );
                // temporary error emition, delete when verification errors can be backtranslated again
                env_diagnostic.span_err_with_help_and_notes(
                    MultiSpan::new(),
                    &format!(
                        "Verification error in {}: {:?}",
                        program_name.clone(),
                        verification_error
                    ),
                    &None,
                    &[],
                );
            }
            *overall_result = VerificationResult::Failure;
        }
        viper::VerificationResultKind::JavaException(exception) => {
            error!("Java exception: {}", exception.get_stack_trace());
            PrustiError::internal(
                format!("in {program_name}: {exception}"),
                DUMMY_SP.into(),
            )
            .emit(env_diagnostic);
            // .emit(&self.env.diagnostic);
            *overall_result = VerificationResult::Failure;
        }
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
