// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{ServerMessage, VerificationRequest, ServerRequest};
use futures::{lock, stream::Stream};
use log::{debug, info};
use std::{
    sync::{self, mpsc},
    thread,
};

struct ThreadJoin {
    handle: Option<thread::JoinHandle<()>>,
}

// we join the thread after dropping the sender for the ServerRequests, so
// that the verification thread actually terminates
impl Drop for ThreadJoin {
    fn drop(&mut self) {
        self.handle.take().unwrap().join().unwrap();
    }
}

pub struct VerificationRequestProcessing {
    mtx_rx_servermsg: lock::Mutex<mpsc::Receiver<ServerMessage>>,
    mtx_tx_verreq: sync::Mutex<mpsc::Sender<ServerRequest>>,
    // mtx_tx_verreq has to be dropped before thread_join
    #[allow(dead_code)]
    thread_join: ThreadJoin,
}

impl Default for VerificationRequestProcessing {
    fn default() -> Self {
        Self::new()
    }
}

/// A structure that lives for all the requests and has a single thread working on all the
/// requests sequentially.
/// On reception of a verification request, we send it through a channel to the already running
/// thread.
impl VerificationRequestProcessing {
    pub fn new() -> Self {
        let (tx_servermsg, rx_servermsg) = mpsc::channel();
        let (tx_verreq, rx_verreq) = mpsc::channel();
        let mtx_rx_servermsg = lock::Mutex::new(rx_servermsg);
        let mtx_tx_verreq = sync::Mutex::new(tx_verreq);

        let handle = thread::spawn(move || verification_thread(rx_verreq, tx_servermsg));
        Self {
            mtx_rx_servermsg,
            mtx_tx_verreq,
            thread_join: ThreadJoin {
                handle: Some(handle),
            },
        }
    }

<<<<<<< HEAD
    // Normalize the request before reaching the cache.
    let normalization_info = NormalizationInfo::normalize_program(&mut request.program);*/

    let hash = request.get_hash();
    info!(
        "Verification request hash: {} - for program {}",
        hash,
        request.program.get_name(),
    );
    /*
        let build_or_dump_viper_program = || {
            let mut stopwatch = Stopwatch::start("prusti-server", "construction of JVM objects");
            let ast_factory = verification_context.new_ast_factory();

            let viper_program = prusti_viper::program_to_viper(request.program, &ast_factory);
            //let viper_program = request
            //    .program
            //    .to_viper(prusti_common::vir::LoweringContext::default(), &ast_factory);
            if config::dump_viper_program() {
                stopwatch.start_next("dumping viper program");
                dump_viper_program(
                    &ast_utils,
                    viper_program,
                    &request.program.get_name_with_check_mode(),
                );
            }

            viper_program
        };

        // Only for testing: Print the hash and skip verification.
        if config::print_hash() {
            println!(
                "Received verification request for: {}",
                request.program.get_name()
            );
            println!("Hash of the request is: {hash}");
            // Some tests need the dump to report a diff of the Viper programs.
            if config::dump_viper_program() {
                ast_utils.with_local_frame(16, || {
                    let _ = build_or_dump_viper_program();
                });
            }
            return viper::VerificationResult::Success;
        }
    */
    // Early return in case of cache hit
    if config::enable_cache() {
        if let Some(result) = cache.get(hash) {
            info!(
                "Using cached result {:?} for program {}",
                &result,
                request.program.get_name()
            );
            /*if config::dump_viper_program() {
                ast_utils.with_local_frame(16, || {
                    let _ = build_or_dump_viper_program();
                });
            }
            normalization_info.denormalize_result(&mut result);*/
            return result;
        }
    };

    let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");

    // Create a new verifier each time.
    // Workaround for https://github.com/viperproject/prusti-dev/issues/744
    let mut backend = match request.backend_config.backend {
        VerificationBackend::Carbon | VerificationBackend::Silicon => Backend::Viper(
            new_viper_verifier(
                request.program.get_name(),
                verification_context,
                request.backend_config,
            ),
            verification_context,
        ),
    };

    stopwatch.start_next("backend verification");
    let result = backend.verify(request.program);

    // Don't cache Java exceptions, which might be due to misconfigured paths.
    if config::enable_cache() && !matches!(result, VerificationResult::JavaException(_)) {
=======
    pub fn verify(&self, request: VerificationRequest) -> impl Stream<Item = ServerMessage> + '_ {
        let hash = request.get_hash();
>>>>>>> ide/rewrite-2023-assistant-features
        info!(
            "Verification request hash: {} - for program {}",
            hash,
            request.program.get_name(),
        );

        request.send(&self.mtx_tx_verreq);

<<<<<<< HEAD
pub fn dump_viper_program(
    ast_utils: &viper::AstUtils,
    program: viper::Program,
    program_name: &str,
) {
    let namespace = "viper_program";
    let filename = format!("{program_name}.vpr");
    info!("Dumping Viper program to '{}/{}'", namespace, filename);
    report(
        namespace,
        filename,
        bodge_field_adt_discr(ast_utils.pretty_print(program)),
    );
}

/// The pretty printing of Viper adt field discriminators is currently broken,
/// this is a workaround for that. Remove once we're on a Viper version where
/// that is fixed.
fn bodge_field_adt_discr(s: String) -> String {
    assert_eq!(include_str!("../../viper-toolchain"), "v-2025-02-04-1042\n");
    s.split('.')
        .map(|s| {
            let Some(space) = s.as_bytes().iter().position(|c| *c == b' ') else {
                return std::borrow::Cow::Borrowed(s);
            };
            if space == 0 || s.as_bytes()[space - 1] != b'?' {
                return std::borrow::Cow::Borrowed(s);
            }
            std::borrow::Cow::Owned(format!("is{}{}", &s[..space - 1], &s[space..]))
        })
        .collect::<Vec<_>>()
        .join(".")
}

fn new_viper_verifier<'v, 't: 'v>(
    program_name: &str,
    verification_context: &'v viper::VerificationContext<'t>,
    backend_config: ViperBackendConfig,
) -> viper::Verifier<'v> {
    let mut verifier_args: Vec<String> = backend_config.verifier_args;
    let report_path: Option<PathBuf>;
    if config::dump_debug_info() {
        let log_path = config::log_dir()
            .join("viper_tmp")
            .join(to_legal_file_name(program_name));
        create_dir_all(&log_path).unwrap();
        report_path = Some(log_path.join("report.csv"));
        let log_dir_str = log_path.to_str().unwrap();
        match backend_config.backend {
            VerificationBackend::Silicon => {
                verifier_args.extend(vec![
                    "--tempDirectory".to_string(),
                    log_dir_str.to_string(),
                    "--printMethodCFGs".to_string(),
                    //"--printTranslatedProgram".to_string(),
                ])
=======
        futures::stream::unfold(false, move |done: bool| async move {
            if done {
                return None;
>>>>>>> ide/rewrite-2023-assistant-features
            }
            let msg = self.mtx_rx_servermsg.lock().await.recv().unwrap();
            let mut done = false;
            if let ServerMessage::Termination(_) = msg {
                done = true;
            }
            Some((msg, done))
        })
    }
}

fn verification_thread(
    rx_verreq: mpsc::Receiver<ServerRequest>,
    tx_servermsg: mpsc::Sender<ServerMessage>,
) {
    debug!("Verification thread started.");

    while let Ok(request) = rx_verreq.recv() {
        match request {
            ServerRequest::Verification(verification_request) => verification_request.process(
                &tx_servermsg,
            ),
        }
    }
    debug!("Verification thread finished.");
}
