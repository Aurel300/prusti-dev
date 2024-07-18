// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::{debug, info};
use viper::{self, VerificationBackend, Program, AstUtils, Viper, VerificationContext, VerificationResultKind, smt_manager::SmtManager, VerificationResult, PersistentCache, Cache};
use prusti_utils::{
    config,
    Stopwatch,
    report::log::{report, to_legal_file_name},
};
use crate::{ServerMessage, Backend};
use once_cell::sync::Lazy;
use std::{
    sync::{self, mpsc, Arc},
    fs::create_dir_all,
    path::PathBuf,
};

/// Server requests that are sent between client and server
/// These are oblivious to the backend being used for verification
/// and could potentially be something other than verification.
pub(crate) enum ServerRequest {
    Verification(ServerVerificationRequest),
}

/// Server requests that are sent between threads of the verifying process.
pub(crate) struct ServerVerificationRequest {
    kind: ServerVerificationRequestKind,
}

/// Specifies the kind of backend to be used for verification and carries necessary data.
enum ServerVerificationRequestKind {
    // viper program, program name, backend config
    JVMViperRequest(jni::objects::GlobalRef, Arc<Viper>, String, ViperBackendConfig),
}

impl ServerVerificationRequest {
    pub fn execute<'v, 't: 'v>(
        &self,
        sender: &mpsc::Sender<ServerMessage>,
    ) {
        let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");
        let mut result = VerificationResult {
            item_name: "".to_string(),
            kind: VerificationResultKind::Success,
            cached: false,
            time_ms: 0,
        };

        match &self.kind {
            ServerVerificationRequestKind::JVMViperRequest(viper_program_ref, viper_arc, program_name, backend_config) => {
                let verification_context = viper_arc.attach_current_thread();
                let mut backend = match backend_config.backend {
                    VerificationBackend::Carbon | VerificationBackend::Silicon => Backend::Viper(
                        new_viper_verifier(
                            &program_name,
                            &verification_context,
                            backend_config.clone(),
                        ),
                        &verification_context,
                        &viper_arc,
                    ),
                };
                stopwatch.start_next("backend verification");
                result.item_name = program_name.clone();
                result.kind = backend.verify(viper::Program::new(viper_program_ref.as_obj()), sender.clone());
                drop(viper_program_ref);
                result.time_ms = stopwatch.finish().as_millis();
            }
        }

        /*normalization_info.denormalize_result(&mut result.kind);*/
        sender.send(ServerMessage::Termination(result)).unwrap();
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationRequest {
    pub program: vir::ProgramRef,
    pub backend_config: ViperBackendConfig,
}

impl<'vir> VerificationRequest {
    pub(crate) fn get_hash(&self) -> u64 {
        self.program.get_hash()
    }

    /// Builds a more specific request based on the backend configuration and sends it.
    /// This includes the vir-viper translation if the Viper backend is used.
    pub(crate) fn send_request(
        &self,
        mtx_tx_verreq: &sync::Mutex<mpsc::Sender<ServerRequest>>,
    ) {
        let request = self.build_request();

        mtx_tx_verreq
            .lock()
            .unwrap()
            .send(ServerRequest::Verification(request))
            .unwrap();
    }

    fn build_request(
            &self,
    ) -> ServerVerificationRequest {
        match self.backend_config.backend {
            VerificationBackend::Carbon | VerificationBackend::Silicon => {
                let mut stopwatch =
                    Stopwatch::start("prusti-server backend", "construction of JVM objects");

                // TODO: this panics when run over a server and two different requests are sent
                // because it tries to construct the same JVM twice.
                let viper_arc = Arc::new(
                    Viper::new_with_args(&config::viper_home(), config::extra_jvm_args())
                );
                let context = viper_arc.attach_current_thread();
                let ast_utils = context.new_ast_utils();

                ast_utils.with_local_frame(16, || {
                    let ast_factory = context.new_ast_factory();

                    let viper_program = vir::with_vcx(|vcx| {
                        let program = vcx.get_program(self.program);
                        prusti_viper::program_to_viper(program, &ast_factory)
                    });

                    if config::dump_viper_program() {
                        stopwatch.start_next("dumping viper program");
                        dump_viper_program(
                            &ast_utils,
                            viper_program,
                            &self.program.get_name_with_check_mode(),
                        );
                    }

                    let viper_program_ref = context
                        .env()
                        .new_global_ref(viper_program.to_jobject())
                        .unwrap();

                    let kind = ServerVerificationRequestKind::JVMViperRequest(
                        viper_program_ref,
                        viper_arc.clone(),
                        self.program.get_name().to_string(),
                        self.backend_config.clone(),
                    );
                    ServerVerificationRequest { kind }
                })
            },
        }
    }
}

pub fn dump_viper_program(
    ast_utils: &viper::AstUtils,
    program: viper::Program,
    program_name: &str,
) {
    let namespace = "viper_program";
    let filename = format!("{program_name}.vpr");
    info!("Dumping Viper program to '{}/{}'", namespace, filename);
    report(namespace, filename, ast_utils.pretty_print(program));
}

/// The configuration for the viper backend, (i.e. verifier).
/// Expresses which backend (silicon or carbon) should be used, and provides command-line arguments
/// to the viper verifier.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Eq, PartialEq, Hash)]
pub struct ViperBackendConfig {
    pub backend: VerificationBackend,
    pub verifier_args: Vec<String>,
}

impl ViperBackendConfig {
    pub fn new(backend: VerificationBackend) -> Self {
        let mut verifier_args = config::extra_verifier_args();
        match backend {
            VerificationBackend::Silicon => {
                if config::use_more_complete_exhale() {
                    verifier_args.push("--enableMoreCompleteExhale".to_string());
                }
                if config::counterexample() {
                    verifier_args.push("--counterexample".to_string());
                    verifier_args.push("mapped".to_string());
                }
                if let Some(number) = config::number_of_parallel_verifiers() {
                    verifier_args.push("--numberOfParallelVerifiers".to_string());
                    verifier_args.push(number.to_string());
                }

                verifier_args.extend(vec![
                    "--assertTimeout".to_string(),
                    config::assert_timeout().to_string(),
                    "--proverConfigArgs".to_string(),
                ]);
                // model.partial changes the default case of functions in counterexamples
                // to #unspecified
                let mut prover_args = format!(
                    "smt.qi.eager_threshold={} model.partial={}",
                    config::smt_qi_eager_threshold(),
                    config::counterexample()
                );

                verifier_args.push(prover_args);

                verifier_args.extend(vec!["--logLevel".to_string(), "ERROR".to_string()]);

                if let Some(check_timeout) = config::check_timeout() {
                    verifier_args.push("--checkTimeout".to_string());
                    verifier_args.push(check_timeout.to_string());
                }

                if config::report_block_messages() && config::report_viper_messages() {
                    verifier_args.push("--generateBlockMessages".to_string());
                }
            }
            VerificationBackend::Carbon => {
                verifier_args.extend(vec!["--disableAllocEncoding".to_string()]);
            }
        }
        Self {
            backend,
            verifier_args,
        }
    }
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
            }
            VerificationBackend::Carbon => verifier_args.extend(vec![
                "--boogieOpt".to_string(),
                format!("/logPrefix {log_dir_str}"),
                //"--print".to_string(), "./log/boogie_program/program.bpl".to_string(),
            ]),
        }
    } else {
        report_path = None;
        if backend_config.backend == VerificationBackend::Silicon {
            // TODO: unknown option?
            // verifier_args.extend(vec!["--disableTempDirectory".to_string()]);
        }
    }
    let (smt_solver, smt_manager) = if config::use_smt_wrapper() {
        std::env::set_var("PRUSTI_ORIGINAL_SMT_SOLVER_PATH", config::smt_solver_path());
        let log_path = config::log_dir()
            .join("smt")
            .join(to_legal_file_name(program_name));
        create_dir_all(&log_path).unwrap();
        let smt_manager = SmtManager::new(
            log_path,
            config::preserve_smt_trace_files(),
            config::write_smt_statistics(),
            config::smt_qi_ignore_builtin(),
            config::smt_qi_bound_global_kind(),
            config::smt_qi_bound_trace(),
            config::smt_qi_bound_trace_kind(),
            config::smt_unique_triggers_bound(),
            config::smt_unique_triggers_bound_total(),
        );
        std::env::set_var(
            "PRUSTI_SMT_SOLVER_MANAGER_PORT",
            smt_manager.port().to_string(),
        );
        if config::log_smt_wrapper_interaction() {
            std::env::set_var("PRUSTI_LOG_SMT_INTERACTION", "true");
        }
        (config::smt_solver_wrapper_path(), smt_manager)
    } else {
        (config::smt_solver_path(), SmtManager::default())
    };
    let boogie_path = config::boogie_path();
    if let Some(bound) = config::smt_qi_bound_global() {
        // We need to set the environment variable to reach our Z3 wrapper.
        std::env::set_var("PRUSTI_SMT_QI_BOUND_GLOBAL", bound.to_string());
    }

    verification_context.new_verifier(
        backend_config.backend,
        verifier_args,
        report_path,
        smt_solver,
        boogie_path,
        smt_manager,
    )
}