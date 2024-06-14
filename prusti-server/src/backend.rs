use crate::{dump_viper_program, ServerMessage};
use log::{debug, info};
use prusti_utils::{
    config,
    Stopwatch,
};
use std::{
    sync::{mpsc, Arc},
    thread, time,
};
use viper::{jni_utils::JniUtils, VerificationContext, VerificationResultKind, Viper};
use viper_sys::wrappers::{java, viper::*};

pub enum Backend<'a> {
    Viper(
        viper::Verifier<'a>,
        &'a VerificationContext<'a>,
        &'a Arc<Viper>,
    ),
}

impl<'a> Backend<'a> {
    pub fn verify(
        &mut self,
        program: vir::ProgramRef,
        sender: mpsc::Sender<ServerMessage>,
    ) -> VerificationResultKind {
        match self {
            Backend::Viper(ref mut verifier, context, viper_arc) => {
                let mut stopwatch =
                    Stopwatch::start("prusti-server backend", "construction of JVM objects");

                let ast_utils = context.new_ast_utils();

                ast_utils.with_local_frame(16, || {
                    let ast_factory = context.new_ast_factory();

                    let viper_program = vir::with_vcx(|vcx| {
                        let program = vcx.get_program(program);
                        prusti_viper::program_to_viper(program, &ast_factory)
                    });

                    if config::dump_viper_program() {
                        stopwatch.start_next("dumping viper program");
                        dump_viper_program(
                            &ast_utils,
                            viper_program,
                            &program.get_name_with_check_mode(),
                        );
                    }

                    stopwatch.start_next("viper verification");

                    if config::report_viper_messages() {
                        verify_and_poll_msgs(verifier, context, viper_arc, viper_program, sender)
                    } else {
                        verifier.verify(viper_program)
                    }
                })
            }
        }
    }
}

fn verify_and_poll_msgs(
    verifier: &mut viper::Verifier,
    verification_context: &viper::VerificationContext,
    viper_arc: &Arc<Viper>,
    viper_program: viper::Program,
    sender: mpsc::Sender<ServerMessage>,
) -> VerificationResultKind {
    let mut kind = VerificationResultKind::Success;

    // get the reporter global reference outside of the thread scope because it needs to
    // be dropped by thread attached to the jvm. This is also why we pass it as reference
    // and not per value
    let env = &verification_context.env();
    let jni = JniUtils::new(env);
    let verifier_wrapper = silver::verifier::Verifier::with(env);
    let reporter = jni.unwrap_result(verifier_wrapper.call_reporter(*verifier.verifier_instance()));
    let rep_glob_ref = env.new_global_ref(reporter).unwrap();

    debug!("Starting viper message polling thread");

    // start thread for polling messages
    thread::scope(|scope| {
        let polling_thread = scope.spawn(|| polling_function(viper_arc, &rep_glob_ref, sender));
        kind = verifier.verify(viper_program);
        polling_thread.join().unwrap();
    });
    debug!("Viper message polling thread terminated");
    kind
}

fn polling_function(
    viper_arc: &Arc<Viper>,
    rep_glob_ref: &jni::objects::GlobalRef,
    sender: mpsc::Sender<ServerMessage>,
) {
    let verification_context = viper_arc.attach_current_thread();
    let env = verification_context.env();
    let jni = JniUtils::new(env);
    let reporter_instance = rep_glob_ref.as_obj();
    let reporter_wrapper = silver::reporter::PollingReporter::with(env);
    loop {
        while reporter_wrapper
            .call_hasNewMessage(reporter_instance)
            .unwrap()
        {
            let msg = reporter_wrapper
                .call_getNewMessage(reporter_instance)
                .unwrap();
            debug!("Polling thread received {}", jni.class_name(msg).as_str());
            match jni.class_name(msg).as_str() {
                "viper.silver.reporter.VerificationTerminationMessage" => return,
                "viper.silver.reporter.BlockReachedMessage" => {
                    let msg_wrapper = silver::reporter::BlockReachedMessage::with(env);
                    let method_name = 
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_methodName(msg)));
                    let label = 
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_label(msg)));
                    let path_id = jni.unwrap_result(msg_wrapper.call_pathId(msg));
                    sender
                      .send(ServerMessage::BlockReached {
                          viper_method: method_name,
                          vir_label: label,
                          path_id: path_id,
                        })
                        .unwrap();
                },
                "viper.silver.reporter.PathProcessedMessage" => {
                    let msg_wrapper = silver::reporter::PathProcessedMessage::with(env);
                    let method_name = 
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_methodName(msg)));
                    let label = 
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_label(msg)));
                    let path_id = jni.unwrap_result(msg_wrapper.call_pathId(msg));
                    let result = 
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_verificationResultKind(msg)));
                    sender
                      .send(ServerMessage::PathProcessed {
                          viper_method: method_name,
                          vir_label: label,
                          path_id: path_id,
                          result: result,
                        })
                        .unwrap();
                },
                _ => (),
            }
        }
        thread::sleep(time::Duration::from_millis(10));
    }
}