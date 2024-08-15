use crate::{ServerMessage, VIPER};
use log::{debug, info};
use prusti_utils::{
    config,
};
use std::{
    sync::mpsc,
    thread, time,
    collections::HashSet,
};
use viper::{jni_utils::JniUtils, VerificationContext, VerificationResultKind};
use viper_sys::wrappers::{viper::*};
use viper_sys::wrappers::java;

pub enum Backend<'a> {
    Viper(
        viper::Verifier<'a>,
        &'a VerificationContext<'a>,
        jni::objects::GlobalRef,
    ),
}

impl<'a> Backend<'a> {
    pub fn verify(
        &mut self,
        procedures: HashSet<String>,
        sender: mpsc::Sender<ServerMessage>,
    ) -> VerificationResultKind {
        match self {
            Backend::Viper(ref mut verifier, viper_thread, viper_program_ref) => {

                let ast_utils = viper_thread.new_ast_utils();

                ast_utils.with_local_frame(16, || {
                    let viper_program = viper::Program::new(viper_program_ref.as_obj());
                    if config::report_viper_messages() {
                        verify_and_poll_msgs(verifier, viper_thread, viper_program, procedures, sender)
                    } else {
                        verifier.verify(viper_program, None)
                    }
                })
            }
        }
    }
}

fn verify_and_poll_msgs(
    verifier: &mut viper::Verifier,
    verification_context: &viper::VerificationContext,
    viper_program: viper::Program,
    procedures: HashSet<String>,
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
        let polling_thread = scope.spawn(|| polling_function(&rep_glob_ref, procedures, sender));
        kind = verifier.verify(viper_program, Some(polling_thread));
    });
    debug!("Viper message polling thread terminated");
    kind
}

fn polling_function(
    rep_glob_ref: &jni::objects::GlobalRef,
    procedures: HashSet<String>,
    sender: mpsc::Sender<ServerMessage>,
) -> HashSet<u64> {
    debug!("attach polling thread to JVM.");
    let verification_context = VIPER
        .get()
        .expect("Viper was not instantiated before polling")
        .attach_current_thread();
    let env = verification_context.env();
    let jni = JniUtils::new(env);
    let reporter_instance = rep_glob_ref.as_obj();
    let reporter_wrapper = silver::reporter::PollingReporter::with(env);

    let mut error_hashes = HashSet::new();
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
                "viper.silver.reporter.QuantifierInstantiationsMessage" => {
                    let msg_wrapper = silver::reporter::QuantifierInstantiationsMessage::with(env);
                    let q_name =
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_quantifier(msg)));
                    let q_inst = jni.unwrap_result(msg_wrapper.call_instantiations(msg));
                    // debug!("QuantifierInstantiationsMessage: {} {}", q_name, q_inst);
                    // also matches the "-aux" and "_precondition" quantifiers generated
                    // we encoded the position id in the line and column number since this is not used by
                    // prusti either way
                    if q_name.starts_with("prog.l") {
                        let no_pref = q_name.strip_prefix("prog.l").unwrap();
                        let stripped = no_pref
                            .strip_suffix("-aux")
                            .or(no_pref.strip_suffix("_precondition"))
                            .unwrap_or(no_pref);
                        let parsed = stripped.parse::<usize>();
                        match parsed {
                            Ok(pos_id) => {
                                sender
                                    .send(ServerMessage::QuantifierInstantiation {
                                        q_name,
                                        insts: u64::try_from(q_inst).unwrap(),
                                        pos_id,
                                    })
                                    .unwrap();
                            }
                            _ => info!("Unexpected quantifier name {}", q_name),
                        }
                    }
                },
                "viper.silver.reporter.QuantifierChosenTriggersMessage" => {
                    let obj_wrapper = java::lang::Object::with(env);
                    let positioned_wrapper = silver::ast::Positioned::with(env);
                    let msg_wrapper = silver::reporter::QuantifierChosenTriggersMessage::with(env);

                    let viper_quant = jni.unwrap_result(msg_wrapper.call_quantifier(msg));
                    let viper_quant_str =
                        jni.get_string(jni.unwrap_result(obj_wrapper.call_toString(viper_quant)));
                    // debug!("quantifier chosen trigger quant: {viper_quant_str}");
                    // we encoded the position id in the line and column number since this is not used by
                    // prusti either way
                    let pos = jni.unwrap_result(positioned_wrapper.call_pos(viper_quant));
                    let pos_string =
                        jni.get_string(jni.unwrap_result(obj_wrapper.call_toString(pos)));
                    // debug!("quantifier chosen trigger pos: {pos_string}");
                    // TODO: the PR unconditionally does `pos_string.rfind('.').unwrap()` which crashes when there is no position.
                    // Is that intended?
                    if let Some(pos_id_index) = pos_string.rfind('.') {
                        // let pos_id_index = pos_string.rfind('.').unwrap();
                        let pos_id = pos_string[pos_id_index + 1..].parse::<usize>().unwrap();

                        let viper_triggers =
                            jni.get_string(jni.unwrap_result(msg_wrapper.call_triggers__string(msg)));
                        debug!(
                            "QuantifierChosenTriggersMessage: {} {} {}",
                            viper_quant_str, viper_triggers, pos_id
                        );
                        sender
                            .send(ServerMessage::QuantifierChosenTriggers {
                                viper_quant: viper_quant_str,
                                triggers: viper_triggers,
                                pos_id,
                            })
                            .unwrap();
                    }
                },
                "viper.silver.reporter.VerificationTerminationMessage" => return error_hashes,
                "viper.silver.reporter.EntitySuccessMessage" => {
                    let msg_wrapper = silver::reporter::EntitySuccessMessage::with(env);
                    let concerning = jni.unwrap_result(msg_wrapper.call_concerning(msg));
                    if jni.is_instance_of(concerning, "viper/silver/ast/Method") {
                        let method_wrapper = silver::ast::Method::with(env);
                        let method_name =
                            jni.get_string(jni.unwrap_result(method_wrapper.call_name(concerning)));
                        debug!("Entity success for method: {method_name}");
                        // this should only match local methods
                        if procedures.contains(&method_name) {
                            let verification_time = jni.unwrap_result(msg_wrapper.call_verificationTime(msg));
                            // verification_time is a long -> i64. but we are using u128
                            if verification_time >= 0 {
                                let verification_time_u128 = verification_time as u64 as u128;
                                sender
                                    .send(ServerMessage::MethodTermination {
                                        viper_method_name: method_name.to_string(),
                                        result: VerificationResultKind::Success,
                                        verification_time: verification_time_u128,
                                    })
                                    .unwrap();
                            } else {
                                debug!("EntitySuccessMessage for {} had negative verification time {}", method_name, verification_time);
                            }
                        }
                    } else {
                        debug!("Entity is not a method");
                    }
                },
                "viper.silver.reporter.EntityFailureMessage" => {
                    let msg_wrapper = silver::reporter::EntityFailureMessage::with(env);
                    let concerning = jni.unwrap_result(msg_wrapper.call_concerning(msg));
                    if jni.is_instance_of(concerning, "viper/silver/ast/Method") {
                        let method_wrapper = silver::ast::Method::with(env);
                        let method_name =
                            jni.get_string(jni.unwrap_result(method_wrapper.call_name(concerning)));
                        debug!("Entity failure for method: {method_name}");
                        // this should only match local methods
                        if procedures.contains(&method_name) {
                            let verification_time = jni.unwrap_result(msg_wrapper.call_verificationTime(msg));
                            // verification_time is a long -> i64. but we are using u128
                            if verification_time >= 0 {
                                    let viper_result = jni.unwrap_result(msg_wrapper.call_result(msg));
                                    let result = viper::extract_errors(&jni, &env, viper_result, Some(&mut error_hashes));
                                    let verification_time_u128 = verification_time as u64 as u128;
                                    sender
                                        .send(ServerMessage::MethodTermination {
                                            viper_method_name: method_name.to_string(),
                                            result,
                                            verification_time: verification_time_u128,
                                        })
                                        .unwrap();
                            } else {
                                debug!("EntityFailureMessage for {} had negative verification time {}", method_name, verification_time);
                            }
                        }
                    } else {
                        debug!("Received entity was not a method");
                    }

                },
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