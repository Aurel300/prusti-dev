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

                    verifier.verify(viper_program)
                })
            }
        }
    }
}