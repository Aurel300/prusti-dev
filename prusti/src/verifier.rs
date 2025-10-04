//! A module that invokes the verifier `prusti-viper`

use log::{debug, warn};
use prusti_interface::{data::VerificationTask, environment::Environment, specs::typed};
use prusti_utils::{config, report::user};

#[tracing::instrument(name = "prusti::verify", level = "debug", skip(env))]
pub fn verify<'tcx>(
    env: Environment<'tcx>,
    def_spec: typed::DefSpecificationMap,
    verification_task: VerificationTask<'tcx>,
) {
    if env.diagnostic.has_errors() {
        warn!("The compiler reported an error, so the program will not be verified.");
    } else {
        debug!("Verification task: {:?}", &verification_task);
        user::message(format!(
            "{}erification of {} items...",
            if verification_task.selective { "Selective v" } else { "V" },
            verification_task.procedures.len()
        ));

        if config::print_collected_verification_items() {
            println!(
                "Collected verification items {}:",
                verification_task.procedures.len()
            );
            for procedure in &verification_task.procedures {
                println!(
                    "procedure: {} at {:?}",
                    env.name.get_item_def_path(*procedure),
                    env.query.get_def_span(procedure)
                );
            }
        }

        // encode the crate to a RequestWithContext
        // TODO: push RequestWithContext through (replace VerificationRequest
        //   which is constructed further inside `prusti_server`)
<<<<<<< HEAD
        let request = prusti_encoder::test_entrypoint(env.tcx(), env.body, def_spec);
=======
        let request = prusti_encoder::test_entrypoint(
            env.tcx(),
            env.body,
            def_spec,
            if verification_task.selective { Some(verification_task.procedures) } else { None },
            &env.diagnostic,
        );

>>>>>>> ide/rewrite-2023-assistant-features
        let program = request.program;
        let mut success = true;

<<<<<<< HEAD
        for prusti_error in prusti_encoder::early_errors() {
            success = false;
            prusti_error.emit(&env.diagnostic);
        }

        let mut results = prusti_server::verify_programs(vec![program]);
        assert_eq!(results.len(), 1); // TODO: eventually verify separate methods as separate programs again?

        let result = results.pop().unwrap().1;
        if std::env::var("LOCAL_TESTING").is_ok() {
            println!("raw result: {result:?}");
        }
        success &= match result {
            viper::VerificationResult::Success => true,
            viper::VerificationResult::JavaException(_e) => false,
            viper::VerificationResult::ConsistencyErrors(_e) => false,
            viper::VerificationResult::Failure(errors) => {
                for error in errors {
                    // TODO: offending_pos_id should always be set!
                    if let Some(offending_pos_id) = error.offending_pos_id {
                        if let Some(translated_errors) = prusti_encoder::backtranslate_error(
                            &error.full_id,
                            offending_pos_id.parse::<usize>().unwrap(),
                            error.reason_pos_id.and_then(|id| id.parse::<usize>().ok()),
                        ) {
                            for prusti_error in translated_errors {
                                prusti_error.emit(&env.diagnostic);
                            }
                        }
                    } else {
                        eprintln!("verifier error without offending_pos_id: {error:?}");
                    }
                }
                false
            }
        };
        if !success {
            user::message("Verification failed");
            // assert!(
            //     env.diagnostic.has_errors()
            //         || config::internal_errors_as_warnings()
            //         || (config::skip_unsupported_features()
            //             && config::allow_unreachable_unsupported_code())
            // );
            std::process::exit(1);
=======
        let result = prusti_server::verify_programs(&env.diagnostic, vec![program]);

        println!("verification result: {result:?}");

        if matches!(result, VerificationResult::Failure) {
            // TODO: This will be unnecessary if diagnostic errors are emitted
            // earlier, it's useful for now to ensure that Prusti returns an
            // error code when verification fails
            env.diagnostic.span_err_with_help_and_notes(
                MultiSpan::new(),
                "Verification failed",
                &None,
                &[],
            );
>>>>>>> ide/rewrite-2023-assistant-features
        }

        //let verification_result =
        //    if verification_task.procedures.is_empty() && verification_task.types.is_empty() {
        //        VerificationResult::Success
        //    } else {
        //        debug!("Dump borrow checker info...");
        //        env.dump_borrowck_info(&verification_task.procedures);
        //
        //        let mut verifier = Verifier::new(&env, def_spec);
        //        let verification_result = verifier.verify(&verification_task);
        //        debug!("Verifier returned {:?}", verification_result);
        //
        //        verification_result
        //    };
        //
        //match verification_result {
        //    VerificationResult::Success => {
        //        if env.diagnostic.has_errors() {
        //            user::message(
        //                "Verification result is inconclusive because errors \
        //                               were encountered during encoding.",
        //            );
        //        } else {
        //            user::message(format!(
        //                "Successful verification of {} items",
        //                verification_task.procedures.len()
        //            ));
        //        }
        //    }
        //    VerificationResult::Failure => {
        //        user::message("Verification failed");
        //        assert!(
        //            env.diagnostic.has_errors()
        //                || config::internal_errors_as_warnings()
        //                || (config::skip_unsupported_features()
        //                    && config::allow_unreachable_unsupported_code())
        //        );
        //    }
        //};
    }
}
