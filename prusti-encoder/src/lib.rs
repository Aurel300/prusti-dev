#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(never_type)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;

use prusti_interface::environment::EnvBody;
use prusti_rustc_interface::{
    middle::ty,
    hir,
};
use vir::{fmt_domain_with_extras, CallableIdent, DomainFunction, DomainAxiom};
use std::fmt::{self, Debug, Formatter};

use crate::encoders::lifted_ty_function::LiftedTyFunctionEnc;

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> vir::Program<'tcx> {
    use task_encoder::TaskEncoder;

    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

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
                        (is_pure, is_trusted)
                }).unwrap_or_default();

                if !(is_trusted && is_pure) {
                    let substs = ty::GenericArgs::identity_for_item(tcx, def_id);
                    let res = crate::encoders::MirImpureEnc::encode((def_id, substs, None));
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

    header(&mut viper_code, "methods");
    for output in crate::encoders::MirImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
    }

    header(&mut viper_code, "functions");
    for output in crate::encoders::MirFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }

    header(&mut viper_code, "MIR builtins");
    for output in crate::encoders::MirBuiltinEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }

    header(&mut viper_code, "generics");
    for output in crate::encoders::GenericEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.type_snapshot));
    }

    header(&mut viper_code, "generic casts");
    for output in crate::encoders::generic_cast::GenericCastEnc::all_outputs() {
        for cast_function in output {
            viper_code.push_str(&format!("{:?}\n", cast_function));
        }
    }

    header(&mut viper_code, "snapshots");
    for output in crate::encoders::DomainEnc_all_outputs() {
        let lifted_ty_func_outputs = LiftedTyFunctionEnc::all_outputs();
        let lifted_ty_func_output = lifted_ty_func_outputs.iter()
            .find(|f_output| f_output.domain.name() == output.name);
        let (type_functions, type_axioms) = if let Some(f_output) = lifted_ty_func_output {
            (f_output.functions.iter().map(|a| *a).collect(), f_output.axioms.iter().map(|a| *a).collect())
        } else {
            (vec![], vec![])
        };
        struct DomainWithExtras<'a>(
            vir::Domain<'a>,
            Vec<DomainFunction<'a>>,
            Vec<DomainAxiom<'a>>
        );

        impl <'a> Debug for DomainWithExtras<'a> {
            fn fmt<'b>(&self, f: &mut Formatter<'_>) -> fmt::Result {
                fmt_domain_with_extras(f, self.0, &self.1, &self.2)
            }
        }
        viper_code.push_str(&format!("{:?}\n", DomainWithExtras(output, type_functions, type_axioms)));
    }

    header(&mut viper_code, "types");
    for output in crate::encoders::PredicateEnc::all_outputs() {
        for field in output.fields {
            viper_code.push_str(&format!("{:?}", field));
        }
        for field_projection in output.ref_to_field_refs {
            viper_code.push_str(&format!("{:?}", field_projection));
        }
        viper_code.push_str(&format!("{:?}\n", output.unreachable_to_snap));
        viper_code.push_str(&format!("{:?}\n", output.function_snap));
        for pred in output.predicates {
            viper_code.push_str(&format!("{:?}\n", pred));
        }
        viper_code.push_str(&format!("{:?}\n", output.method_assign));
    }

    std::fs::write("local-testing/simple.vpr", viper_code).unwrap();

    vir::with_vcx(|vcx|
        vcx.mk_program(
            &[],
            &[],
            &[],
            vcx.alloc_slice(&[
                vcx.mk_function("test_function", &[], &vir::TypeData::Bool, &[], &[], None),
            ]),
            &[]
        )
    )
}
