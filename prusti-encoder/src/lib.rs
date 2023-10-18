#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(local_key_cell_methods)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;

use prusti_interface::{environment::EnvBody, specs::typed::SpecificationItem};
use prusti_rustc_interface::{
    middle::ty,
    hir,
};

/*
struct MirBodyPureEncoder;
#[derive(Hash, Clone, PartialEq, Eq)]
enum MirBodyPureEncoderTask<'tcx> {
    Function {
        parent_def_id: ty::WithOptConstParam<DefId>, // ID of the function
        param_env: ty::ParamEnv<'tcx>, // param environment at the usage site
        substs: ty::SubstsRef<'tcx>, // type substitutions at the usage site
    },
    Constant {
        parent_def_id: ty::WithOptConstParam<DefId>, // ID of the function
        promoted: mir::Promoted, // ID of a constant within the function
        param_env: ty::ParamEnv<'tcx>, // param environment at the usage site
        substs: ty::SubstsRef<'tcx>, // type substitutions at the usage site
    },
}
// impl<'tcx> MirBodyPureEncoder {} // TODO: shortcuts for creating tasks?
impl TaskEncoder for MirBodyPureEncoder {
    type TaskDescription<'vir, 'tcx> = MirBodyPureEncoderTask<'tcx>;
    type TaskKey<'vir, 'tcx> = (
        DefId, // ID of the function
        Option<mir::Promoted>, // ID of a constant within the function, or `None` if encoding the function itself
        ty::SubstsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    );
    type OutputFullLocal<'vir, 'tcx> = vir::Expr<'vir> where 'tcx: 'vir;

    type EncodingError = ();

    encoder_cache!(MirBodyPureEncoder);

    fn do_encode_full<'vir, 'tcx>(
        task_key: &Self::TaskKey<'vir, 'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, 'tcx>,
    ) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir, 'tcx>>,
    )> {
        todo!()
    }

    fn task_to_key<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::TaskKey<'vir, 'tcx> {
        match task {
            MirBodyPureEncoderTask::Function {
                parent_def_id,
                param_env,
                substs,
            } => (
                parent_def_id.did,
                None,
                substs, // TODO
            ),
            MirBodyPureEncoderTask::Constant {
                parent_def_id,
                promoted,
                param_env,
                substs,
            } => (
                parent_def_id.did,
                Some(*promoted),
                substs, // TODO
            ),
        }
    }

    fn task_to_output_ref<'vir, 'tcx>(_task: &Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx> {
        ()
    }
}*/

// delegate to MirBodyPureEncoder
// - MirConstantEncoder
// - MirFunctionPureEncoder
/*
struct MirBodyImpureEncoder<'vir, 'tcx>(PhantomData<&'vir ()>, PhantomData<&'tcx ()>);
impl<'vir, 'tcx> TaskEncoder<'vir, 'tcx> for MirBodyImpureEncoder<'vir, 'tcx> {
    type TaskDescription = (
        ty::WithOptConstParam<DefId>, // ID of the function
        ty::ParamEnv<'tcx>, // param environment at the usage site
        ty::SubstsRef<'tcx>, // type substitutions at the usage site
    );
    // TaskKey, OutputRef same as above
    type OutputFull = vir::Method<'vir>;
} 

struct MirTyEncoder<'vir, 'tcx>(PhantomData<&'vir ()>, PhantomData<&'tcx ()>);
impl<'vir, 'tcx> TaskEncoder<'vir, 'tcx> for MirTyEncoder<'vir, 'tcx> {
    type TaskDescription = ty::Ty<'tcx>;
    // TaskKey = TaskDescription
    type OutputRef = vir::Type<'vir>;
    type OutputFull = (
        Vec<vir::Domain<'vir>>,
        Vec<vir::Predicate<'vir>>,
    );
}
*/

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> vir::Program<'tcx> {
    use task_encoder::TaskEncoder;

    crate::encoders::init_def_spec(def_spec.clone());
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir_crate_items(()).definitions() {
        //println!("item: {def_id:?}");
        let kind = tcx.def_kind(def_id);

        //println!("  kind: {:?}", kind);
        /*if !format!("{def_id:?}").contains("foo") {
            continue;
        }*/
        match kind {
            hir::def::DefKind::Fn => {
                if prusti_interface::specs::is_spec_fn(tcx, def_id.to_def_id()) {
                    continue;
                }

                let spec = def_spec
                    .get_proc_spec(&def_id.to_def_id())
                    .map(|e| &e.base_spec);
                let is_pure = matches!(spec.map(|s| s.kind), Some(SpecificationItem::Inherent(
                    prusti_interface::specs::typed::ProcedureSpecificationKind::Pure,
                )));

                let is_trusted = matches!(spec.map(|spec| spec.trusted), Some(SpecificationItem::Inherent(
                    true,
                )));

                if ! (is_trusted && is_pure) {
                    let res = crate::encoders::MirImpureEncoder::encode(def_id.to_def_id());
                    assert!(res.is_ok());
                }

               

                if is_pure 
                {
                    log::debug!("Encoding {def_id:?} as a pure function because it is labeled as pure");
                    let res = crate::encoders::MirFunctionEncoder::encode(def_id.to_def_id());
                    assert!(res.is_ok());
                }

            
                /*
                match res {
                    Ok(res) => println!("ok: {:?}", res),
                    Err(err) => println!("err: {:?}", err),
                }*/
            }
            unsupported_item_kind => {
                println!("another item: {unsupported_item_kind:?}");
            }
        }
    }
    //println!("all items in crate: {:?}", tcx.hir_crate_items(()).definitions().collect::<Vec<_>>());

    fn header(code: &mut String, title: &str) {
        code.push_str("// -----------------------------\n");
        code.push_str(&format!("// {}\n", title));
        code.push_str("// -----------------------------\n");
    }
    let mut viper_code = String::new();

    header(&mut viper_code, "methods");
    for output in crate::encoders::MirImpureEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
    }

    header(&mut viper_code, "functions");
    for output in crate::encoders::MirFunctionEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }

    header(&mut viper_code, "MIR builtins");
    for output in crate::encoders::MirBuiltinEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }

    header(&mut viper_code, "generics");
    for output in crate::encoders::GenericEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.snapshot_param));
        viper_code.push_str(&format!("{:?}\n", output.predicate_param));
        viper_code.push_str(&format!("{:?}\n", output.domain_type));
    }

    header(&mut viper_code, "types");
    for output in crate::encoders::TypeEncoder::all_outputs() {
        for field in output.fields {
            viper_code.push_str(&format!("{:?}", field));
        }
        viper_code.push_str(&format!("{:?}\n", output.snapshot));
        for field_projection in output.field_projection_p {
            viper_code.push_str(&format!("{:?}", field_projection));
        }
        viper_code.push_str(&format!("{:?}\n", output.function_unreachable));
        viper_code.push_str(&format!("{:?}\n", output.function_snap));
        viper_code.push_str(&format!("{:?}\n", output.predicate));
        //viper_code.push_str(&format!("{:?}\n", output.method_refold));
        viper_code.push_str(&format!("{:?}\n", output.method_assign));
        viper_code.push_str(&format!("{:?}\n", output.method_reassign));
    }

    header(&mut viper_code, "utility types");
    for output in crate::encoders::ViperTupleEncoder::all_outputs() {
        if let Some(domain) = output.domain {
            viper_code.push_str(&format!("{:?}\n", domain));
        }
    }

    std::fs::write("local-testing/simple.vpr", viper_code).unwrap();

    vir::with_vcx(|vcx| vcx.alloc(vir::ProgramData {
        fields: &[],
        domains: &[],
        predicates: &[],
        functions: vcx.alloc_slice(&[
            vcx.alloc(vir::FunctionData {
                name: "test_function",
                args: &[],
                ret: &vir::TypeData::Bool,
                pres: &[],
                posts: &[],
                expr: None,
            }),
        ]),
        methods: &[],
    }))
}
