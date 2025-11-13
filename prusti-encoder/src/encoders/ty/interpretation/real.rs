use task_encoder::EncodeFullError;
use vir::{
    BackendInterpretationPair, FunctionIdn, VirCtxt,
};

use crate::encoders::ty::pure::{DomainBuilder, TyPureBuiltinData, TyPureEnc};

#[derive(Debug, Clone, Copy)]
pub struct TyRealLocal<'vir> {
    // pub domain: vir::DomainIdn<'vir, vir::CSnap>,
    pub real_mul: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
}

pub(crate) fn ty_pure<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureBuiltinData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    builder.set_interpretation(vcx.alloc_slice(&[vcx.alloc(BackendInterpretationPair {
        key: "SMTLIB",
        value: "(Real)",
    })]));
    let real_mul = builder.backend_func(
        "mul",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("*"),
    );
    Ok(TyPureBuiltinData::TyPureBuiltinReal(TyRealLocal {
        real_mul,
    }))
}

// struct RealDomainBuilder<'vir> {
//     vcx: &'vir VirCtxt<'vir>,
//     domain_name: &'vir str,
//     functions: Vec<&'vir DomainFunctionData<'vir>>
// }

// impl<'vir> RealDomainBuilder<'vir> {
//     fn function<A: Arity, T: CompType> (&mut self, function_name: &'vir str, args: A::Tys<'vir>,
//         ret: Type<'vir, T>, interpretation: &'vir str) -> FunctionIdn<'vir, A, T>{
//         let func_name = vir::vir_format!(self.vcx, "{}_{}", self.domain_name, function_name);
//         let func = FunctionIdn::new(
//             ViperIdent::new(func_name),
//                 args,
//                 ret
//         );

//         self.functions.push(self.vcx.mk_domain_function::<A>(
//             func,
//             false,
//             Some(interpretation)
//         ));

//         func
//     }
// }

// pub struct RealEnc;
// impl TaskEncoder for RealEnc {
//     task_encoder::encoder_cache!(RealEnc);

//     type TaskDescription<'vir> = ();

//     type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

//     type OutputFullDependency<'vir> = TyRealLocal<'vir>;

//     type EncodingError = ();

//     fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
//         *task
//     }

//     fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
//         for output in RealEnc::all_outputs_local_no_errors() {
//             program.add_domain(output);
//         }
//     }

//     fn do_encode_full<'vir>(
//         task_key: &Self::TaskKey<'vir>,
//         deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
//     ) -> task_encoder::EncodeFullResult<'vir, Self> {
//         vir::with_vcx(|vcx| {
//             let domain_name = "s_Real";

//             let mut builder = RealDomainBuilder {
//                 vcx,
//                 domain_name,
//                 functions: Vec::new()
//             };

//             let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(domain_name));

//             let self_type = domain_ident();

//             let real_mul: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap> = builder.function("mul", (self_type, self_type), self_type, "*");

//             let domain_data = vcx.mk_domain::<(), !>(
//                 domain_ident.name(),
//                 &[],
//                 &[],
//                 vcx.alloc_slice(builder.functions.as_slice()),
//                 Some("(Real)")
//             );

//             deps.emit_output_ref(*task_key, ())?;
//             Ok((
//                 domain_data,
//                 TyRealLocal {
//                     domain: domain_ident,
//                     real_mul
//                 },
//             ))
//         })
//     }
// }
