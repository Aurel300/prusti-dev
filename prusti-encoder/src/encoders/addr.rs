use task_encoder::TaskEncoder;
use vir::{Function, FunctionIdn, ViperIdent};

pub struct AddrUseEnc;

#[derive(Debug, Clone)]
pub struct AddrUse<'vir> {
    pub ref_from_addr: vir::FunctionIdn<'vir, vir::Int, vir::Ref>,
}

#[derive(Debug, Clone)]
pub struct AddrLocal<'vir> {
    pub ref_from_addr: Function<'vir>,
}

impl TaskEncoder for AddrUseEnc {
    task_encoder::encoder_cache!(AddrUseEnc);
    type TaskDescription<'vir> = ();
    type OutputFullLocal<'vir> = AddrLocal<'vir>;
    type OutputFullDependency<'vir> = AddrUse<'vir>;

    type TaskKey<'vir> = Self::TaskDescription<'vir>;

    fn task_to_key<'vir>(_task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {}

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let ref_from_addr = FunctionIdn::new(
            ViperIdent::new("ref_from_addr"),
            vir::TYPE_INT,
            vir::TYPE_REF,
        );
        deps.emit_output_ref(*task_key, ())?;
        Ok((
            AddrLocal {
                ref_from_addr: vir::with_vcx(|vcx| {
                    let arg_decl = vcx.mk_local_decl("arg", vir::TYPE_INT);
                    vcx.mk_function(ref_from_addr, (arg_decl,), &[], &[], None, None)
                }),
            },
            AddrUse { ref_from_addr },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = AddrUseEnc::all_outputs_local_no_errors();
        for output in outputs {
            program.add_function(output.ref_from_addr);
        }
    }
}
