use task_encoder::TaskEncoder;
use vir::{
    BackendInterpretationPair, CastType, DomainGenData, DomainIdnCSnap, FunctionIdn, ViperIdent,
};

#[derive(Eq, PartialEq, Hash, Debug, Clone, Copy)]
pub enum BitVecSize {
    BitVec8,
    BitVec16,
    BitVec32,
    BitVec64,
    BitVec128,
}

impl BitVecSize {
    pub fn from_bits(bits: u32) -> Self {
        match bits {
            8 => BitVecSize::BitVec8,
            16 => BitVecSize::BitVec16,
            32 => BitVecSize::BitVec32,
            64 => BitVecSize::BitVec64,
            128 => BitVecSize::BitVec128,
            _ => unreachable!("unsupported bitvector width {bits}"),
        }
    }

    pub fn to_bits(self) -> u32 {
        match self {
            BitVecSize::BitVec8 => 8,
            BitVecSize::BitVec16 => 16,
            BitVecSize::BitVec32 => 32,
            BitVecSize::BitVec64 => 64,
            BitVecSize::BitVec128 => 128,
        }
    }

    pub fn domain_name(&self) -> &'static str {
        match *self {
            BitVecSize::BitVec8 => "s_BitVec_8",
            BitVecSize::BitVec16 => "s_BitVec_16",
            BitVecSize::BitVec32 => "s_BitVec_32",
            BitVecSize::BitVec64 => "s_BitVec_64",
            BitVecSize::BitVec128 => "s_BitVec_128",
        }
    }

    pub fn int_to_bv_interpretation(&self) -> &'static str {
        match *self {
            BitVecSize::BitVec8 => "(_ int2bv 8)",
            BitVecSize::BitVec16 => "(_ int2bv 16)",
            BitVecSize::BitVec32 => "(_ int2bv 32)",
            BitVecSize::BitVec64 => "(_ int2bv 64)",
            BitVecSize::BitVec128 => "(_ int2bv 128)",
        }
    }

    pub fn interpretation(&self) -> (&'static str, &'static str) {
        match *self {
            BitVecSize::BitVec8 => ("(_ BitVec 8)", "bv8"),
            BitVecSize::BitVec16 => ("(_ BitVec 16)", "bv16"),
            BitVecSize::BitVec32 => ("(_ BitVec 32)", "bv32"),
            BitVecSize::BitVec64 => ("(_ BitVec 64)", "bv64"),
            BitVecSize::BitVec128 => ("(_ BitVec 128)", "bv128"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BitVecDomain<'vir> {
    pub domain: vir::DomainIdn<'vir, vir::CSnap>,
    pub from_int: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    pub sbv_to_int: FunctionIdn<'vir, vir::CSnap, vir::Int>,
    pub ubv_to_int: FunctionIdn<'vir, vir::CSnap, vir::Int>,
}

pub struct BitVecEnc;

impl TaskEncoder for BitVecEnc {
    task_encoder::encoder_cache!(BitVecEnc);
    const ENCODER_NAME: &'static str = "bitvec encoder";

    type TaskDescription<'vir> = BitVecSize;

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = BitVecDomain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let domain_name = task_key.domain_name();

            let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(domain_name), 0);

            let self_type = domain_ident();

            let from_int_name = vir::vir_format!(vcx, "{}_from_int", domain_name);

            let from_int = FunctionIdn::new(
                ViperIdent::new(from_int_name),
                vir::TYPE_INT.upcast_ty(),
                self_type,
            );

            let from_int_data =
                vcx.mk_domain_function(from_int, false, Some(task_key.int_to_bv_interpretation()));

            let sbv_to_int_name = vir::vir_format!(vcx, "{}_sbv_to_int", domain_name);

            let sbv_to_int =
                FunctionIdn::new(ViperIdent::new(sbv_to_int_name), self_type, vir::TYPE_INT);

            let sbv_to_int_data = vcx.mk_domain_function(sbv_to_int, false, Some("sbv_to_int"));

            let ubv_to_int_name = vir::vir_format!(vcx, "{}_ubv_to_int", domain_name);

            let ubv_to_int =
                FunctionIdn::new(ViperIdent::new(ubv_to_int_name), self_type, vir::TYPE_INT);

            let ubv_to_int_data = vcx.mk_domain_function(ubv_to_int, false, Some("bv2nat"));

            let functions = &[from_int_data, sbv_to_int_data, ubv_to_int_data];

            let (smtlib_interpretation, boogie_interpretation) = task_key.interpretation();

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident.name(),
                &[],
                &[],
                vcx.alloc_slice(functions),
                Some(vcx.alloc_slice(&[
                    vcx.alloc(BackendInterpretationPair {
                        key: "SMTLIB",
                        value: smtlib_interpretation,
                    }),
                    vcx.alloc(BackendInterpretationPair {
                        key: ("Boogie"),
                        value: boogie_interpretation,
                    }),
                ])),
            );

            deps.emit_output_ref(*task_key, ())?;
            Ok((
                domain_data,
                BitVecDomain {
                    domain: domain_ident,
                    from_int,
                    sbv_to_int,
                    ubv_to_int,
                },
            ))
        })
    }
}
