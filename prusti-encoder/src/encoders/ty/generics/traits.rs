use prusti_rustc_interface::{middle::ty::AssocKind, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, ViperIdent};

pub struct TraitEnc;

#[derive(Debug, Clone, Copy)]
pub struct TraitData<'vir> {
    pub trait_name: &'vir str,
    pub type_did_fun_mapping: &'vir [(DefId, FunctionIdn<'vir, vir::TyVal, vir::TyVal>)],
}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputFullDependency<'vir> = TraitData<'vir>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for dom in TraitEnc::all_outputs_local_no_errors() {
            program.add_domain(dom);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());
            let type_did_fun_mapping = tcx.associated_items(task_key).in_definition_order().filter(|item| matches!(item.kind, AssocKind::Type{data: _})).map(|item| (item.def_id, FunctionIdn::new(
                ViperIdent::new(
                    vcx.alloc_str(&format!("{}_Assoc_{}_func", trait_name, tcx.item_name(item.def_id))),
                ),
                vir::TYPE_TYVAL,
                vir::TYPE_TYVAL,
            ))).collect::<Vec<_>>();
            let assoc_funs = type_did_fun_mapping
                .iter()
                .map(|(_, function_idn)| vcx.mk_domain_function(*function_idn, false, None))
                .collect::<Vec<_>>();
            let trait_domain = vcx.mk_domain(
                ViperIdent::new(vcx.alloc_str(&format!("t_{}", trait_name))),
                &[],
                &[],
                vcx.alloc_slice(assoc_funs.as_slice()),
                None,
            );
            Ok((
                trait_domain,
                TraitData {
                    trait_name,
                    type_did_fun_mapping: vcx.alloc_slice(type_did_fun_mapping.as_slice()),
                },
            ))
        })
    }
}
