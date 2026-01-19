use std::collections::HashMap;

use prusti_rustc_interface::{middle::ty::AssocKind, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, vir_format_identifier};

use crate::encoders::ty::generics::{GParams, GenericParamsEnc};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitData<'vir> {
    pub trait_name: &'vir str,
    pub type_did_fun_mapping: HashMap<DefId, FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>>,
    pub impl_fun: FunctionIdn<'vir, vir::ManyTyVal, vir::Bool>,
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
            let params = deps.require_dep::<GenericParamsEnc>(GParams::from(*task_key))?;
            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());
            let mut funcs = Vec::new();
            let mut type_did_fun_mapping = HashMap::new();
            for item in tcx.associated_items(task_key).in_definition_order() {
                match item.kind {
                    AssocKind::Type { .. } => {
                        let params_type = deps
                            .require_dep::<GenericParamsEnc>(GParams::from(item.def_id))
                            .unwrap();
                        let type_func = FunctionIdn::new(
                            vir_format_identifier!(
                                vcx,
                                "{}_assoc_type_{}",
                                trait_name,
                                tcx.item_name(item.def_id),
                            ),
                            vcx.alloc_slice(&vec![vir::TYPE_TYVAL; params_type.ty_exprs().len()]), // params_type also includes parameters of trait itself
                            vir::TYPE_TYVAL,
                        );
                        type_did_fun_mapping.insert(item.def_id, type_func);
                        funcs.push(vcx.mk_domain_function(type_func, false, None));
                    }
                    AssocKind::Fn { ../*name, has_self*/ } => (), // TODO
                    AssocKind::Const { .. } => (), // noop?
                }
            }

            let impl_fun = FunctionIdn::new(
                vir_format_identifier!(vcx, "{}_impl", trait_name),
                vcx.alloc_slice(&(vec![vir::TYPE_TYVAL; params.ty_exprs().len()])),
                vir::TYPE_BOOL,
            );
            funcs.push(vcx.mk_domain_function(impl_fun, false, None));

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{}", trait_name),
                &[],
                &[],
                vcx.alloc_slice(&funcs),
                None,
            );

            Ok((
                trait_domain,
                TraitData {
                    trait_name,
                    type_did_fun_mapping,
                    impl_fun,
                },
            ))
        })
    }
}
