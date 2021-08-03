use crate::encoder::{Encoder, borrows::ProcedureContract};
use crate::encoder::errors::{SpannedEncodingResult, ErrorCtxt, WithSpan};
use crate::encoder::borrows::compute_procedure_contract;
use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
use prusti_interface::{
    environment::{
        Procedure,
        Environment
    },
    data::ProcedureDefId,
    specs::typed,
};
use prusti_common::vir;
use prusti_common::vir::ExprIterator;
use rustc_middle::{ty, mir};
use rustc_span::Span;
use log::{debug, trace};
use rustc_hir as hir;

pub enum SpecFunctionKind {
    Pre,
    Post,
    HistInv
}

pub struct SpecFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    procedure: &'p Procedure<'p, 'tcx>,
    span: Span,
    proc_def_id: ProcedureDefId,
    is_closure: bool,
    mir: &'p mir::Body<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SpecFunctionEncoder<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        procedure: &'p Procedure<'p, 'tcx>,
    ) -> Self {
        let proc_def_id = procedure.get_id();
        Self {
            encoder: encoder,
            procedure: procedure,
            span: procedure.get_span(),
            proc_def_id,
            is_closure: encoder.env().tcx().is_closure(proc_def_id),
            mir: procedure.get_mir(),
            mir_encoder: MirEncoder::new(encoder, procedure.get_mir(), proc_def_id),
        }
    }

    pub fn encode(&self) -> SpannedEncodingResult<Vec<vir::Function>> {
        let specs = if let Some(specs) = self.encoder.get_procedure_specs(self.proc_def_id) {
            specs
        } else {
            return Ok(vec![]);
        };

        let contract = compute_procedure_contract(
            self.proc_def_id,
            self.encoder.env().tcx(),
            typed::SpecificationSet::Procedure(specs),
            Some(&self.encoder.current_tymap())
        ).with_span(self.span)?.to_def_site_contract();

        let pre_func = self.encode_pre_spec_func(&contract)?;
        let post_func = self.encode_post_spec_func(&contract)?;
        // let invariant_func = self.encode_invariant_func(&contract)?;

        Ok(vec![]) // Ok(vec![pre_func, post_func, invariant_func])
    }

    fn encode_pre_spec_func(&self, contract: &ProcedureContract<'tcx>)
        -> SpannedEncodingResult<vir::Function> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect::<Result<Vec<_>, _>>()?;

        for item in contract.functional_precondition() {
            func_spec.push(self.encoder.encode_assertion(
                &item,
                &self.mir,
                None,
                &encoded_args
                    .iter()
                    .map(|e| -> vir::Expr { e.into() }).collect::<Vec<_>>(),
                None,
                true,
                None,
                ErrorCtxt::GenericExpression,
                self.proc_def_id,
            )?);
        }

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.proc_def_id,
                                                     SpecFunctionKind::Pre),
            formal_args: encoded_args,
            return_type: vir::Type::Bool,
        })
    }

    fn encode_post_spec_func(&self, contract: &ProcedureContract<'tcx>)
        -> SpannedEncodingResult<vir::Function> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect::<Result<Vec<_>, _>>()?;
        let encoded_return = self.encode_local(contract.returned_value.clone().into())?;
        // encoded_args:
        // _1    - closure "self"
        // _2... - additional arguments
        // encoded return: _0

        for item in contract.functional_postcondition() {
            func_spec.push(self.encoder.encode_assertion(
                &item,
                &self.mir,
                None,
                &encoded_args
                    .iter()
                    .map(|e| -> vir::Expr { e.into() }).collect::<Vec<_>>(),
                Some(&encoded_return.clone().into()),
                true,
                None,
                ErrorCtxt::GenericExpression,
                self.proc_def_id,
            )?);
        }

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.proc_def_id,
                                                     SpecFunctionKind::Post),
            formal_args: encoded_args.into_iter()
                                     .chain(std::iter::once(encoded_return))
                                     .collect(),
            return_type: vir::Type::Bool,
        })
    }
    /*
    fn encode_invariant_func(&self, contract: &ProcedureContract<'tcx>)
        -> SpannedEncodingResult<vir::Function> {

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.proc_def_id,
                                                     SpecFunctionKind::HistInv),
            formal_args: vec![],
            return_type: vir::Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(func_spec.into_iter()
                                .map(|post| SnapshotSpecPatcher::new(self.encoder).patch_spec(post))
                                .collect::<Result<Vec<vir::Expr>, _>>()
                                .with_span(self.span)?
                                .into_iter()
                                .conjoin()),
        })
    }
*/
    fn encode_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let var_name = self.mir_encoder.encode_local_var_name(local);
        let var_type = self
            .encoder
            .encode_snapshot_type(self.mir_encoder.get_local_ty(local))
            .with_span(self.span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
    }
}
