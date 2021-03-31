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
    env: &'v Environment<'tcx>,
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
            env: encoder.env(),
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

        let closure_snapshot = if self.is_closure {
            Some(self.encoder
                .encode_snapshot_type(self.mir.local_decls[1usize.into()].ty)
                .with_span(self.span)?)
        } else {
            None
        };

        let pre_func = self.encode_pre_spec_func(&contract, closure_snapshot.clone())?;
        let post_func = self.encode_post_spec_func(&contract, closure_snapshot.clone())?;
        // let invariant_func = self.encode_invariant_func(&contract)?;

        Ok(vec![pre_func, post_func] // , invariant_func]
            .into_iter()
            .map(|func| self.encoder.patch_snapshots_function(func))
            .collect::<Result<_, _>>()
            .with_span(self.span)?)
    }

    fn encode_pre_spec_func(
        &self,
        contract: &ProcedureContract<'tcx>,
        closure_snapshot: Option<vir::Type>,
    ) -> SpannedEncodingResult<vir::Function> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let mut encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect::<Result<Vec<_>, _>>()?;

        if self.is_closure {
            encoded_args[0] = vir::LocalVar::new(
                encoded_args[0].name.to_string(),
                closure_snapshot.unwrap(),
            );
        }

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
            )?);
        }

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.proc_def_id,
                                                     SpecFunctionKind::Pre),
            formal_args: encoded_args,
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(func_spec.into_iter().conjoin()), // TODO: patch snapshots
        })
    }

    fn encode_post_spec_func(
        &self,
        contract: &ProcedureContract<'tcx>,
        closure_snapshot: Option<vir::Type>,
    ) -> SpannedEncodingResult<vir::Function> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let mut encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect::<Result<Vec<_>, _>>()?;

        if self.is_closure {
            let original_arg = encoded_args[0].clone();
            encoded_args[0] = vir::LocalVar::new(
                original_arg.name.to_string(),
                closure_snapshot.clone().unwrap(),
            );
            encoded_args.push(vir::LocalVar::new(
                format!("{}_old", original_arg.name),
                closure_snapshot.unwrap(),
            ));
        }

        // TODO: (after CAV) snapshot and duplicate any mutable argument

        let encoded_return = self.encode_local(contract.returned_value.clone().into())?;
        // encoded_args:
        // _1    - closure "self"
        // _2... - additional arguments
        // encoded return: _0

        for item in contract.functional_postcondition() {
            let mut encoded_item = self.encoder.encode_assertion(
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
            )?;
            encoded_item = self.patch_old_access(
                encoded_item,
                &encoded_args[0],
                &encoded_args[encoded_args.len() - 1],
            );
            func_spec.push(encoded_item);
        }

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.proc_def_id,
                                                     SpecFunctionKind::Post),
            formal_args: encoded_args.into_iter()
                                     .chain(std::iter::once(encoded_return))
                                     .collect(),
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(func_spec.into_iter().conjoin()), // TODO: patch snapshots
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
    fn patch_old_access(&self, expr: vir::Expr, local_post: &vir::LocalVar, local_pre: &vir::LocalVar) -> vir::Expr {
        if self.is_closure {
            // TODO: do replacement for all fields
            return expr.replace_place(
                &vir::Expr::labelled_old(
                    "",
                    vir::Expr::field(
                        vir::Expr::field(
                            vir::Expr::field(
                                vir::Expr::local(local_post.clone()),
                                vir::Field::new(
                                    "f$count",
                                    vir::Type::TypedRef("i32".to_string()),
                                ),
                            ),
                            vir::Field::new(
                                "val_ref",
                                vir::Type::TypedRef("i32".to_string()),
                            ),
                        ),
                        vir::Field::new(
                            "val_int",
                            vir::Type::Int,
                        ),
                    )
                ),
                &vir::Expr::field(
                    vir::Expr::field(
                        vir::Expr::field(
                            vir::Expr::local(local_pre.clone()),
                            vir::Field::new(
                                "f$count",
                                vir::Type::TypedRef("i32".to_string()),
                            ),
                        ),
                        vir::Field::new(
                            "val_ref",
                            vir::Type::TypedRef("i32".to_string()),
                        ),
                    ),
                    vir::Field::new(
                        "val_int",
                        vir::Type::Int,
                    ),
                ),
            );
        }
        return expr;
    }

    fn encode_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let var_name = self.mir_encoder.encode_local_var_name(local);
        let var_type = self
            .encoder
            .encode_value_or_ref_type(self.mir_encoder.get_local_ty(local))
            .with_span(self.span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
    }
}
