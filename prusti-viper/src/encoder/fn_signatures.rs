// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::Encoder;
use rustc_middle::ty;
use rustc_hir::def_id::DefId;

#[derive(Debug)]
pub enum ExtractedFnKind {
    FnDef,
    Closure,
    Param,
}

#[derive(Debug)]
pub struct ExtractedFnSig<'tcx> {
    /// Original function type.
    pub ty: ty::Ty<'tcx>,
    pub kind: ExtractedFnKind,
    /// Argument types.
    pub inputs: Vec<ty::Ty<'tcx>>,
    /// Result type.
    pub output: ty::Ty<'tcx>,
    /// DefId of the function, closure, or GenericParamDef.
    pub def_id: DefId,
    /// Whether the function is pure.
    pub is_pure: bool,
}

impl ExtractedFnSig<'_> {
    pub fn has_self(&self) -> bool {
        match self.kind {
            ExtractedFnKind::Closure
            | ExtractedFnKind::Param => true,
            _ => false
        }
    }
}

/// Extracts the function signature from the given MIR type. The supported type
/// kinds are:
/// - FnDef - regular functions
/// - Closure - arguments are un-tupled but do not include a closure argument
/// - Param - looks up Fn* trait bounds for the given type parameter in the
///     procedure that is currently being encoded (!!!)
pub fn extract_fn_sig<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    original_fn_type: ty::Ty<'tcx>,
) -> ExtractedFnSig<'tcx> {
    // TODO: return an Option or Result?
    let tcx = encoder.env().tcx();
    let kind;
    let mut inputs;
    let output;
    let def_id;
    let mut is_pure = false;
    //let span;
    let fn_type = encoder.resolve_deref_typaram(original_fn_type);
    // TODO: skip_binder is most likely wrong, figure out how to properly
    // use the substs or other information we have to discharge the Binder
    match fn_type.peel_refs().kind() {
        ty::TyKind::FnDef(fn_def_id, _) => {
            kind = ExtractedFnKind::FnDef;
            let fn_sig = tcx.fn_sig(*fn_def_id).skip_binder();
            inputs = fn_sig.inputs().to_vec();
            output = fn_sig.output();
            def_id = *fn_def_id;
            is_pure = encoder.is_pure(def_id);
            //span = tcx.def_span(*def_id);
        }
        ty::TyKind::Closure(cl_def_id, substs) => {
            kind = ExtractedFnKind::Closure;
            let fn_sig = substs.as_closure().sig().skip_binder();
            inputs = vec![original_fn_type.clone()];
            inputs.extend(match fn_sig.inputs()[0].kind() {
                ty::TyKind::Tuple(substs) => substs
                    .iter()
                    .map(|ty| ty.expect_ty())
                    .collect::<Vec<_>>(),
                _ => unreachable!("closure fn_sig arg should be a tuple"),
            });
            output = fn_sig.output();
            def_id = *cl_def_id;
            is_pure = encoder.is_pure(def_id);
            //span = tcx.def_span(*def_id); // TODO: span of assertion?
        }
        ty::TyKind::Param(param) => {
            kind = ExtractedFnKind::Param;
            // TODO: don't rely on state
            let owner = encoder.current_proc.borrow().unwrap();
            let generics = tcx.generics_of(owner);
            let param_def = generics.type_param(param, tcx);
            def_id = param_def.def_id;
            let predicates = tcx.predicates_of(owner);
            let mut inputs_opt = None;
            let mut output_opt = None;
            is_pure = param.name.as_str().starts_with("Ghost");
            for (predicate, _) in predicates.predicates {
                let kind = predicate.kind().skip_binder(); // FIXME: skip_binder
                match kind {
                    ty::PredicateKind::Trait(pred, _) if pred.self_ty() == fn_type
                        && matches!(
                            encoder.env().get_absolute_item_name(pred.def_id()).as_str(),
                            "std::ops::Fn" | "std::ops::FnMut" | "std::ops::FnOnce",
                        )
                    => {
                        if matches!(
                            encoder.env().get_absolute_item_name(pred.def_id()).as_str(),
                            "std::ops::FnMut" | "std::ops::FnOnce",
                        ) {
                            is_pure = false;
                        }
                        // TODO: this makes an assumption about the order
                        // of substitutions of Fn/FnMut
                        assert!(inputs_opt.is_none());
                        inputs_opt = Some(match pred.trait_ref.substs[1].expect_ty().kind() {
                            ty::TyKind::Tuple(substs) => substs
                                .iter()
                                .map(|ty| ty.expect_ty())
                                .collect::<Vec<_>>(),
                            _ => unreachable!(),
                        });
                    }
                    ty::PredicateKind::Projection(pred) if pred.projection_ty.substs[0].expect_ty() == fn_type
                        && (encoder.env().get_absolute_item_name(pred.projection_ty.item_def_id) == "std::ops::Fn::Output"
                            || encoder.env().get_absolute_item_name(pred.projection_ty.item_def_id) == "std::ops::FnMut::Output"
                            || encoder.env().get_absolute_item_name(pred.projection_ty.item_def_id) == "std::ops::FnOnce::Output")
                    => {
                        assert!(output_opt.is_none());
                        output_opt = Some(pred.ty);
                    }
                    _ => {},
                }
            }
            inputs = vec![original_fn_type.clone()];
            inputs.extend(inputs_opt.unwrap());
            output = output_opt.unwrap();
        }
        _ => unreachable!("cannot extract function signature of {}", fn_type),
    }
    ExtractedFnSig {
        ty: original_fn_type,
        kind,
        inputs,
        output,
        def_id,
        is_pure,
    }
}
