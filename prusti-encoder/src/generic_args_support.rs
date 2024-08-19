use std::collections::HashSet;

use prusti_rustc_interface::middle::ty::{
    self, GenericArgs, ParamTy, Ty, TyKind, TypeSuperVisitable, TypeVisitable, TypeVisitor,
};
use std::ops::ControlFlow;

/// Extracts all unique `ParamTy`s from the provided `GenericArgs` in the order
/// they appear. For example, if the input was `[Option<T, U>, T]`, the output
/// would be `[T, U]`.
pub fn get_unique_param_tys_in_order<'tcx>(
    generic_args: &'tcx GenericArgs<'tcx>,
) -> impl Iterator<Item = ParamTy> + 'tcx {
    unique(
        generic_args
            .iter()
            .filter_map(|arg| arg.as_type())
            .flat_map(extract_ty_params),
    )
}

pub fn extract_ty_params(ty: Ty<'_>) -> Vec<ParamTy> {
    struct TyParamCollector {
        ty_params: Vec<ty::ParamTy>,
    }

    impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for TyParamCollector {
        fn visit_ty(&mut self, ty: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
            if let TyKind::Param(p) = ty.kind() {
                self.ty_params.push(*p);
            }
            ty.super_visit_with(self)
        }

        type BreakTy = !;
    }
    let mut collector = TyParamCollector { ty_params: vec![] };
    ty.visit_with(&mut collector);
    collector.ty_params
}

pub fn unique(iter: impl IntoIterator<Item = ParamTy>) -> impl Iterator<Item = ParamTy> {
    let mut seen = HashSet::new();
    iter.into_iter().filter(move |item| seen.insert(*item))
}
