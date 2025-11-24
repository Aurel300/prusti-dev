use prusti_rustc_interface::middle::ty;

use super::GParams;

/// The instantiation of generic arguments, typically found in `TyKind::Adt` and
/// `TyKind::FnDef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GArgs<'tcx> {
    pub(super) context: GParams<'tcx>,
    pub(super) args: &'tcx [ty::GenericArg<'tcx>],
}

pub enum GParamVariant<'vir> {
    Param(ty::ParamTy),
    Alias(
        &'vir str,
        &'vir str,
        Vec<(ty::Ty<'vir>, ty::Ty<'vir>, &'vir str)>,
    ),
}

impl<'tcx> GArgs<'tcx> {
    pub fn new(context: impl Into<GParams<'tcx>>, args: &'tcx [ty::GenericArg<'tcx>]) -> Self {
        GArgs {
            context: context.into(),
            args,
        }
    }

    pub(in crate::encoders::ty) fn context(self) -> GParams<'tcx> {
        self.context
    }

    pub fn args(self) -> &'tcx [ty::GenericArg<'tcx>] {
        self.args
    }

    /// Substitutes type arguments and try to normalize associated types
    pub fn normalize(self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        // Substitute type parameters
        let ty = vir::with_vcx(|vcx| ty::EarlyBinder::bind(ty).instantiate(vcx.tcx(), self.args));
        // Normalize associated types
        self.context.normalize(ty)
    }

    pub fn expect_param<'vir>(self) -> GParamVariant<'vir> {
        assert_eq!(self.args.len(), 1);
        match self.args[0].expect_ty().kind() {
            ty::TyKind::Param(p) => GParamVariant::Param(*p),
            ty::TyKind::Alias(_k, t) => vir::with_vcx(|vcx| {
                let tcx = vcx.tcx();
                let trait_name = vcx.alloc_str(
                    tcx.item_name(tcx.associated_item(t.def_id).container_id(tcx))
                        .as_str(),
                );
                let type_name = vcx.alloc_str(tcx.item_name(t.def_id).as_str());
                let assoc_type_substs = tcx
                    .all_impls(tcx.associated_item(t.def_id).container_id(tcx))
                    .map(|imp| {
                        let imp_type = tcx.type_of(imp).instantiate_identity();
                        let assoc_types = tcx
                            .associated_items(imp)
                            .filter_by_name_unhygienic_and_kind(
                                tcx.item_name(t.def_id),
                                ty::AssocTag::Type,
                            )
                            .collect::<Vec<_>>();
                        assert!(assoc_types.len() == 1);
                        let assoc_type = tcx.type_of(assoc_types[0].def_id).instantiate_identity();
                        let st_name = vcx.alloc_str(
                            tcx.type_of(imp).instantiate_identity().to_string().as_str(),
                        );
                        (imp_type, assoc_type, st_name)
                    })
                    .collect::<Vec<_>>();
                GParamVariant::Alias(trait_name, type_name, assoc_type_substs)
            }),
            other => panic!("expected type parameter, {other:?}"),
        }
    }
}
