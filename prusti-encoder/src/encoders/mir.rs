use prusti_rustc_interface::{middle::ty, span::def_id::DefId};

pub fn get_def_id_and_caller_substs<'tcx>(ty: ty::Ty<'tcx>) -> (DefId, ty::GenericArgsRef<'tcx>) {
    match ty.kind() {
        ty::TyKind::FnDef(def_id, substs) => (*def_id, substs),
        _ => todo!(),
    }
}
