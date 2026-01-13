use task_encoder::EncodeFullError;
use vir::{AdtDestructorData, CastType, FunctionIdn, TYPE_PERM};

use crate::encoders::ty::pure::{AdtBuilder, TyPureBuiltinData, TyPureEnc};

#[derive(Debug, Clone, Copy)]
pub struct TyRealLocal<'vir> {
    pub perm_to_snap: FunctionIdn<'vir, vir::Perm, vir::CSnap>,
    pub snap_to_perm: &'vir AdtDestructorData<'vir, vir::CSnap, vir::Perm>,
}

pub(crate) fn ty_pure<'vir>(
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureBuiltinData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (cons, vec) = builder.constructor("", TYPE_PERM, None);
    Ok(TyPureBuiltinData::TyPureBuiltinReal(TyRealLocal {
        perm_to_snap: cons,
        snap_to_perm: vec.first().unwrap().downcast_ty(),
    }))
}
