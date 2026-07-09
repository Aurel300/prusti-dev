use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, TYPE_INT};

use crate::encoders::ty::{
    impure::{PredicateBuilder, TyImpureBuiltin, TyImpureEnc},
    pure::{AdtBuilder, TyPureBuiltinData, TyPureEnc},
};

use super::TyPrimLocal;

pub(crate) fn ty_pure<'vir>(
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureBuiltinData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (cons, vec) = builder.constructor("", TYPE_INT, None);
    Ok(TyPureBuiltinData::TyPureBuiltinInt(TyPrimLocal {
        prim_to_snap: cons,
        snap_to_prim: vec.first().unwrap().downcast_ty(),
    }))
}

pub(crate) fn ty_impure<'vir>(
    _data: (),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureBuiltin<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let prim_field = builder.field("val", snap_type);

    // main predicate
    builder.mk_predicate("", Some(vir::expr! { acc((ref_self).[prim_field]) }));

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [prim_field](ref_self) }));

    Ok(())
}
