use task_encoder::EncodeFullError;

use crate::encoders::ty::{
    RustBuiltin, RustBuiltinData, impure,
    pure::{TyPureBuilder, TyPureBuiltin, TyPureBuiltinData, TyPureEnc},
};

pub(crate) fn ty_pure<'vir>(
    data: &RustBuiltin<'vir>,
    builder: &mut TyPureBuilder<'vir>,
) -> Result<TyPureBuiltin<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    match data {
        // Represented directly by the native Viper `Int`/`Perm` types (see
        // `TyPureBuilder::new`); there is nothing to emit.
        RustBuiltinData::Int => Ok(TyPureBuiltinData::Int),
        RustBuiltinData::Real => Ok(TyPureBuiltinData::Real),
        RustBuiltinData::Ghost => {
            let builder = builder.set_adt_builder();
            builder.constructor::<()>("", (), None);
            Ok(TyPureBuiltinData::Ghost)
        }
    }
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustBuiltin<'vir>, &TyPureBuiltin<'vir>),
    _deps: &mut task_encoder::TaskEncoderDependencies<'vir, impure::TyImpureEnc>,
    builder: &mut impure::PredicateBuilder<'vir>,
) -> Result<impure::TyImpureBuiltin<'vir>, EncodeFullError<'vir, impure::TyImpureEnc>> {
    match data.0 {
        RustBuiltinData::Int | RustBuiltinData::Real => {
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
        RustBuiltinData::Ghost => {
            super::opaque::set_opaque(builder);
            Ok(())
        }
    }
}
