use crate::encoders::ty::{
    impure::{ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureParam}, pure::{DomainBuilder, PureTyDatas, TyPureEnc, TyPureParam}, RustTyDatas, RustTyParam
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};

pub(crate) fn ty_pure<'vir>(
    _data: &RustTyParam<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureParam<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    Ok(())
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustTyParam<'vir>, &TyPureParam<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureParam<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    super::opaque::set_opaque(builder);
    Ok(())
}
