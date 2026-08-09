use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, HasType};

use crate::encoders::{TyUseImpureEnc, TyUsePureEnc, ty::{RustTyDatas, RustUnique, data::TyData, impure::{PredicateBuilder, TyImpureEnc, TyImpureUnique, TyImpureUniqueData}, pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureUnique, TyPureUniqueData}}};

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &RustUnique<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureUnique<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data.metadata.decompose(task_key.params);
    let metadata = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let ty = data.referent.decompose(task_key.params);
    let referent = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, metadata, referent), None);

    Ok(TyPureUniqueData {
        prim_to_snap: field_snaps_to_snap,
        address_access: field_access[0].downcast_ty(),
        metadata_access: field_access[1].downcast_ty(),
        value_access: field_access[2].downcast_ty(),
    })
}


pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &(&RustUnique<'vir>, &TyPureUnique<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureUnique<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();

    let metadata_type = data.0.metadata.decompose(task_key.0.params);
    let metadata_impure = deps.require_dep::<TyUseImpureEnc>(metadata_type)?;
    let inner_type = data.0.referent.decompose(task_key.0.params);
    let inner_impure = deps.require_dep::<TyUseImpureEnc>(inner_type)?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let metadata_field = builder.field("metadata", metadata_impure.snapshot().ty());
    let value_field = builder.field("value", inner_impure.snapshot().ty());

    // functions
    let addr_fun: FunctionIdn<'vir, vir::Ref, vir::Ref> = builder.function("address", ref_self_decl.ty, vir::TYPE_REF, (ref_self_decl,), &[],
        &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
        None);

    let addr_predicate = builder.vcx.mk_predicate_app_expr(
        inner_impure.ref_to_pred_app((addr_fun)(ref_self), None)
    );

    // main predicate
    builder.mk_predicate(
        "",
        Some(vir::expr! {
           ([addr_predicate]) && ((acc((ref_self).[metadata_field])) && (acc((ref_self).[value_field])))
        }),
    );

    let cons = (data.1.prim_to_snap)((addr_fun)(ref_self), builder.vcx.mk_field_expr(ref_self, metadata_field.downcast_ty()), builder.vcx.mk_field_expr(ref_self, value_field.downcast_ty()));

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [cons] }));

    Ok(TyImpureUniqueData {})
}