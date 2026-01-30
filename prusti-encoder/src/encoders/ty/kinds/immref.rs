use crate::encoders::{TyUsePureEnc, ty::{
    RustImmRef, RustTyDecomposition, generics::GParams, impure::{PredicateBuilder, TyImpureEnc, TyImpureImmRef, TyImpureImmRefData}, pure::{AdtBuilder, TyPureEnc, TyPureImmRef, TyPureImmRefData}
}};
use prusti_rustc_interface::{middle::ty, span::Symbol};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    _data: &RustImmRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureImmRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let dummy_param = builder
        .vcx
        .tcx()
        .mk_ty_from_kind(ty::TyKind::Param(ty::ParamTy::new(0, Symbol::intern("T"))));
    let ty_task_param = RustTyDecomposition::from_ty(
        dummy_param,
        builder.vcx.tcx(),
        GParams::new(
            builder.vcx.tcx().mk_args(&[dummy_param.into()]),
            ty::ParamEnv::empty(),
            false,
        ),
    );
    deps.require_ref::<TyUsePureEnc>(ty_task_param)?;

    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, vir::TYPE_PSNAP), None);

    Ok(TyPureImmRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        value_access: field_access[1].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustImmRef<'vir>, &TyPureImmRef<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureImmRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    builder.mk_predicate(
        "",
        Some(vir::expr! {
            acc((ref_self).[ref_field])
            // TODO: pure typeof assertions do not currently work
            // && (([generic_typeof]([data.1.value_access]([ref_field](ref_self)))) == ([builder.params.ty_exprs()[0]]))
        }), // TODO: use generic args?
    );

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [ref_field](ref_self) }));

    Ok(TyImpureImmRefData {})
}
