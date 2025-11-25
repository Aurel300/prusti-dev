use crate::encoders::{
    TyUseImpureEnc,
    ty::{
        RustTyDatas,
        data::{StructData, TyData},
        generics::{GParams, trait_impls::TraitImplEnc},
        impure::{ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureFieldData},
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureFieldData, TyPureStructData},
        use_pure::TyUsePureEnc,
    },
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType, PredicateIdn};

use prusti_rustc_interface::span::def_id::DefId;

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<StructData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    ty_pure_variant("", None, task_key, data, deps, builder)
}

pub(super) fn generate_axioms_for_impls<'vir, E: TaskEncoder + 'vir + ?Sized>(
    did: DefId,
    deps: &mut TaskEncoderDependencies<'vir, E>,
) -> Result<(), EncodeFullError<'vir, E>> {
    vir::with_vcx(|vcx| {
        let tcx = vcx.tcx();
        for trait_id in tcx.visible_traits() {
            for impl_id in tcx.all_impls(trait_id) {
                if tcx.type_of(impl_id).instantiate_identity()
                    == tcx.type_of(did).instantiate_identity()
                {
                    deps.require_dep::<TraitImplEnc>((impl_id, GParams::empty()))?;
                }
            }
        }
        Ok(())
    })
}

pub(super) fn ty_pure_variant<'vir>(
    prefix: &str,
    discr: Option<vir::ExprCSnap<'vir>>,
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<StructData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    if let Some(d) = data.did {
        generate_axioms_for_impls(d, deps)?;
    }
    let field_tys = data
        .fields
        .iter()
        .map(|f| {
            let ty = f.decompose(task_key.params);
            Ok(deps.require_ref::<TyUsePureEnc>(ty)?.snapshot)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let field_tys = builder.vcx.alloc_slice(&field_tys);
    let (field_snaps_to_snap, des) = builder.constructor(prefix, field_tys, discr);
    assert_eq!(des.len(), data.fields.len());
    let des = des
        .iter()
        .map(|read| TyPureFieldData {
            read: read.downcast_ty(),
        })
        .collect::<Vec<_>>();
    Ok(StructData::new(
        TyPureStructData {
            field_snaps_to_snap,
        },
        data.inhabited,
        des,
        data.did,
    ))
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<StructData<'vir, ImpureTyDatas>, EncodeFullError<'vir, TyImpureEnc>> {
    let (data, self_pred, snap_expr) = ty_impure_variant("", task_key, data, deps, builder)?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
                "snap",
                (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
                builder.csnap_type(),
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
                &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
                &[],
                Some(snap_expr),
            )
            .1,
    );
    Ok(data)
}

pub(super) type ImpureVariant<'vir> = (
    StructData<'vir, ImpureTyDatas>,
    PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    vir::ExprCSnap<'vir>,
);

pub(crate) fn ty_impure_variant<'vir>(
    prefix: &str,
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<ImpureVariant<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    if let Some(d) = data.did {
        generate_axioms_for_impls(d, deps)?;
    }
    let fields = data
        .fields
        .iter()
        .map(|f| {
            let ty = f.0.decompose(task_key.0.params);
            deps.require_dep::<TyUseImpureEnc>(ty)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // Ref-to-Ref function for every field
    let field_accessors = fields
        .iter()
        .enumerate()
        .map(|(idx, _field)| {
            let ref_to_field_ref = builder
                .inner
                .function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>(
                    &format!("{prefix}field_{idx}"),
                    (
                        ref_self_decl.ty(),
                        builder.params.ty_args(),
                        builder.params.const_args(),
                    ),
                    vir::TYPE_REF,
                    (
                        ref_self_decl,
                        builder.params.ty_decls(),
                        builder.params.const_decls(),
                    ),
                    &[], // TODO: should have a read permission here!
                    &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
                    None,
                );
            TyImpureFieldData { ref_to_field_ref }
        })
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_owned = builder
        .inner
        .predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            &pred_name,
            (
                ref_self_decl.ty(),
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            (
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            Some(
                builder.vcx.mk_conj(
                    &fields
                        .iter()
                        .zip(&field_accessors)
                        .map(|(field, accessor)| {
                            let TyImpureFieldData { ref_to_field_ref } = accessor;
                            field.ref_to_pred(
                                builder.vcx,
                                ref_to_field_ref(
                                    ref_self,
                                    builder.params.ty_exprs(),
                                    builder.params.const_exprs(),
                                ),
                                None,
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
            ),
        );

    // Ref-to-snap
    let snap_args: Vec<&'vir vir::ExprGenData<'vir, (), !, vir::Snap>> = fields
        .iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| {
            let TyImpureFieldData { ref_to_field_ref } = accessor;
            field.ref_to_snap(ref_to_field_ref(
                ref_self,
                builder.params.ty_exprs(),
                builder.params.const_exprs(),
            ))
        })
        .collect::<Vec<_>>();
    let variant_snap_expr = vir::expr! {
        unfolding ([pred_owned](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([data.1.field_snaps_to_snap](..[snap_args.as_slice()]))
    };

    Ok((
        StructData::new((), data.inhabited, field_accessors, data.did),
        pred_owned,
        variant_snap_expr,
    ))
}
