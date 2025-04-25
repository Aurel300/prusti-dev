use crate::encoders::{
    domain::{DomainBuilder, DomainDataPrim, DomainEnc, DomainEncOutputRef, DomainEncSpecifics}, predicate::{PredicateBuilder, PredicateEncData}, rust_ty_snapshots::RustTySnapshotsEnc, snapshot::SnapshotEncOutput, PredicateEnc
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::ToKnownArity;

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Array(elem_ty, _) = ty_kind else { unreachable!() };
    let elem_ty_enc = deps.require_ref::<RustTySnapshotsEnc>(*elem_ty)?;
    let prim_type = builder.vcx.mk_ty_seq(elem_ty_enc.generic_snapshot.snapshot);

    let value_ident = builder.function("value", &[builder.self_type()], prim_type);
    let cons_ident = builder.function("cons", &[prim_type], builder.self_type());

    builder.axiom("cons", vir::expr! {
        forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
    });
    builder.axiom("value", vir::expr! {
        forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
    });

    Ok(DomainEncSpecifics::Primitive(DomainDataPrim {
        prim_type,
        snap_to_prim: value_ident.to_known(),
        prim_to_snap: cons_ident.to_known(),
    }))
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDecl<'vir>],
    generic_exprs: &[vir::Expr<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        PredicateEncData<'vir>,
        Option<vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>>,
    ),
    EncodeFullError<'vir, PredicateEnc>,
> {
    // let ty = task_key.ty();
    // let ty_kind = ty.kind();

    let snap_type = snap.snapshot;

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    // fields
    // let prim_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        None, // Some(vir::expr! { acc_field([prim_field](ref_self)) }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function(
                "snap",
                &[ref_self_decl]
                    .into_iter()
                    .chain(generic_decls.iter().cloned())
                    .collect::<Vec<_>>(),
                snap_type,
                &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
                &[],
                None,
                // Some(vir::expr! {
                //     unfolding_wildcard ([self_pred](ref_self)) in ([prim_field](ref_self))
                // }),
            )
            .1,
    );

    Ok((
        PredicateEncData::Primitive(snap.specifics.expect_primitive()),
        None,
    ))
}
