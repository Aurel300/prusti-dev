use crate::encoders::{domain::{DomainBuilder, DomainEnc, DomainEncSpecifics}, predicate::{PredicateBuilder, PredicateEncData}, snapshot::SnapshotEncOutput, PredicateEnc};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

pub(crate) fn domain<'vir>(
    _task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    Ok(DomainEncSpecifics::Opaque)
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDecl<'vir>],
    generic_exprs: &[vir::Expr<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    // let ty = task_key.ty();
    // let ty_kind = ty.kind();

    let snap_type = snap.snapshot;

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    // main predicate
    builder.predicate(
        "",
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        None,
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
                &[], // &[vir::expr! { false }],
                &[],
                None,
            )
            .1,
    );

    Ok(PredicateEncData::Opaque)
}
