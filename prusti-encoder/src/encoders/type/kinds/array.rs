use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncOutputRef, DomainEncSpecifics}, predicate::{PredicateBuilder, PredicateEncData}, rust_ty_snapshots::RustTySnapshotsEnc, snapshot::SnapshotEncOutput, GenericEnc, PredicateEnc, PredicateEncOutputRef
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdent, MethodIdent, ToKnownArity, UnaryArity, UnknownArity};

#[derive(Clone, Copy, Debug)]
pub struct DomainDataArray<'vir> {
    pub prim_type: vir::Type<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> DomainEncSpecifics<'vir> {
    #[track_caller]
    pub fn expect_array(self) -> DomainDataArray<'vir> {
        match self {
            Self::Array(data) => data,
            _ => panic!("expected array domain data (got {self:?})"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataArray<'vir> {
    pub snap_data: DomainDataArray<'vir>,
    pub index_access: FunctionIdent<'vir, UnknownArity<'vir>>,
    pub unfold_index: MethodIdent<'vir, UnknownArity<'vir>>,
    pub fold_index: MethodIdent<'vir, UnknownArity<'vir>>,
}

impl<'vir> PredicateEncOutputRef<'vir> {
    #[track_caller]
    pub fn expect_array(&self) -> &PredicateEncDataArray<'vir> {
        match &self.specifics {
            PredicateEncData::Array(data) => data,
            s => panic!("expected array predicate data (got {s:?})"),
        }
    }
}

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _output_ref: &DomainEncOutputRef<'vir>,
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

    Ok(DomainEncSpecifics::Array(DomainDataArray {
        prim_type,
        snap_to_prim: value_ident.to_known(),
        prim_to_snap: cons_ident.to_known(),
    }))
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
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
    let snap_data = snap.specifics.expect_array();

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        None,
    );

    // Ref-to-snap
    let (snap_ident, snap_func) = builder.mk_function(
        "snap",
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        snap_type,
        &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
        &[],
        None,
    );
    builder.function_snap = Some(snap_func);

    // "borrowed" predicate, to frame across index accesses
    let borrowed_pred = builder.predicate(
        "borrowed",
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        None,
    );
    let borrowed_snap = builder.function(
        "borrowed_snap",
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        snap_type,
        &[vir::expr! { acc_wildcard([borrowed_pred](ref_self, ..[generic_exprs])) }],
        &[],
        None,
    );

    let index_access = builder.function(
        "index",
        &[ref_self_decl].into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        &vir::TypeData::Ref,
        &[], // TODO: should have a read permission here!
        &[],
        None,
    );

    // unfold/fold index
    let self_snap = vir::expr! { [snap_ident](ref_self, ..[generic_exprs]) };
    let self_val = vir::expr! { [snap_data.snap_to_prim](self_snap) };
    let index = builder.vcx.mk_local("index", &vir::TypeData::Int);
    let index_decl = builder.vcx.mk_local_decl_local(index);
    let generic_enc = deps.require_ref::<GenericEnc>(())?;
    let index_val = builder.vcx.mk_bin_op_expr(vir::BinOpKind::SeqIndex, self_val, vir::expr! { index });

    let unfold_index = builder.method(
        "unfold_index",
        &[index_decl, ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        &[],
        &[
            vir::expr! { acc([self_pred](ref_self, ..[generic_exprs])) },
            vir::expr! { ((0) <= (index)) && ((index) < (vpr_seq_len(self_val))) },
        ],
        &[
            vir::expr! { acc([borrowed_pred](ref_self, ..[generic_exprs])) },
            vir::expr! { acc([generic_enc.ref_to_pred]([index_access](ref_self, ..[generic_exprs]), ..[generic_exprs])) },
            vir::expr! { ([borrowed_snap](ref_self, ..[generic_exprs])) == (old(self_snap)) },
            vir::expr! { ([generic_enc.ref_to_snap]([index_access](ref_self, ..[generic_exprs]), ..[generic_exprs])) == (old(index_val)) },
        ],
    );

    let fold_index = builder.method(
        "fold_index",
        &[index_decl, ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        &[],
        &[
            vir::expr! { acc([borrowed_pred](ref_self, ..[generic_exprs])) },
            vir::expr! { acc([generic_enc.ref_to_pred]([index_access](ref_self, ..[generic_exprs]), ..[generic_exprs])) },
            vir::expr! { ((0) <= (index)) && ((index) < (vpr_seq_len([snap_data.snap_to_prim]([borrowed_snap](ref_self, ..[generic_exprs]))))) },
        ],
        &[
            vir::expr! { acc([self_pred](ref_self, ..[generic_exprs])) },
            vir::expr! { (vpr_seq_len(self_val)) == (old(vpr_seq_len([snap_data.snap_to_prim]([borrowed_snap](ref_self, ..[generic_exprs]))))) },
            vir::expr! {
                forall i: [&vir::TypeData::Int] :: {[builder.vcx.mk_bin_op_expr(vir::BinOpKind::SeqIndex, self_val, vir::expr! { i })]} (((0) <= (i)) && ((i) < (vpr_seq_len(self_val))))
                    ==> (([builder.vcx.mk_bin_op_expr(vir::BinOpKind::SeqIndex, self_val, vir::expr! { i })]) == ([builder.vcx.mk_ternary_expr(
                        vir::expr! { (i) == (index) },
                        vir::expr! { old([generic_enc.ref_to_snap]([index_access](ref_self, ..[generic_exprs]), ..[generic_exprs])) },
                        vir::expr! { old([builder.vcx.mk_bin_op_expr(
                            vir::BinOpKind::SeqIndex,
                            vir::expr! { [snap_data.snap_to_prim]([borrowed_snap](ref_self, ..[generic_exprs])) },
                            vir::expr! { i },
                        )]) },
                    )]))
            },
        ],
    );

    Ok((
        PredicateEncData::Array(PredicateEncDataArray {
            snap_data: snap.specifics.expect_array(),
            index_access,
            unfold_index,
            fold_index,
        }),
        None,
    ))
}
