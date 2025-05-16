use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncSpecifics},
    predicate::{PredicateBuilder, PredicateEncData},
    snapshot::SnapshotEncOutput,
    PredicateEnc,
};
use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    target::abi,
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdent, ToKnownArity, UnaryArity};

#[derive(Clone, Copy, Debug)]
pub struct DomainDataPrim<'vir> {
    pub prim_type: vir::Type<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> DomainEncSpecifics<'vir> {
    #[track_caller]
    pub fn expect_primitive(self) -> DomainDataPrim<'vir> {
        match self {
            Self::Primitive(data) => data,
            _ => panic!("expected primitive"),
        }
    }
}

impl<'vir> DomainDataPrim<'vir> {
    pub fn expr_from_bits(&self, ty: ty::Ty<'vir>, value: u128) -> vir::Expr<'vir> {
        match *self.prim_type {
            vir::TypeData::Bool => {
                vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0)))
            }
            vir::TypeData::Int => {
                let (bit_width, signed) = match ty.kind() {
                    TyKind::Int(ty::IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u64, true),
                    TyKind::Int(ty) => (ty.bit_width().unwrap(), true),
                    TyKind::Uint(ty::UintTy::Usize) => {
                        ((std::mem::size_of::<usize>() * 8) as u64, true)
                    }
                    TyKind::Uint(ty) => (ty.bit_width().unwrap(), false),
                    kind => unreachable!("{kind:?}"),
                };
                let size = abi::Size::from_bits(bit_width);
                let negative_value = if signed {
                    let value = size.sign_extend(value);
                    Some(value).filter(|value| value.is_negative())
                } else {
                    None
                };
                match negative_value {
                    Some(value) => vir::with_vcx(|vcx| {
                        let value = vcx.mk_const_expr(vir::ConstData::Int(value.unsigned_abs()));
                        vcx.mk_unary_op_expr(vir::UnOpKind::Neg, value)
                    }),
                    None => vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Int(value))),
                }
            }
            ref k => unreachable!("{k:?}"),
        }
    }
}

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let prim_type = match ty_kind {
        ty::TyKind::Bool => &vir::TypeData::Bool,
        ty::TyKind::Char | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => &vir::TypeData::Int,
        ty::TyKind::Float(_) => todo!(),
        _ => unreachable!(),
    };

    let value_ident = builder.function("value", &[builder.self_type()], prim_type);
    let cons_ident = builder.function("cons", &[prim_type], builder.self_type());

    builder.axiom("cons", vir::expr! {
        forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
    });

    match ty_kind {
        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
            let min = builder.vcx.get_min_int(ty_kind);
            let max = builder.vcx.get_max_int(ty_kind);
            builder.axiom("bounds", vir::expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} (([min]) <= ([value_ident](s))) && (([value_ident](s)) <= ([max]))
            });
            builder.axiom(
                "value",
                vir::expr! {
                    forall value: [prim_type] :: {[cons_ident](value)}
                        ((([min]) <= (value)) && ((value) <= ([max])))
                            ==> (([value_ident]([cons_ident](value))) == (value))
                },
            );
        }
        _ => {
            builder.axiom("value", vir::expr! {
                forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
            });
        }
    };

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
    let prim_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl],
        Some(vir::expr! { acc_field([prim_field](ref_self)) }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function(
                "snap",
                &[ref_self_decl],
                snap_type,
                &[vir::expr! { acc_wildcard([self_pred](ref_self)) }],
                &[],
                Some(vir::expr! {
                    unfolding_wildcard ([self_pred](ref_self)) in ([prim_field](ref_self))
                }),
            )
            .1,
    );

    Ok((
        PredicateEncData::Primitive(snap.specifics.expect_primitive()),
        None,
    ))
}
