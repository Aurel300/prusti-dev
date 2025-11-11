use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType};

use crate::encoders::ty::{
    RustFloat,
    bitvec::{BitVecEnc, BitVecSize},
    impure::{PredicateBuilder, TyImpureEnc, TyImpureFloat},
    pure::{DomainBuilder, TyPureEnc, TyPureFloat, TyPureFloatData},
};

pub(crate) fn ty_pure<'vir>(
    data: &RustFloat<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureFloat<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let interpretation = match data {
        ty::FloatTy::F16 => "(_ FloatingPoint 5 11)",
        ty::FloatTy::F32 => "(_ FloatingPoint 8 24)",
        ty::FloatTy::F64 => "(_ FloatingPoint 11 53)",
        ty::FloatTy::F128 => "(_ FloatingPoint 15 113)",
    };
    builder.set_interpretation(interpretation);

    let fp_eq = builder.backend_func(
        "eq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        "fp.eq",
    );

    let fp_add = builder.backend_func(
        "add",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        "fp.add RNE",
    );

    let fp_sub = builder.backend_func(
        "sub",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        "fp.sub RNE",
    );

    let fp_mul = builder.backend_func(
        "mul",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        "fp.mul RNE",
    );

    let fp_div = builder.backend_func(
        "div",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        "fp.div RNE",
    );

    let fp_trunc = builder.backend_func(
        "trunc",
        builder.self_type(),
        builder.self_type(),
        "fp.roundToIntegral RTZ",
    );

    let fp_is_nan = builder.backend_func("is_nan", builder.self_type(), vir::TYPE_BOOL, "fp.isNaN");

    let fp_is_infinite = builder.backend_func(
        "is_infinite",
        builder.self_type(),
        vir::TYPE_BOOL,
        "fp.isInfinite",
    );

    let fp_lt = builder.backend_func(
        "lt",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        "fp.lt",
    );
    let fp_leq = builder.backend_func(
        "leq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        "fp.leq",
    );
    let fp_geq = builder.backend_func(
        "geq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        "fp.geq",
    );
    let fp_gt = builder.backend_func(
        "gt",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        "fp.gt",
    );
    let fp_neg = builder.backend_func("neg", builder.self_type(), builder.self_type(), "fp.neg");

    let fp_abs = builder.backend_func("abs", builder.self_type(), builder.self_type(), "fp.abs");

    let bit_vec = deps.require_dep::<BitVecEnc>(match data {
        ty::FloatTy::F16 => BitVecSize::BitVec16,
        ty::FloatTy::F32 => BitVecSize::BitVec32,
        ty::FloatTy::F64 => BitVecSize::BitVec64,
        ty::FloatTy::F128 => BitVecSize::BitVec128,
    })?;

    let from_bv = builder.backend_func(
        "from_bv",
        (bit_vec.domain)(),
        builder.self_type(),
        match data {
            ty::FloatTy::F16 => "(_ to_fp 5 11)",
            ty::FloatTy::F32 => "(_ to_fp 8 24)",
            ty::FloatTy::F64 => "(_ to_fp 11 53)",
            ty::FloatTy::F128 => "(_ to_fp 15 113)",
        },
    );
    let prim_type = vir::TYPE_INT.upcast_ty();
    let prim_to_snap = builder.function("prim_to_snap", prim_type, builder.self_type());

    builder.axiom("prim_to_snap", vir::expr! {
        forall i: [prim_type] :: {[prim_to_snap](i)} ([prim_to_snap(i)]) == ([from_bv]([bit_vec.from_int](i)))
    });

    Ok(TyPureFloatData::new(
        from_bv,
        fp_eq,
        prim_to_snap,
        fp_add,
        fp_sub,
        fp_mul,
        fp_div,
        fp_trunc,
        fp_is_nan,
        fp_is_infinite,
        fp_lt,
        fp_leq,
        fp_gt,
        fp_geq,
        fp_neg,
        fp_abs,
    ))
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustFloat<'vir>, &TyPureFloat<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureFloat<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let prim_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.predicate::<vir::Ref>(
        "",
        ref_self_decl.ty(),
        (ref_self_decl,),
        Some(vir::expr! { acc((ref_self).[prim_field]) }),
    );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<vir::Ref, _>(
                "snap",
                ref_self_decl.ty(),
                snap_type,
                (ref_self_decl,),
                &[vir::expr! { acc([self_pred](ref_self)) }],
                &[],
                Some(vir::expr! {
                    unfolding ([self_pred](ref_self)) in ([prim_field](ref_self))
                }),
            )
            .1,
    );

    Ok(())
}
