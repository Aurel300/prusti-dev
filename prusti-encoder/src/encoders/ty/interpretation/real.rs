use task_encoder::EncodeFullError;
use vir::{BackendInterpretationPair, FunctionIdn, VirCtxt};

use crate::encoders::ty::pure::{DomainBuilder, TyPureBuiltinData, TyPureEnc};

#[derive(Debug, Clone, Copy)]
pub struct TyRealLocal<'vir> {
    pub real_add: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub real_sub: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub real_mul: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub real_div: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub real_neg: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub real_eq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub real_lt: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub real_le: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub real_gt: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub real_ge: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
}

pub(crate) fn ty_pure<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPureBuiltinData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    builder.set_interpretation(vcx.alloc_slice(&[vcx.alloc(BackendInterpretationPair {
        key: "SMTLIB",
        value: "(Real)",
    })]));
    let real_sub = builder.backend_func(
        "sub",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("-"),
    );
    let real_add = builder.backend_func(
        "add",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("+"),
    );
    let real_div = builder.backend_func(
        "div",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("/"),
    );
    let real_mul = builder.backend_func(
        "mul",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("*"),
    );
    let real_neg = builder.backend_func("neg", builder.self_type(), builder.self_type(), Some("-"));
    let real_eq = builder.backend_func(
        "eq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("="),
    );
    let real_lt = builder.backend_func(
        "lt",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("<"),
    );
    let real_le = builder.backend_func(
        "le",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("<="),
    );
    let real_gt = builder.backend_func(
        "gt",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some(">"),
    );
    let real_ge = builder.backend_func(
        "ge",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some(">="),
    );
    Ok(TyPureBuiltinData::TyPureBuiltinReal(TyRealLocal {
        real_add,
        real_sub,
        real_mul,
        real_div,
        real_neg,
        real_eq,
        real_lt,
        real_le,
        real_gt,
        real_ge,
    }))
}
