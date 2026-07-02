use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::{CallableIdn, CastType, FunctionIdn, HasType, MethodIdn};

use crate::encoders::{
    ConstEnc, TyUseImpureEnc,
    r#const::ConstEncTask,
    ty::{
        RustTy, RustTyDecomposition, TySpecifics,
        generics::{GParams, GenericParamsEnc},
        interpretation::float::FloatDomain,
        pure::{TyPure, TyPurePrimData, TyPurePrimDataKind},
        use_pure::TyUsePureEnc,
    },
};

pub struct MirBuiltinUnOpEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MirBuiltinUnOpTask<'vir> {
    result_ty: RustTy<'vir>,
    op: mir::UnOp,
    operand_ty: RustTy<'vir>,
}

impl<'vir> MirBuiltinUnOpTask<'vir> {
    pub fn new(
        result_ty: RustTyDecomposition<'vir>,
        op: mir::UnOp,
        operand_ty: RustTyDecomposition<'vir>,
    ) -> Self {
        Self {
            result_ty: result_ty.ty,
            op,
            operand_ty: operand_ty.ty,
        }
    }
}

impl TaskEncoder for MirBuiltinUnOpEnc {
    task_encoder::encoder_cache!(MirBuiltinUnOpEnc);
    const ENCODER_NAME: &'static str = "MIR builtin unary op encoder";

    type TaskDescription<'vir> = MirBuiltinUnOpTask<'vir>;

    type OutputFullDependency<'vir> = vir::FunctionIdn<'vir, vir::CSnap, vir::CSnap>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let MirBuiltinUnOpTask {
            result_ty,
            op,
            operand_ty,
        } = *task_key;
        assert!(matches!(op, mir::UnOp::Neg | mir::UnOp::Not));
        vir::with_vcx(|vcx| {
            assert_eq!(result_ty, operand_ty);
            let ty_task = RustTyDecomposition::identity(operand_ty);
            let e_ty = deps.require_dep::<TyUsePureEnc>(ty_task)?;

            let name = vir::vir_format_identifier!(vcx, "mir_unop_{op:?}_{}", operand_ty.name());
            let e_ty_snap = e_ty.snapshot.downcast_ty();
            let fn_idn = FunctionIdn::new(name, e_ty_snap, e_ty_snap);

            let snap_arg_decl = vcx.mk_local_decl("arg", e_ty_snap);
            let prim_res_ty = e_ty.expect_primitive();
            let snap_arg = vcx.mk_local_ex(snap_arg_decl);
            let body = match prim_res_ty.kind {
                TyPurePrimDataKind::Native(native) => {
                    let prim_arg = (native.snap_to_prim)(snap_arg);
                    let mut val = (prim_res_ty.prim_to_snap)(
                        vcx.mk_unary_op_expr(vir::UnOpKind::from(op), prim_arg),
                    );
                    // Can overflow when doing `- iN::MIN -> iN::MIN`. There is no
                    // `CheckedUnOp`, instead the compiler puts an `TerminatorKind::Assert`
                    // before in debug mode. We should still produce the correct result in
                    // release mode, which the code under this branch does.
                    let operand_ty = *operand_ty.expect_primitive();
                    if op == mir::UnOp::Neg && operand_ty.is_signed() {
                        let bound = vcx.get_min_int(operand_ty.kind());
                        // `snap_to_prim(arg) == -iN::MIN`
                        let cond = vcx.mk_eq_expr(prim_arg.downcast_ty(), bound);
                        // `snap_to_prim(arg) == -iN::MIN ? arg :
                        // prim_to_snap(-snap_to_prim(arg))`
                        val = vcx.mk_ternary_expr(cond, snap_arg, val)
                    }
                    val
                }
                TyPurePrimDataKind::Float(float) => {
                    assert!(matches!(op, mir::UnOp::Neg));
                    (float.fp_neg)(snap_arg)
                }
            };
            let function = vcx.mk_function(fn_idn, (snap_arg_decl,), &[], &[], None, Some(body));
            Ok((function, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for function in Self::all_outputs_local_no_errors(program) {
            program.add_function(function);
        }
    }
}
