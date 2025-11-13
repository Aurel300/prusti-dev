use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    MirBuiltinEnc, MirBuiltinEncTask, TyUsePureEnc,
    ty::{RustTyDecomposition, generics::GParams, use_pure::TyUsePure},
};
use prusti_rustc_interface::middle::{mir, ty};

pub(super) struct PureRvalueEnc<'vir: 'enc, 'enc, Enc: TaskEncoder, Ctxt> {
    vcx: &'vir vir::VirCtxt<'vir>,
    context: Ctxt,
    deps: &'enc mut TaskEncoderDependencies<'vir, Enc>,
    body: &'enc mir::Body<'vir>,
}

impl<'vir: 'enc, 'enc, Enc: TaskEncoder, Ctxt: Copy + Into<GParams<'vir>>>
    PureRvalueEnc<'vir, 'enc, Enc, Ctxt>
{
    pub(super) fn new(
        vcx: &'vir vir::VirCtxt<'vir>,
        context: Ctxt,
        deps: &'enc mut TaskEncoderDependencies<'vir, Enc>,
        body: &'enc mir::Body<'vir>,
    ) -> Self {
        Self {
            vcx,
            context,
            deps,
            body,
        }
    }

    fn ty_use(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.context);
        self.deps.require_dep::<TyUsePureEnc>(ty_task).unwrap()
    }

    pub(super) fn encode_len<Curr, Next>(
        &mut self,
        place: &mir::Place<'vir>,
        encoded_place: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let place_ty = place.ty(self.body, self.vcx.tcx());
        let len_function = self
            .deps
            .require_ref::<MirBuiltinEnc>(crate::encoders::MirBuiltinEncTask::Len(place_ty.ty))
            .unwrap()
            .len()
            .unwrap();
        len_function.call()(encoded_place.downcast_ty()).upcast_ty()
    }

    pub(super) fn encode_un_op<Curr, Next>(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::UnOp,
        operand: &mir::Operand<'vir>,
        encoded_operand: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let operand_ty = operand.ty(self.body, self.vcx.tcx());
        let un_op_function = self
            .deps
            .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::UnOp(rvalue_ty, op, operand_ty))
            .unwrap()
            .un_op()
            .unwrap();
        un_op_function.call()(encoded_operand.downcast_ty()).upcast_ty()
    }

    pub(super) fn encode_aggregate<Curr, Next>(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        kind: mir::AggregateKind,
        encoded_fields: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let e_rvalue_ty = self.ty_use(rvalue_ty);
        let sl = match kind {
            mir::AggregateKind::Adt(_, vidx, _, _, _) => e_rvalue_ty.get_variant_any(vidx),
            _ => e_rvalue_ty.expect_structlike(),
        };
        sl.field_snaps_to_snap(encoded_fields).upcast_ty()
    }

    pub(super) fn encode_binop<Curr, Next>(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l: &mir::Operand<'vir>,
        r: &mir::Operand<'vir>,
        encoded_l: vir::ExprGenSnap<'vir, Curr, Next>,
        encoded_r: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let l_ty = l.ty(self.body, self.vcx.tcx());
        let r_ty = r.ty(self.body, self.vcx.tcx());
        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
        let task = if op.is_overflowing() {
            CheckedBinOp(rvalue_ty, op, l_ty, r_ty)
        } else {
            BinOp(rvalue_ty, op, l_ty, r_ty)
        };
        let binop_function = self
            .deps
            .require_ref::<MirBuiltinEnc>(task)
            .unwrap()
            .bin_op()
            .unwrap();
        binop_function.call()(encoded_l.downcast_ty(), encoded_r.downcast_ty()).upcast_ty()
    }

    pub(super) fn encode_cast<Curr, Next>(
        &mut self,
        _kind: mir::CastKind,
        operand: &mir::Operand<'vir>,
        ty: ty::Ty<'vir>,
        encoded_operand: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let from_ty = operand.ty(self.body, self.vcx.tcx());
        let from_vir_ty = self.ty_use(from_ty).expect_primitive().expect_native();
        let to_vir_ty = self.ty_use(ty).expect_primitive();
        let from_prim = from_vir_ty.snap_to_prim.call()(encoded_operand.downcast_ty());
        to_vir_ty.prim_to_snap.call()(from_prim).upcast_ty()
    }
}
