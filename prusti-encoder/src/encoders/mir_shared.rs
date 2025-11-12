use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    TyUsePureEnc,
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

    pub(super) fn encode_cast<Curr, Next>(
        &mut self,
        kind: mir::CastKind,
        operand: &mir::Operand<'vir>,
        ty: ty::Ty<'vir>,
        encoded_operand: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        let from_ty = operand.ty(self.body, self.vcx.tcx());
        let from_vir_ty = self.ty_use(from_ty).expect_primitive();
        let to_vir_ty = self.ty_use(ty).expect_primitive();
        let from_prim = from_vir_ty.snap_to_prim.call()(encoded_operand.downcast_ty());
        to_vir_ty.prim_to_snap.call()(from_prim).upcast_ty()
    }
}
