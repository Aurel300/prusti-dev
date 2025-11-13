use pcg::utils::Place;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    ConstEnc, MirBuiltinEnc, MirBuiltinEncTask, r#const::ConstEncTask, ty::use_pure::TyUsePure,
};
use prusti_rustc_interface::{
    abi,
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

#[allow(type_alias_bounds)]
pub(crate) type EncResult<'vir, T, Enc: PureRvalueEnc<'vir>> =
    Result<T, EncodeFullError<'vir, Enc::Encoder>>;

#[allow(type_alias_bounds)]
pub(crate) type ExprResult<'vir, Enc: PureRvalueEnc<'vir>> = Result<
    vir::ExprGenSnap<'vir, Enc::ExprCurr, Enc::ExprNext>,
    EncodeFullError<'vir, Enc::Encoder>,
>;

pub(crate) trait PureRvalueEnc<'vir> {
    type Encoder: TaskEncoder + 'vir;
    type EncodePlaceCtxt;
    type ExprCurr;
    type ExprNext;
    fn def_id(&self) -> DefId;
    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, Self::Encoder>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir>;
    fn body(&self) -> &mir::Body<'vir>;
    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir>;

    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self>;

    fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext>;

    fn encode_cast_snap<'slf>(
        &'slf mut self,
        kind: mir::CastKind,
        operand: &mir::Operand<'vir>,
        ty: ty::Ty<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        if !matches!(kind, mir::CastKind::IntToInt) {
            todo!("cast kind {kind:?}");
        }
        let encoded_operand = self.encode_operand_snap(operand, ctxt)?;
        let from_ty = operand.ty(self.body(), self.vcx().tcx());
        let from_vir_ty = self.ty_use_pure(from_ty).expect_primitive().expect_native();
        let to_vir_ty = self.ty_use_pure(ty).expect_primitive();
        let from_prim = from_vir_ty.snap_to_prim.call()(encoded_operand.downcast_ty());
        Ok(to_vir_ty.prim_to_snap.call()(from_prim).upcast_ty())
    }

    fn encode_binop_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::BinOp,
        l: &mir::Operand<'vir>,
        r: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let encoded_l = self.encode_operand_snap(l, ctxt)?;
        let encoded_r = self.encode_operand_snap(r, ctxt)?;
        let l_ty = l.ty(self.body(), self.vcx().tcx());
        let r_ty = r.ty(self.body(), self.vcx().tcx());
        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
        let task = if op.is_overflowing() {
            CheckedBinOp(rvalue_ty, op, l_ty, r_ty)
        } else {
            BinOp(rvalue_ty, op, l_ty, r_ty)
        };
        let binop_function = self
            .deps()
            .require_ref::<MirBuiltinEnc>(task)
            .unwrap()
            .bin_op()
            .unwrap();
        Ok(binop_function.call()(encoded_l.downcast_ty(), encoded_r.downcast_ty()).upcast_ty())
    }

    fn encode_constant_snap(
        &mut self,
        constant: &mir::ConstOperand<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, Self::Encoder>> {
        let def_id = self.def_id();
        self.deps().require_dep::<ConstEnc>(ConstEncTask::Mir {
            const_: constant.const_,
            encoding_depth: 0,
            def_id,
            span: constant.span,
        })
    }

    fn encode_un_op_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        op: mir::UnOp,
        operand: &mir::Operand<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let encoded_operand = self.encode_operand_snap(operand, ctxt)?;
        let operand_ty = operand.ty(self.body(), self.vcx().tcx());
        let un_op_function = self
            .deps()
            .require_ref::<MirBuiltinEnc>(MirBuiltinEncTask::UnOp(rvalue_ty, op, operand_ty))
            .unwrap()
            .un_op()
            .unwrap();
        Ok(un_op_function.call()(encoded_operand.downcast_ty()).upcast_ty())
    }

    fn encode_aggregate_snap(
        &mut self,
        rvalue_ty: ty::Ty<'vir>,
        kind: &mir::AggregateKind<'vir>,
        fields: &IndexVec<abi::FieldIdx, mir::Operand<'vir>>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> ExprResult<'vir, Self> {
        let encoded_fields = fields
            .iter()
            .map(|field| self.encode_operand_snap(field, ctxt))
            .collect::<Result<Vec<_>, _>>()?;
        let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
        let sl = match kind {
            mir::AggregateKind::Adt(_, vidx, _, _, _) => e_rvalue_ty.get_variant_any(*vidx),
            _ => e_rvalue_ty.expect_structlike(),
        };
        Ok(sl.field_snaps_to_snap(encoded_fields).upcast_ty())
    }

    fn encode_len_snap(
        &mut self,
        place: Place<'vir>,
        ctxt: &Self::EncodePlaceCtxt,
    ) -> vir::ExprGenSnap<'vir, Self::ExprCurr, Self::ExprNext> {
        let encoded_place = self.encode_place_snap(place, ctxt);
        let place_ty = (*place).ty(self.body(), self.vcx().tcx());
        let len_function = self
            .deps()
            .require_ref::<MirBuiltinEnc>(crate::encoders::MirBuiltinEncTask::Len(place_ty.ty))
            .unwrap()
            .len()
            .unwrap();
        len_function.call()(encoded_place.downcast_ty()).upcast_ty()
    }
}
