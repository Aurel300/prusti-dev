use pcg::{
    borrow_pcg::region_projection::{
        MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
    },
    free_pcs::PcgBasicBlock,
    pcg::{EvalStmtPhase, PCGNode},
    r#loop::LoopId,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, Place, SnapshotLocation},
};
use prusti_rustc_interface::{
    middle::{
        mir::{self, visit::Visitor},
        ty::{self, TyKind},
    },
    span::def_id::DefId,
};
use std::collections::HashSet;

use task_encoder::TaskEncoder;
use vir::{CastType, Reify};

use crate::{
    encoders::{
        indirect::{IndirectKey, IndirectPredicatesEnc},
        lifted::rust_ty_cast::RustTyCastersEnc,
        mir_pure::{MirPureEnc, MirPureEncTask, PureKind},
        rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
        rust_ty_snapshots::RustTySnapshotsEnc,
        spec, ImpureEncVisitor,
    },
    CastTypePure,
};

type ExprInput<'vir> = (DefId, &'vir [vir::Expr<'vir>]);
type ExprRet<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

pub(super) enum WandOldOuter<'vir> {
    LetBind(Vec<(&'vir str, vir::ExprSnap<'vir>)>),
    Label(Option<&'vir str>),
}

struct CollectedLocals {
    locals: HashSet<mir::Local>,
}

impl CollectedLocals {
    fn new() -> Self {
        Self {
            locals: HashSet::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for CollectedLocals {
    fn visit_local(
        &mut self,
        local: mir::Local,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.locals.insert(local);
    }
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    fn collect_used_locals_in_loop(
        &self,
        loop_id: LoopId,
    ) -> std::collections::HashSet<mir::Local> {
        let mut visitor = CollectedLocals::new();

        for (block_idx, block_data) in self.body.basic_blocks.iter_enumerated() {
            if !self.loop_analysis.in_loop(block_idx, loop_id) {
                continue;
            }

            visitor.visit_basic_block_data(block_idx, block_data);
        }

        visitor.locals
    }

    /// Calculate invariant at loop head
    pub(crate) fn get_loop_inv(
        &mut self,
        lh: LoopId,
        cfpcs: &PcgBasicBlock<'vir>,
    ) -> &'vir [vir::ExprBool<'vir>] {
        let mut inv = Vec::new();
        let start = &cfpcs.statements[0];
        let state = &start.states[EvalStmtPhase::PreOperands];
        let used_locals = self.collect_used_locals_in_loop(lh);
        // let borrows = &*start.borrows[EvalStmtPhase::PreOperands];
        // self.stmt(self.vcx.mk_comment_stmt(
        //     vir::vir_format!(self.vcx, "_borrows: {:#?}", borrows),
        // ));
        for cap_local in state.owned_pcg().locals().iter() {
            if cap_local.is_unallocated() {
                continue;
            }
            let cap = cap_local.get_allocated();
            for place in cap.leaves(self.pcg_ctxt()).iter() {
                if !state.capabilities().is_exclusive(*place) {
                    continue;
                }
                if !used_locals.contains(&place.local) {
                    continue;
                }
                let (place_res, snap, _, _) = self.encode_place_snap(*place);
                let ty = (*place).ty(self.pcg_ctxt());
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
                let pred = ty_out.ref_to_pred(self.vcx, place_res.expr, None);
                inv.push(pred);

                let regions = ty.ty.walk().flat_map(IndirectKey::from_generic_arg);
                for region in regions {
                    let indirect = self
                        .deps
                        .require_ref::<IndirectPredicatesEnc>((ty.ty, region))
                        .unwrap();
                    inv.extend(
                        indirect
                            .covariant
                            .into_iter()
                            .map(|expr| expr.reify(self.vcx, snap)),
                    );
                }
            }
        }
        for (_edge, inputs, outputs) in Self::get_abstraction_edges(state.borrow_pcg().graph()) {
            let mut let_bind = WandOldOuter::LetBind(Vec::new());
            let mut wand_rhs = Vec::new();
            for i in inputs {
                self.encode_pcg_node(&i, &mut wand_rhs, &mut let_bind);
            }
            let mut wand_lhs = Vec::new();
            for i in outputs {
                let exprs = self.encode_region_projection(i, &mut let_bind);
                wand_lhs.extend(exprs);
            }
            let wand = self.vcx.mk_wand(
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
            );
            let mut wand = self.vcx.mk_wand_expr(wand);
            let WandOldOuter::LetBind(let_bind) = let_bind else {
                unreachable!()
            };
            for (ident, expr) in let_bind {
                wand = self.vcx.mk_let_expr(ident, expr, wand);
            }
            inv.push(wand);
        }

        let loop_invariants_map = self.build_loop_invariants_map();
        if let Some(loop_invariants) = loop_invariants_map.get(&lh) {
            inv.extend(loop_invariants.iter().cloned());
        }

        self.vcx.alloc_slice(&inv)
    }

    pub(super) fn encode_pcg_node(
        &mut self,
        node: &PCGNode<'vir, MaybeRemotePlace<'vir>, MaybeRemotePlace<'vir>>,
        wand_rhs: &mut Vec<vir::ExprBool<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) {
        match node {
            PCGNode::Place(MaybeRemotePlace::Remote(_)) => unreachable!(),
            PCGNode::Place(place @ MaybeRemotePlace::Local(_)) => {
                let p = Self::get_place(*place);
                let ty = (*p).ty(self.local_decls, self.vcx.tcx());
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
                let p = self.encode_place(p);
                let p = self.configure_old(*place, p.expr, old_outer);

                let pred = ty_out.ref_to_pred(self.vcx, p, None);
                wand_rhs.push(pred);
            }
            PCGNode::RegionProjection(r) => {
                let exprs = self.encode_region_projection(*r, old_outer);
                wand_rhs.extend(exprs);
            }
        }
    }

    pub(super) fn encode_region_projection<T: RegionProjectionBaseLike<'vir>>(
        &mut self,
        r: RegionProjection<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::ExprBool<'vir>> {
        let place = r.place().to_maybe_remote_region_projection_base();
        let (place_snap, ty, _) = match place {
            MaybeRemoteRegionProjectionBase::Place(p) => {
                self.encode_maybe_remote_place_snap(p, old_outer)
            }
            MaybeRemoteRegionProjectionBase::Const(c) => todo!("{c:?}"),
        };
        let mut regions = ty.ty.walk().flat_map(IndirectKey::from_generic_arg);
        let region = regions.next().unwrap();
        // TODO:
        assert!(
            regions.next().is_none(),
            "multiple regions in a type not supported ({:?})",
            ty.ty
        );
        let indirect = self
            .deps
            .require_ref::<IndirectPredicatesEnc>((ty.ty, region))
            .unwrap();
        indirect
            .covariant
            .into_iter()
            .map(|expr| expr.reify(self.vcx, place_snap))
            .collect::<Vec<_>>()
    }

    fn get_place(place: MaybeRemotePlace<'vir>) -> Place<'vir> {
        match place {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) => place,
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(place)) => place.place(),
            MaybeRemotePlace::Remote(r) => r.assigned_local().into(),
        }
    }

    fn encode_maybe_remote_place_snap(
        &mut self,
        place: MaybeRemotePlace<'vir>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> (
        vir::ExprSnap<'vir>,
        mir::tcx::PlaceTy<'vir>,
        RustTyPredicatesEncOutputRef<'vir>,
    ) {
        let p = Self::get_place(place);
        let (_, place_snap, ty, ty_out) = self.encode_place_snap(p);
        let place_snap = self.configure_old(place, place_snap, old_outer);
        (place_snap, ty, ty_out)
    }

    fn configure_old<T: vir::CompType>(
        &mut self,
        place: MaybeRemotePlace,
        expr: vir::Expr<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir, T> {
        match place {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { .. }) => {
                self.mk_wand_outer(expr, old_outer)
            }
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(place)) => {
                let label = Self::get_location_label(self.vcx, place.at());
                self.vcx.mk_old(expr, label)
            }
            MaybeRemotePlace::Remote(_) => self.vcx.mk_old_expr(expr),
        }
    }

    pub(crate) fn get_location_label(
        vcx: &'vir vir::VirCtxt<'vir>,
        at: SnapshotLocation,
    ) -> vir::OldLabel<'vir> {
        match at {
            // TODO: handle this properly!!
            SnapshotLocation::After(loc) => {
                let name =
                    vir::vir_format!(vcx, "_after_{}_{}", loc.block.index(), loc.statement_index);
                vir::OldLabel::Label(name)
            }
            SnapshotLocation::Mid(loc) => {
                let name =
                    vir::vir_format!(vcx, "_mid_{}_{}", loc.block.index(), loc.statement_index);
                vir::OldLabel::Label(name)
            }
            SnapshotLocation::Start(bb) => {
                vir::OldLabel::Block(vir::CfgBlockLabelData::BasicBlock(bb.as_usize()))
            }
        }
    }

    fn mk_wand_outer<T: vir::CompType>(
        &mut self,
        expr: vir::Expr<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir, T> {
        match old_outer {
            WandOldOuter::LetBind(let_bind) => {
                let ident = vir::vir_format!(self.vcx, "_snap{}", let_bind.len());
                // TODO: this is sometimes `Ref` type?
                let_bind.push((ident, expr.inner_cast_ty()));
                self.vcx.mk_local_ex(ident, expr.ty())
            }
            WandOldOuter::Label(label) => {
                let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
                self.vcx.mk_local_labelled_old_expr(expr, label)
            }
        }
    }

    fn build_loop_invariants_map(
        &mut self,
    ) -> std::collections::HashMap<LoopId, Vec<vir::Expr<'vir>>> {
        let mut loop_invariants_map = std::collections::HashMap::new();

        for (block_idx, block_data) in self.body.basic_blocks.iter_enumerated() {
            for stmt in &block_data.statements {
                if let mir::StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
                    if let mir::Rvalue::Aggregate(
                        box mir::AggregateKind::Closure(cl_def_id, cl_args),
                        ref upvar_operands,
                    ) = rvalue
                    {
                        let is_loop_invariant = spec::with_type_spec(|def_spec| {
                            if let Some(loop_spec) = def_spec.get_loop_spec(cl_def_id) {
                                assert!(!matches!(loop_spec, prusti_interface::specs::typed::LoopSpecification::BodyInvariant(_)), "body_invariant! currently not supported");
                                matches!(loop_spec, prusti_interface::specs::typed::LoopSpecification::LoopInvariant(_))
                            } else {
                                false
                            }
                        });

                        if is_loop_invariant {
                            if let Some(innermost_loop_id) =
                                self.loop_analysis.innermost_loop(block_idx)
                            {
                                let invariant_expr = self.encode_loop_invariant_closure(
                                    *cl_def_id,
                                    *cl_args,
                                    &upvar_operands.raw,
                                );
                                let concrete_expr = unsafe {
                                    std::mem::transmute::<ExprRet<'_>, vir::ExprGen<'_, !, !>>(
                                        invariant_expr,
                                    )
                                };

                                loop_invariants_map
                                    .entry(innermost_loop_id)
                                    .or_insert_with(Vec::new)
                                    .push(concrete_expr);
                            }
                        }
                    }
                }
            }
        }

        loop_invariants_map
    }

    fn encode_loop_invariant_closure(
        &mut self,
        cl_def_id: DefId,
        _cl_args: ty::GenericArgsRef<'vir>,
        upvar_operands: &[mir::Operand<'vir>],
    ) -> ExprRet<'vir> {
        let tcx = self.vcx.tcx();
        let closure_ty = tcx.type_of(cl_def_id).instantiate_identity();

        let (qvar_tys, upvar_rust_tys_from_closure_sig) = match closure_ty.kind() {
            TyKind::Closure(_, gen_args) => (
                match gen_args.as_closure().sig().skip_binder().inputs()[0].kind() {
                    TyKind::Tuple(list) => list,
                    _ => unreachable!("Invariant closure signature malformed: qvars not a tuple"),
                },
                gen_args.as_closure().upvar_tys().iter().collect::<Vec<_>>(),
            ),
            _ => panic!("Illegal loop invariant closure type: {:?}", closure_ty),
        };

        let qvars = self.vcx.alloc_slice(
            &qvar_tys
                .iter()
                .enumerate()
                .map(|(idx, qvar_ty)| {
                    let ty_out = self
                        .deps
                        .require_ref::<RustTySnapshotsEnc>(qvar_ty)
                        .unwrap();
                    self.vcx.mk_local_decl(
                        vir::vir_format!(self.vcx, "qvar_{idx}"),
                        ty_out.generic_snapshot.snapshot,
                    )
                })
                .collect::<Vec<_>>(),
        );
        let mut ref_to_original_place_map: std::collections::HashMap<
            mir::Place<'vir>,
            mir::Place<'vir>,
        > = std::collections::HashMap::new();
        for (_block_idx, block_data) in self.body.basic_blocks.iter_enumerated() {
            for stmt in &block_data.statements {
                if let mir::StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                    if let mir::Rvalue::Ref(_, _, original_place) = rvalue {
                        if let Some(existing_place) =
                            ref_to_original_place_map.insert(*place, *original_place)
                        {
                            panic!("Collision in ref_to_original_place_map: place {:?} already mapped to {:?}, trying to map to {:?}", 
                                   place, existing_place, original_place);
                        }
                    }
                }
            }
        }

        let mut fields_for_closure_struct = Vec::new();

        for (idx, upvar_operand) in upvar_operands.iter().enumerate() {
            let upvar_mir_place = match upvar_operand {
                mir::Operand::Move(p) | mir::Operand::Copy(p) => *p,
                mir::Operand::Constant(_) => {
                    panic!("Constant upvars in loop invariant closure not yet handled")
                }
            };

            let original_mir_place =
                ref_to_original_place_map
                    .get(&upvar_mir_place)
                    .expect(&format!(
                        "Could not find original place for upvar {:?}",
                        upvar_mir_place
                    ));
            let original_place_viper_ref = self.encode_place((*original_mir_place).into()).expr;
            let original_place_rust_ty = original_mir_place.ty(self.body, self.vcx.tcx()).ty;
            let (_, direct_snap_of_original_place, _, _) =
                self.encode_place_snap((*original_mir_place).into());
            let val_caster = self
                .deps
                .require_local::<RustTyCastersEnc<CastTypePure>>(original_place_rust_ty)
                .unwrap();
            let param_for_snap_original =
                val_caster.cast_to_generic_if_necessary(self.vcx, direct_snap_of_original_place);
            let upvar_ref_rust_ty = upvar_rust_tys_from_closure_sig[idx];
            let s_ref_imm_enc_for_field = self
                .deps
                .require_local::<RustTySnapshotsEnc>(upvar_ref_rust_ty)
                .unwrap();
            let field_s_ref_immutable_expr = s_ref_imm_enc_for_field
                .generic_snapshot
                .specifics
                .expect_immref()
                .prim_to_snap
                .apply(
                    self.vcx,
                    [original_place_viper_ref, param_for_snap_original],
                );

            fields_for_closure_struct.push(field_s_ref_immutable_expr);
        }

        let closure_struct_snapshots_enc = self
            .deps
            .require_local::<RustTySnapshotsEnc>(closure_ty)
            .unwrap();
        let closure_struct_val_expr = vir::with_vcx(|vcx| {
            closure_struct_snapshots_enc
                .generic_snapshot
                .specifics
                .expect_structlike()
                .field_snaps_to_snap
                .apply(vcx, vcx.alloc_slice(&fields_for_closure_struct))
        });

        let closure_caster = self
            .deps
            .require_local::<RustTyCastersEnc<CastTypePure>>(closure_ty)
            .unwrap();
        let closure_struct_as_param_expr =
            closure_caster.cast_to_generic_if_necessary(self.vcx, closure_struct_val_expr);
        let outer_ref_to_closure_rust_ty = tcx.mk_ty_from_kind(ty::TyKind::Ref(
            tcx.lifetimes.re_erased,
            closure_ty,
            ty::Mutability::Not,
        ));
        let outer_s_ref_imm_enc = self
            .deps
            .require_local::<RustTySnapshotsEnc>(outer_ref_to_closure_rust_ty)
            .unwrap();

        let final_reify_arg0 = outer_s_ref_imm_enc
            .generic_snapshot
            .specifics
            .expect_immref()
            .prim_to_snap
            .apply(self.vcx, [self.vcx.mk_null(), closure_struct_as_param_expr]);

        let mut reify_args = vec![final_reify_arg0];
        reify_args.extend(
            qvars
                .iter()
                .map(|qvar| self.vcx.mk_local_ex(qvar.name, qvar.ty)),
        );

        let body = self
            .deps
            .require_local::<MirPureEnc>(MirPureEncTask {
                encoding_depth: 1,
                kind: PureKind::Closure,
                parent_def_id: cl_def_id,
                param_env: tcx.param_env(cl_def_id),
                substs: ty::List::identity_for_item(self.vcx.tcx(), cl_def_id),
                caller_def_id: Some(self.def_id),
            })
            .unwrap()
            .expr;

        let reified_body = body
            .reify(self.vcx, (cl_def_id, self.vcx.alloc_slice(&reify_args)))
            .lift();

        let bool_snapshots_enc = self
            .deps
            .require_local::<RustTySnapshotsEnc>(tcx.types.bool)
            .unwrap();
        let bool_primitive_enc = bool_snapshots_enc
            .generic_snapshot
            .specifics
            .expect_primitive();

        self.vcx.mk_forall_expr(
            qvars,
            &[],
            bool_primitive_enc
                .snap_to_prim
                .apply(self.vcx, [reified_body]),
        )
    }
}
