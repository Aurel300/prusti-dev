use pcg::{
    PcgOutput,
    action::{BorrowPcgAction, PcgAction, PcgActions},
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            abstraction::{AbstractionEdge, FunctionCallOrLoop},
            kind::BorrowPcgEdgeKind,
        },
        state::BorrowsState,
        unblock_graph::BorrowPcgUnblockAction,
    },
    coupling::PcgCoupledEdgeKind,
    free_pcs::RepackOp,
    r#loop::{LoopAnalysis, LoopId, PlaceUsages},
    pcg::{CapabilityKind, EvalStmtPhase, Pcg, PcgNode, PcgSuccessor},
    results::PcgBasicBlock,
    utils::{CompilerCtxt, HasPlace, Place, maybe_old::MaybeLabelledPlace},
};
<<<<<<< HEAD
use prusti_interface::{PrustiError, specs::specifications::SpecQuery};
use prusti_rustc_interface::{
    abi,
    data_structures::fx::FxHashMap,
    middle::{
        mir,
        ty::{self, TyKind},
    },
    span::def_id::DefId,
};
use prusti_utils::config;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, CompType};
=======
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    abi,
    middle::{
        mir,
        ty::{GenericArgs, TyKind},
    },
    span::def_id::DefId,
};
//use mir_ssa_analysis::{
//    SsaAnalysis,
//};
use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};
use vir::{MethodIdent, UnknownArity};
>>>>>>> ide/rewrite-2023-assistant-features

use crate::encoders::{
    self, FunctionCallEnc, MirBuiltinEnc, TyUseImpureEnc, WandEnc, WandEncTask,
    r#const::ConstEncTask,
    mir_fn::{CallTaskDescription, RustSignature},
    ty::{
        RustTyDecomposition,
        use_impure::TyUseImpure,
        use_pure::{TyUsePure, TyUsePureEnc},
    },
};

use super::{ConstEnc, WandEncOutput};

<<<<<<< HEAD
pub struct ImpureEncVisitor<'vir, 'enc, E: TaskEncoder>
where
    'vir: 'enc,
{
    pub vcx: &'vir vir::VirCtxt<'vir>,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, E>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'vir>,
    pub fpcs_analysis: PcgOutput<'enc, 'vir>,
    pub local_defs: crate::encoders::MirLocalDefEncOutput<'vir>,
    pub body: &'enc mir::Body<'vir>,

    pub wands: WandEncOutput<'vir>,

    pub tmp_ctr: usize,
    pub label_ctr: usize,
    pub call_labels: FxHashMap<mir::BasicBlock, (&'vir str, &'vir str)>,
    pub from_to_vars: FxHashMap<mir::BasicBlock, Vec<(mir::BasicBlock, vir::LocalDeclBool<'vir>)>>,

    // for the current basic block
    pub current_fpcs: Option<PcgBasicBlock<'enc, 'vir>>,

    pub current_block_label: Option<vir::CfgBlockLabel<'vir>>,
=======
#[derive(Clone, Debug)]
pub struct MirImpureEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirImpureEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

use crate::{
    encoder_traits::{impure_function_enc::{
        ImpureFunctionEncOutput, ImpureFunctionEncOutputRef,
    }, pure_func_app_enc::PureFuncAppEnc},
    encoders::{
        self,
        lifted::{
            aggregate_cast::{
                AggregateSnapArgsCastEnc,
                AggregateSnapArgsCastEncTask
            },
            func_app_ty_params::LiftedFuncAppTyParamsEnc
        },
        FunctionCallTaskDescription, MirBuiltinEnc
    },
    Span,
};

use super::{
    lifted::{
        cast::{CastArgs, CastToEnc},
        casters::CastTypeImpure,
        rust_ty_cast::RustTyCastersEnc
    },
    rust_ty_predicates::RustTyPredicatesEnc,
    ConstEnc,
    MirMonoImpureEnc,
    MirPolyImpureEnc
};
use tracing::log::debug;
use crate::hir::PatKind::Box;
use prusti_utils::config;

const ENCODE_REACH_BB: bool = false;

impl MirImpureEnc {
    pub fn monomorphize() -> bool {
        cfg!(feature = "mono_function_encoding")
    }
}

impl TaskEncoder for MirImpureEnc {
    task_encoder::encoder_cache!(MirImpureEnc);

    type TaskDescription<'vir> = FunctionCallTaskDescription<'vir>;

    type OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ImpureFunctionEncOutput<'vir>;

    type EncodingError = MirImpureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let monomorphize = Self::monomorphize();
        let output_ref = if monomorphize {
            deps.require_ref::<MirMonoImpureEnc>(*task_key)?
        } else {
            deps.require_ref::<MirPolyImpureEnc>(task_key.def_id)?
        };
        deps.emit_output_ref(*task_key, output_ref);
        let output: ImpureFunctionEncOutput<'_> = if monomorphize {
            deps.require_local::<MirMonoImpureEnc>(*task_key)?
        } else {
            deps.require_local::<MirPolyImpureEnc>(task_key.def_id)?
        };
        Ok((output, ()))
    }
}

pub struct ImpureEncVisitor<'vir, 'enc, E: TaskEncoder>
    where 'vir: 'enc
{
    pub vcx: &'vir vir::VirCtxt<'vir>,
    // Are we monomorphizing functions?
    pub monomorphize: bool,
    pub deps: &'enc mut TaskEncoderDependencies<'vir, E>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'vir>,
    //ssa_analysis: SsaAnalysis,
    pub fpcs_analysis: FreePcsAnalysis<'enc, 'vir>,
    pub local_defs: crate::encoders::MirLocalDefEncOutput<'vir>,

    pub tmp_ctr: usize,

    // for the current basic block
    pub current_fpcs: Option<FreePcsBasicBlock<'vir>>,

>>>>>>> ide/rewrite-2023-assistant-features
    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

<<<<<<< HEAD
/// Represents the translation of a MIR place. If the place crosses a shared
/// reference, then we will no longer have a predicate for the `address` Ref,
/// but we do also have the snapshot available.
pub(crate) struct PlaceExpr<'vir> {
    address: vir::ExprRef<'vir>,
    snap: Option<vir::ExprSnap<'vir>>,
}

impl<'vir> PlaceExpr<'vir> {
    /// Expects the encoded place to not be behind a shared ref
    pub(crate) fn expect_predicate(&self) -> vir::ExprRef<'vir> {
        assert!(self.snap.is_none());
        self.address
    }

    pub(crate) fn map(
        self,
        fa: impl FnOnce(vir::ExprRef<'vir>) -> vir::ExprRef<'vir>,
        fs: impl FnOnce(vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir>,
    ) -> Self {
        PlaceExpr {
            address: fa(self.address),
            snap: self.snap.map(fs),
        }
=======
impl<'vir, E: TaskEncoder> PureFuncAppEnc<'vir, E> for ImpureEncVisitor<'vir, '_, E> {
    type EncodeOperandArgs = ();
    type Curr = !;
    type Next = !;
    type LocalDeclsSrc = mir::LocalDecls<'vir>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir> {
        self.vcx
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, E> {
        self.deps
    }

    fn local_decls_src(&self) -> &Self::LocalDeclsSrc {
        self.local_decls
    }

    fn encode_operand(
        &mut self,
        _args: &Self::EncodeOperandArgs,
        operand: &mir::Operand<'vir>,
    ) -> vir::ExprGen<'vir, Self::Curr, Self::Next> {
        self.encode_operand_snap(operand)
>>>>>>> ide/rewrite-2023-assistant-features
    }

    fn monomorphize(&self) -> bool {
        self.monomorphize
    }
}

<<<<<<< HEAD
pub(crate) struct EncodePlaceResult<'vir> {
    pub(crate) expr: PlaceExpr<'vir>,
    pub(crate) ty: mir::PlaceTy<'vir>,
}

macro_rules! comment {
    ($self:tt, $($arg:tt)*) => { $self.comment(
        vir::vir_format!($self.vcx, $($arg)*),
    ) };
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(crate) fn pcg_ctxt(&self) -> CompilerCtxt<'enc, 'vir> {
        self.fpcs_analysis.ctxt()
    }

    // TODO: make `pub(super)`
    pub(crate) fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
        self.current_stmts.as_mut().unwrap().push(stmt);
    }

    fn stmts(&mut self, stmts: impl IntoIterator<Item = vir::Stmt<'vir>>) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }

    fn comment(&mut self, msg: &'vir str) {
        self.stmt(self.vcx.mk_comment_stmt(msg));
    }

    fn ty_use_impure(&mut self, ty: ty::Ty<'vir>) -> TyUseImpure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.def_id);
        self.deps.require_dep::<TyUseImpureEnc>(ty_task).unwrap()
    }

    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.vcx.tcx(), self.def_id);
        self.deps.require_dep::<TyUsePureEnc>(ty_task).unwrap()
    }

=======
struct EncodePlaceResult<'vir> {
    expr: vir::Expr<'vir>,

    /// Statements to undo the impure casts that were made to access the place.
    /// If the place was only accessed to take a snapshot or copy (rather than a
    /// move), these statements should be applied in-order to restore
    /// permissions to the root of the place.
    undo_casts: Vec<vir::Stmt<'vir>>,
}

impl<'vir> EncodePlaceResult<'vir> {
    fn new(expr: vir::Expr<'vir>) -> Self {
        Self { expr, undo_casts: Vec::new() }
    }

    fn map_expr(&mut self, f: impl FnOnce(vir::Expr<'vir>) -> vir::Expr<'vir>) -> &mut Self {
        self.expr = f(self.expr);
        self
    }
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
        self.current_stmts
            .as_mut()
            .unwrap()
            .push(stmt);
    }

>>>>>>> ide/rewrite-2023-assistant-features
    /*
    fn project_fields(
        &mut self,
        mut ty_out: crate::encoders::TyImpureRef<'vir>,
        projection: &'vir ty::List<mir::PlaceElem<'vir>>
    ) -> &'vir [&'vir str] {
        let mut ret = vec![];
        for proj in projection {
            match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::TyImpureEnc>(
                        ty,
                    ).unwrap();
                    ret.push();
                    ty_out = field_ty_out;
                }
                _ => panic!("unsupported projection"),
            }
        }
        ret
        self.vcx.alloc_slice(&projection.iter()
            .map(|proj| match proj {
            }).collect::<Vec<_>>())

        projection.iter()
            .fold((base, ty_out), |(base, ty_out), proj| match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::TyImpureEnc>(
                        ty,
                    ).unwrap();
                    (self.vcx.mk_func_app(
                        ty_out_struct.field_projection_p[f.as_usize()],
                        &[base],
                    ), field_ty_out)
                }
                _ => panic!("unsupported projection"),
            }).0
    }
    */

    /// Do the same as [self.pcs_succ] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_pcs_succ<'a>(
        &mut self,
        state: &Pcg<'_, 'vir>,
        pcs: &'a PcgSuccessor<'_, 'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.pcs_succ(state, pcs);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn block(&mut self, f: impl FnOnce(&mut Self)) -> Vec<vir::Stmt<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        f(self);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    pub(crate) fn pcs_borrow_expansion(
        &mut self,
<<<<<<< HEAD
        expansion: BorrowPcgExpansion<'vir>,
        unfold: bool,
        label: Option<&'vir str>,
    ) {
        // TODO: code duplication with pcs_reborrow_expands
        if expansion.base().place().is_owned(self.pcg_ctxt()) {
            return;
        }
        let base = expansion.base();
        let PcgNode::Place(base) = base else {
            // Ignore expansions of region projections
            return;
        };
        let (place, old) = match base {
            MaybeLabelledPlace::Current(place) => (place, None),
            MaybeLabelledPlace::Labelled(snap) => {
                // We shouldn't be unfolding old places?
                debug_assert!(!unfold);
                (
                    snap.place(),
                    Some(Self::get_location_label(self.vcx, snap.at())),
                )
            }
        };
        if matches!(
            self.local_decls[place.local].ty.kind(),
            ty::TyKind::Ref(_, _, ty::Mutability::Not)
        ) {
            return; // TODO: does this make sense??? we don't want to unfold because for immut refs we only use snapshot read/writes
        }
        let ref_p = self.encode_place(place);
        let place_ty = ref_p.ty;
        let mut ref_p = ref_p.expr.expect_predicate();
        let data = self.ty_use_impure(place_ty.ty);

        if let Some(label) = old {
            ref_p = self.vcx.mk_old(ref_p, label);
        } else if let Some(label) = label {
            ref_p = self.vcx.mk_local_labelled_old_expr(ref_p, label);
        }
        if unfold {
            for stmt in data.unfold(place_ty.variant_index, ref_p, None) {
                self.stmt(stmt);
            }
        } else {
            for stmt in data.fold(place_ty.variant_index, ref_p, None) {
                self.stmt(stmt);
            }
        }
    }

    fn pcs_handle_edge(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) {
        let conditions = edge.conditions();

        // For each block `b` where the edge is only valid if control flow
        // continues from `b` to a specified subset of its successors, `cond`
        // contains the corresponding VIR expression.
        let cond = conditions
            .all_branch_choices()
            .map(|choices| {
                let successors = choices.successors(self.body);
                let from = choices.from();
                let conj = successors
                    .iter()
                    .map(|to| {
                        let decl = self
                            .from_to_vars
                            .get(&from)
                            .and_then(|tos| tos.iter().find(|(t, _)| t == to))
                            .map(|(_, decl)| *decl);
                        let decl = decl.unwrap_or_else(|| {
                            let name = vir::vir_format!(
                                self.vcx,
                                "_from_bb{}_to_bb{}",
                                from.index(),
                                to.index()
                            );
                            self.vcx.mk_local_decl(name, vir::TYPE_BOOL)
                        });
                        self.vcx.mk_local_ex(decl)
                    })
                    .collect::<Vec<_>>();
                // Control flow must continue from `choices.from()` to any one of the `successors`
                self.vcx.mk_disj(self.vcx.alloc_slice(&conj))
            })
            .collect::<Vec<_>>();
        // For each block `b` where the edge validity depends on the successor taken from `b`,
        // every successor must be valid.
        let cond = self.vcx.mk_conj(self.vcx.alloc_slice(&cond));
        let stmts = self.block(|self_| {
            self_.pcs_handle_edge_conditionless(
                borrows_state,
                edge,
                add,
                label,
                edge_to_loop,
                to_skip,
            )
        });
        if stmts.is_empty()
            || stmts
                .iter()
                .all(|stmt| matches!(stmt.kind, vir::StmtKindData::Comment(_)))
        {
            self.stmts(stmts);
            return;
        }
        let stmts = self.vcx.alloc_slice(&stmts);
        self.stmt(self.vcx.mk_if_stmt(cond, stmts, &[]));
    }

    fn pcs_handle_edge_conditionless(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        edge: &BorrowPcgEdge<'vir>,
        add: bool,
        label: Option<&'vir str>,
        edge_to_loop: bool,
        to_skip: &mut Vec<mir::BasicBlock>,
    ) {
        match edge.kind() {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                self.pcs_borrow_expansion(expansion.clone(), add, label);
            }
            BorrowPcgEdgeKind::Coupled(PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(
                call_edge,
            ))) => {
                if add {
                    // The wand will be introduced by the method call itself.
                    return;
                }
                let call = call_edge.metadata();
                // We may be encoding multiple edges as a single wand, skip
                // further edge removals. This is a hack to get around the fact
                // that Viper doesn't support hyperwands.
                if to_skip.contains(&call.location().block) {
                    return;
                }
                to_skip.push(call.location().block);
                // TODO: this applies *all* the wands for the referenced
                //   function call; instead we should figure out which
                //   wand it is based on the edge info.
                // TODO: closures
                let wands = self
                    .deps
                    .require_dep::<WandEnc>(WandEncTask {
                        data: call.function_data().unwrap(),
                    })
                    .unwrap();
                let bb = &self.body[call.location().block];
                let terminator = bb.terminator.as_ref().unwrap();
                match &terminator.kind {
                    mir::TerminatorKind::Call {
                        args, destination, ..
                    } => {
                        let (_, dest_snap, _, _) = self.encode_place_snap((*destination).into());
                        let wand_args =
                            std::iter::once(dest_snap)
                                .chain(args.iter().map(|operand| {
                                    self.encode_operand_snap_immediate(&operand.node)
                                }))
                                .collect::<Vec<_>>();
                        let (label_pre, label_post) = self.call_labels[&call.location().block];
                        wands.apply_wands(&wand_args, label_pre, label_post, self);
                    }
                    _ => unreachable!(),
                }
            }
            BorrowPcgEdgeKind::Abstraction(at @ AbstractionEdge::Loop(_)) => {
                self.pcs_handle_wand(
                    borrows_state,
                    add,
                    &at.clone().into_singleton_coupled_edge(),
                    label,
                    edge_to_loop,
                );
            }
            other => comment!(self, "(ignoring) {other:?}"),
        }
    }

    pub(crate) fn pcs_unblock_actions(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        actions: &[BorrowPcgUnblockAction<'vir>],
        label: Option<&'vir str>,
    ) {
        let mut to_skip = Vec::new();
        for action in actions {
            self.pcs_handle_edge(
                borrows_state,
                action.edge(),
                false,
                label,
                false,
                &mut to_skip,
            );
        }
    }

    fn pcg_actions(&mut self, pcg: &Pcg<'_, 'vir>, actions: &PcgActions<'vir>, edge_to_loop: bool) {
        for action in actions.iter() {
            match action {
                PcgAction::Borrow(action) => self.borrow_action(pcg, action, edge_to_loop),
                PcgAction::Owned(action) => self.pcg_repack(action.kind()),
            }
        }
    }
    fn borrow_action(
        &mut self,
        pcg: &Pcg<'_, 'vir>,
        action: &BorrowPcgAction<'vir>,
        edge_to_loop: bool,
    ) {
        let mut to_skip = Vec::new();
        match action.kind() {
            //Weaken(Weaken<'tcx>),
            //Restore(RestoreCapability<'tcx>),
            //MakePlaceOld(Place<'tcx>),
            //SetLatest(Place<'tcx>, Location),
            //AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
            BorrowPcgActionKind::RemoveEdge(edge) => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                false,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            BorrowPcgActionKind::AddEdge { edge } => self.pcs_handle_edge(
                pcg.borrow_pcg(),
                edge,
                true,
                None,
                edge_to_loop,
                &mut to_skip,
            ),
            //RenamePlace {
            //    old: MaybeLabelledPlace<'tcx>,
            //    new: MaybeLabelledPlace<'tcx>,
            //},
            other => comment!(self, "(ignoring) {other:?}"),
        }
    }

    fn pcg_repack(&mut self, repack_op: &RepackOp<'vir>) {
        comment!(self, "[PCG] {repack_op:?}");
        match repack_op {
            RepackOp::Expand(_) | RepackOp::Collapse(_) => {
                let (place, capability_kind) = match repack_op {
                    RepackOp::Expand(expand) => (expand.from(), expand.capability()),
                    RepackOp::Collapse(collapse) => (collapse.to(), collapse.capability()),
                    _ => unreachable!(),
                };
                if matches!(capability_kind, CapabilityKind::Write) {
                    // Collapsing an already exhaled place is a no-op
                    // TODO: unless it's through a Ref I imagine?
                    //assert!(matches!(repack_op, RepackOp::Collapse(..)));
                    if !matches!(repack_op, RepackOp::Collapse(..)) {
                        comment!(self, "expected RepackOp::Collapse but got {repack_op:?}");
                    }
                    return;
                }
                let place_enc = self.encode_place(place);
                let place_ty = place_enc.ty;
                let place_enc = place_enc.expr.expect_predicate();
                let data = self.ty_use_impure(place_ty.ty);
                if matches!(repack_op, pcg::free_pcs::RepackOp::Expand(..)) {
                    for stmt in data.unfold(place_ty.variant_index, place_enc, None) {
                        self.stmt(stmt);
                    }
                } else {
                    for stmt in data.fold(place_ty.variant_index, place_enc, None) {
                        self.stmt(stmt);
                    }
                }
            }
            RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                let place_ty = (*place).ty(self.pcg_ctxt());
                assert!(place_ty.variant_index.is_none());

                let place_ty_out = self.ty_use_impure(place_ty.ty);

                let place_enc = self.encode_place(*place);
                comment!(self, "exhale due to Weaken(E, W)");
                self.stmt(self.vcx.mk_exhale_stmt(place_ty_out.ref_to_pred(
                    self.vcx,
                    place_enc.expr.expect_predicate(),
                    None,
                )));
            }
            ignored_op @ (RepackOp::RegainLoanedCapability(..)
            | RepackOp::Weaken(_, CapabilityKind::Exclusive, CapabilityKind::Read)) => {
                self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                    self.vcx,
                    "ignored repack op: {ignored_op:?}"
                )));
            }
            unsupported_op => {
                self.stmt(self.vcx.mk_comment_stmt(vir::vir_format!(
                    self.vcx,
                    "unsupported repack op: {unsupported_op:?}"
                )));
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
            }
        }
    }

    fn loop_analysis(&mut self) -> &LoopAnalysis {
        self.fpcs_analysis.analysis().loop_analysis()
    }

    fn loop_place_usages(&mut self, block: mir::BasicBlock) -> Option<PlaceUsages<'vir>> {
        self.fpcs_analysis
            .analysis()
            .loop_place_usages(block)
            .cloned()
    }

    fn loop_head_of(&mut self, block: mir::BasicBlock) -> Option<LoopId> {
        self.loop_analysis().loop_head_of(block)
    }

    fn pcs_succ<'a>(&mut self, pcg_state: &Pcg<'_, 'vir>, succ: &'a PcgSuccessor<'_, 'vir>) {
        let edge_to_loop = self.loop_head_of(succ.block()).is_some();
        self.pcg_actions(pcg_state, succ.actions(), edge_to_loop);
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'vir>) -> vir::ExprSnap<'vir> {
        match operand {
            &mir::Operand::Move(source) => {
                let (result, snap_val, _, ty_out) = self.encode_place_snap(Place::from(source));

                let tmp_exp = self.new_tmp(ty_out.snapshot());
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(self.vcx.mk_exhale_stmt(ty_out.ref_to_pred(
                    self.vcx,
                    result.expr.expect_predicate(),
                    None,
                )));
                tmp_exp
            }
            &mir::Operand::Copy(place) => self.encode_place_snap(place.into()).1,
            mir::Operand::Constant(box constant) => self.encode_constant(constant).upcast_ty(),
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'vir>) -> vir::ExprRef<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => {
                return self
                    .encode_place(Place::from(source))
                    .expr
                    .expect_predicate();
            }
            &mir::Operand::Copy(_source) => {
                let ty_out = self.ty_use_impure(ty);
                (self.encode_operand_snap(operand), ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.ty_use_impure(ty);
                let constant = self.encode_constant(constant);
                (constant.upcast_ty(), ty_out)
            }
        };
        let tmp_exp: vir::ExprRef<'vir> = self.new_tmp(vir::TYPE_REF);
        self.stmt(ty_out.apply_method_assign(self.vcx, tmp_exp, encode_place_result));
=======
        repacks: &[RepackOp<'vir>],
    ) {
        for &repack_op in repacks {
            match repack_op {
                RepackOp::Expand(place, _target, capability_kind)
                | RepackOp::Collapse(place, _target, capability_kind) => {
                    if matches!(capability_kind, CapabilityKind::Write) {
                        // Collapsing an already exhaled place is a no-op
                        // TODO: unless it's through a Ref I imagine?
                        assert!(matches!(repack_op, RepackOp::Collapse(..)));
                        return;
                    }
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    let place_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                    let ref_to_pred = place_ty_out
                        .generic_predicate
                        .expect_pred_variant_opt(place_ty.variant_index);

                    let ref_p = self.encode_place(place).expr;
                    let args = place_ty_out.ref_to_args(self.vcx, ref_p);
                    let predicate = ref_to_pred.apply(self.vcx, &args, None);
                    if matches!(
                        repack_op,
                        mir_state_analysis::free_pcs::RepackOp::Expand(..)
                    ) {
                        self.stmt(self.vcx.mk_unfold_stmt(predicate));
                    } else {
                        self.stmt(self.vcx.mk_fold_stmt(predicate));
                    }
                }
                RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    assert!(place_ty.variant_index.is_none());

                    let place_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();

                    let ref_p = self.encode_place(place).expr;
                    self.stmt(
                        self.vcx
                            .mk_exhale_stmt(place_ty_out.ref_to_pred(self.vcx, ref_p, None)),
                    );
                }
                unsupported_op => panic!("unsupported repack op: {unsupported_op:?}"),
            }
        }
    }

    fn fpcs_repacks_location(
        &mut self,
        location: mir::Location,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let repacks = repacks(&current_fpcs.statements[location.statement_index]);
        self.fpcs_repacks(repacks);
        self.current_fpcs = Some(current_fpcs);
    }

    fn fpcs_repacks_terminator(
        &mut self,
        succ_idx: usize,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let repacks = repacks(&current_fpcs.terminator.succs[succ_idx]);
        self.fpcs_repacks(repacks);
        self.current_fpcs = Some(current_fpcs);
    }

    fn undo_impure_casts(&mut self, result: EncodePlaceResult<'vir>) {
        result.undo_casts.iter().for_each(|stmt| self.stmt(stmt));
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'vir>) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        match operand {
            &mir::Operand::Move(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let result = self.encode_place(Place::from(source));
                let snap_val = ty_out.ref_to_snap(self.vcx, result.expr);

                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(
                    self.vcx
                        .mk_exhale_stmt(ty_out.ref_to_pred(self.vcx, result.expr, None)),
                );
                tmp_exp
            }
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let result = self.encode_place(Place::from(source));
                let snap_val = ty_out.ref_to_snap(self.vcx, result.expr);
                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.undo_impure_casts(result);
                tmp_exp
            }
            mir::Operand::Constant(box constant) => self
                .deps
                .require_local::<ConstEnc>((constant.literal, 0, self.def_id))
                .unwrap(),
        }
    }

    fn encode_operand(
        &mut self,
        operand: &mir::Operand<'vir>,
    ) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)).expr,
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let mut result = self.encode_place(Place::from(source));
                result.map_expr(|e| ty_out.ref_to_snap(self.vcx, e));
                (result, ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let constant = self.deps.require_local::<ConstEnc>((constant.literal, 0, self.def_id)).unwrap();
                (EncodePlaceResult::new(constant), ty_out)
            }
        };
        let tmp_exp: vir::Expr<'vir> = self.new_tmp(&vir::TypeData::Ref).1;
        self.stmt(ty_out.apply_method_assign(self.vcx, tmp_exp, encode_place_result.expr));
        self.undo_impure_casts(encode_place_result);
>>>>>>> ide/rewrite-2023-assistant-features
        tmp_exp
    }

    /// Encodes the snapshot of an operand. This should not be used for encoding
    /// regular mir statements/terminators as it doesn't match the semantics.
    fn encode_operand_snap_immediate(
        &mut self,
<<<<<<< HEAD
        operand: &mir::Operand<'vir>,
    ) -> vir::ExprSnap<'vir> {
        match operand {
            &mir::Operand::Move(source) => self.encode_place_snap(Place::from(source)).1,
            &mir::Operand::Copy(source) => self.encode_place_snap(Place::from(source)).1,
            mir::Operand::Constant(box constant) => self.encode_constant(constant).upcast_ty(),
        }
    }

    fn encode_constant(&mut self, constant: &mir::ConstOperand<'vir>) -> vir::ExprCSnap<'vir> {
        self.deps
            .require_dep::<ConstEnc>(ConstEncTask::Mir {
                const_: constant.const_,
                encoding_depth: 0,
                def_id: self.def_id,
            })
            .unwrap()
    }

    pub(crate) fn encode_place(&mut self, place: Place<'vir>) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut encoded_place = mir::Place::from(place.local);
        let mut result = PlaceExpr {
            address: self.local_defs[place.local].local_ex,
            snap: None,
        };
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            result = self.encode_place_element(place_ty, elem, result);
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
            encoded_place = encoded_place.project_deeper(&[elem], self.vcx.tcx());
        }
        EncodePlaceResult {
            expr: result,
            ty: place_ty,
        }
    }

    pub(crate) fn encode_place_snap(
        &mut self,
        place: Place<'vir>,
    ) -> (
        EncodePlaceResult<'vir>,
        vir::ExprSnap<'vir>,
        mir::PlaceTy<'vir>,
        TyUseImpure<'vir>,
    ) {
        let ty = (*place).ty(self.local_decls, self.vcx.tcx());
        assert!(ty.variant_index.is_none());

        let ty_out = self.ty_use_impure(ty.ty);
        let result = self.encode_place(place);
        let snap = result
            .expr
            .snap
            .unwrap_or_else(|| ty_out.ref_to_snap(result.expr.address));
        (result, snap, ty, ty_out)
    }

    fn encode_place_element(
        &mut self,
        place_ty: mir::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: PlaceExpr<'vir>,
    ) -> PlaceExpr<'vir> {
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self.ty_use_impure(place_ty.ty);
                let field_access = e_ty.expect_variant_opt(place_ty.variant_index);
                expr.map(
                    |r| field_access[field_idx].field_ref(r),
                    |snap| {
                        let e_ty = self.ty_use_pure(place_ty.ty);
                        let field_access = e_ty.expect_variant_opt(place_ty.variant_index);
                        field_access[field_idx].read(snap.downcast_ty())
                    },
                )
=======
        place: Place<'vir>,
    ) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut result = EncodePlaceResult::new(self.local_defs.locals[place.local].local_ex);
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            let (expr, unapply_cast_stmt) = self.encode_place_element(place_ty, elem, result.expr);
            result.expr = expr;
            if let Some(stmt) = unapply_cast_stmt {
                result.undo_casts.push(stmt);
            }
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
        }
        result
    }

    // Returns a tuple (expr, unapply_cast), where `expr` is the encoded place element,
    // and `unapply_cast` is a statement to undo the impure cast that was made to access
    // it.
    fn encode_place_element(
        &mut self,
        place_ty: mir::tcx::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        expr: vir::Expr<'vir>
    ) -> (vir::Expr<'vir>, Option<vir::Stmt<'vir>>) {
        match elem {
            mir::ProjectionElem::Field(field_idx, ty) => {
                let e_ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                let field_access = e_ty
                    .generic_predicate
                    .expect_variant_opt(place_ty.variant_index)
                    .ref_to_field_refs;
                let projection_p = field_access[field_idx.as_usize()];
                let proj_app = projection_p.apply(self.vcx, [expr]);
                let mut unapply_cast_stmt = None;
                match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant = def.variant(place_ty.variant_index.unwrap_or(
                            abi::FIRST_VARIANT
                        ));
                        let generic_field_ty = variant.fields[field_idx].ty(
                            self.vcx.tcx(),
                            GenericArgs::identity_for_item(self.vcx.tcx(), def.did())
                        );
                        let cast_args = CastArgs {
                            expected: ty,
                            actual: generic_field_ty
                        };
                        if let Some(cast) = self
                            .deps.require_ref::<CastToEnc<CastTypeImpure>>(cast_args)
                            .unwrap().apply_cast_if_necessary(self.vcx, proj_app) {
                                self.stmt(cast);
                                unapply_cast_stmt = self
                                    .deps
                                    .require_ref::<CastToEnc<CastTypeImpure>>(cast_args.reversed())
                                    .unwrap().apply_cast_if_necessary(self.vcx, proj_app);
                        }
                    }
                    TyKind::Tuple(_) => {
                        if let Some(cast_stmts) = self
                            .deps.require_local::<RustTyCastersEnc<CastTypeImpure>>(ty)
                            .unwrap().cast_to_concrete_if_possible(self.vcx, proj_app) {
                                self.stmt(cast_stmts.apply_cast_stmt);
                                unapply_cast_stmt = Some(cast_stmts.unapply_cast_stmt);
                        }
                    }
                    _ => {}
                }
                (proj_app, unapply_cast_stmt)
>>>>>>> ide/rewrite-2023-assistant-features
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => (expr, None),
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
<<<<<<< HEAD
                let e_ty = self.ty_use_impure(place_ty.ty);
                match place_ty.ty.kind() {
                    ty::TyKind::Adt(adt, _) if adt.is_box() => {
                        let field_access = e_ty.expect_variant_opt(None);
                        expr.map(
                            // TODO: this is unsound: a Box should be modelled
                            // with a Ref field rather than a field_access
                            // function.
                            |r| field_access[abi::FieldIdx::ZERO].field_ref(r),
                            |snap| {
                                let e_ty = self.ty_use_pure(place_ty.ty);
                                let field_access = e_ty.expect_variant_opt(None);
                                field_access[abi::FieldIdx::ZERO].read(snap.downcast_ty())
                            },
                        )
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Not) => {
                        let snap = expr
                            .snap
                            .unwrap_or_else(|| e_ty.ref_to_snap(expr.address))
                            .downcast_ty();
                        let p_ty = self.ty_use_pure(place_ty.ty).expect_immref();
                        PlaceExpr {
                            address: p_ty.deref_access(snap),
                            snap: Some(p_ty.value_access(snap)),
                        }
                    }
                    ty::TyKind::Ref(_, _, ty::Mutability::Mut) => {
                        if let Some(snap) = expr.snap {
                            let snap = snap.downcast_ty();
                            let p_ty = self.ty_use_pure(place_ty.ty).expect_mutref();
                            PlaceExpr {
                                address: p_ty.deref_access(snap),
                                snap: Some(p_ty.value_access(snap)),
                            }
                        } else {
                            PlaceExpr {
                                address: e_ty.expect_mutref().deref(expr.address),
                                snap: None,
                            }
                        }
                    }
                    _ => unreachable!(),
                }
=======
                let e_ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                let ref_field = e_ty.generic_predicate.expect_ref().ref_field;
                let expr = self.vcx.mk_field_expr(expr, ref_field);
                let inner_ty = place_ty.ty.builtin_deref(true).unwrap().ty;
                if let Some(cast_stmts) = self
                    .deps.require_local::<RustTyCastersEnc<CastTypeImpure>>(inner_ty)
                    .unwrap().cast_to_concrete_if_possible(self.vcx, expr) {
                        self.stmt(cast_stmts.apply_cast_stmt);
                        return (expr, Some(cast_stmts.unapply_cast_stmt));
                }
                (expr, None)
>>>>>>> ide/rewrite-2023-assistant-features
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp<T: CompType>(&mut self, ty: vir::Type<'vir, T>) -> vir::Expr<'vir, T> {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        let local = vir::vir_local_decl! { self.vcx; [name] : [ty] };
        self.tmp_ctr += 1;
        self.stmt(self.vcx.mk_local_decl_stmt(local, None));
        self.vcx.mk_local_ex(local)
    }

    pub(crate) fn new_label(&mut self, base: &str) -> &'vir str {
        let name = vir::vir_format!(self.vcx, "{base}{}", self.label_ctr);
        self.label_ctr += 1;
        self.stmt(self.vcx.mk_label_stmt(name));
        name
    }

    fn new_after_label(&mut self, location: mir::Location) {
        let name = vir::vir_format!(
            self.vcx,
            "_after_{}_{}",
            location.block.index(),
            location.statement_index
        );
        self.stmt(self.vcx.mk_label_stmt(name));
    }

    fn set_from_to_flag(&mut self, from: mir::BasicBlock, to: mir::BasicBlock) -> vir::Stmt<'vir> {
        let name = vir::vir_format!(self.vcx, "_from_bb{}_to_bb{}", from.index(), to.index());
        let decl = self.vcx.mk_local_decl(name, vir::TYPE_BOOL);
        let tos = self.from_to_vars.entry(from).or_default();
        debug_assert!(!tos.contains(&(to, decl)));
        tos.push((to, decl));
        let local = self.vcx.mk_local_ex(decl);
        self.vcx
            .mk_pure_assign_stmt(local, self.vcx.mk_bool::<true>())
    }
}

impl<'vir, 'enc, E: TaskEncoder> mir::visit::Visitor<'vir> for ImpureEncVisitor<'vir, 'enc, E> {
<<<<<<< HEAD
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'vir>) {
        // We are verifying the absence of panics, so cleanup block should never
        // be reached, or even referenced.
        if data.is_cleanup {
            self.encoded_blocks.push(
                self.vcx.mk_cfg_block(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
                    &[],
                    &[],
                    self.vcx
                        .mk_dummy_stmt(vir::vir_format!(self.vcx, "cleanup block")),
                ),
            );
            return;
        }
        if self.deps.check_cycle().is_err() {
            return;
        }
=======
    // fn visit_body(&mut self, body: &mir::Body<'tcx>) {
    //     println!("visiting body!");
    // }
    fn visit_basic_block_data(
        &mut self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'vir>,
    ) {
        self.current_fpcs = Some(self.fpcs_analysis.get_all_for_bb(block));
>>>>>>> ide/rewrite-2023-assistant-features

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        self.current_block_label = Some(
            self.vcx
                .alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
        );
        let cfpcs = self.fpcs_analysis.get_all_for_bb(block).unwrap().unwrap();

        // Calculate invariant at loop head
        let invariant = self
            .loop_place_usages(block)
            .map(|place_usages| self.get_loop_inv(&cfpcs, &place_usages, self.pcg_ctxt()))
            .unwrap_or_default();

        self.current_fpcs = Some(cfpcs);

        /*
        let mut phi_stmts = vec![];
        if let Some(phi_nodes) = self.ssa_analysis.phi.get(&block) {
            for phi_node in phi_nodes {
                assert!(!phi_node.sources.is_empty());
                let local_ty = &self.local_types[phi_node.local];
                let expr = phi_node.sources.iter()
                    .fold(self.vcx.mk_func_app(
                        local_ty.function_unreachable,
                        &[],
                    ), |prev, source| self.vcx.alloc(vir::ExprData::Ternary(self.vcx.alloc(vir::TernaryData {
                        cond: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
                    ty: self.local_types[phi_node.local].snapshot,
                    expr: Some(expr),
                })));
            }
        }
        for phi_stmt in phi_stmts {
            self.stmt(phi_stmt);
        }
        */

        assert!(self.current_terminator.is_none());
        self.super_basic_block_data(block, data);
        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
<<<<<<< HEAD
        self.encoded_blocks.push(self.vcx.mk_cfg_block(
            self.current_block_label.take().unwrap(),
            invariant,
            self.vcx.alloc_slice(&stmts),
            terminator,
        ));
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'vir>, location: mir::Location) {
        if self.deps.check_cycle().is_err() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {statement:?}");

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false);
        }
        self.current_fpcs = Some(current_fpcs);

=======

        // Register the spans of individual blocks. Since these ranges are supposed to give an idea
        // of the more granular range of what has been verified already, we need to filter them a bit.
        if prusti_utils::config::report_block_messages() {
            let stmt_count = data.statements.len();
            if stmt_count > 0 {
                debug!("bb_{}", block.as_usize());
                let terminator = data.terminator.as_ref().unwrap();
                // TODO more (or more precise) filters may be needed
                // note that if there is a possibility for errors to occur in blocks that do not end up having
                // any spans, this will cause that the block messages finally emitted do not show this error.
                // so some care is needed (how should the ranges of such blocks be reported?).
                let terminator_span = match terminator.kind {
                // Terminator kinds: https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/syntax/enum.TerminatorKind.html
                // `Goto` may have large ranges (yet to figure out what the ranges really refer to)
                // `SwitchInt` seem to cover a condition, a `match expr` or an `assert!` argument, which is ok
                // `UnwindResume` not observed but probably similar to `Return`
                // `UnwindTerminate` not observed but probably similar to `Return`
                //
                // `Return` may include the end of a method body, including the braces (and a column past it).
                // According to my observations, if there are actual statements or expressions associated with
                // the return (as in `return val;`), the ranges thereof are in the block statements. So we can
                // skip these.
                //
                // `Unreachable` not observed.
                // `Drop` seems to just cover the end of a method similar to what `Return` may do. Only observed
                // one case though.
                //
                // `Call` includes the span of the call, which may not be included in any statements of the block
                // so we need to include these spans.
                // `TailCall` is not present in the rust version we use?
                //
                // `Assert` are not `assert!` calls. These are compiler inserted and seem to have the range of
                // the statements or expressions that trigger them to be inserted. E.g. this may be an overflow
                // check on the range of `+1` in an expression `var+1`. In this case the span is also included in
                // block statements. Are there examples where they are not/where `Assert` has problematic spans?
                //
                // `Yield` not observed. Should be like `Return` in terms of spans?
                // `CoroutineDrop` not observed. Should be like `Return` in terms of spans?
                //
                // `FalseEdge` not observed. The description states it behaves like a goto, so assuming the same
                // for associated spans. They do occur in the .vpr file but the blocks don't seem to pass through
                // here.
                // `FalseUnwind` not observed. They do occur in the .vpr file but the blocks don't seem to pass
                // through here.
                //
                // `InlineAsm` not observed
                //
                    mir::TerminatorKind::Call {..} => Some(terminator.source_info.span),
                    _ => None,
                };
                debug!("{}terminator: --{:?}--", if terminator_span.is_none() {"(ignored) "} else {""}, data.terminator);
                let block_span = data
                    .statements
                    .iter()
                    .fold(terminator_span, |acc, stmt| {
                        // Statement kinds: https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/syntax/enum.StatementKind.html
                        // Some statements include excessively large ranges, so we try to filter them out.
                        //
                        // `Assign` sometimes occurs in the form `lval = const ()`. These assignments (according to inexhaustive observation)
                        // either refer to small ranges that are contained in other statements of the block or to large, encompassing ones.
                        // Sometimes even the entire method body or if-else statements. The lvals of these assignments, from my observation,
                        // only seem to occur in `StorageDead` & `StorageLive` statements.
                        // Might be generalizing too much. If there are unit assignments that have a relevant local range, they should be included.
                        // Could other rvalues also be problematic?
                        // Rvalues: https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/syntax/enum.Rvalue.html
                        //
                        // `FakeRead` may be problematic. e.g. `FakeRead(ForLet(None), _2)` seems to have the range of where `_2` was defined
                        //  (same range as the corresponding `StorageLive`). Which means this range may go outside the current block.
                        // `FakeRead(ForMatchedPlace(None), _2)` on the other hand, seems to cover the range of a statement to be matched rather
                        // than the definition (using `let`) of `_2`. But this range is also covered by an assignment like `_4 = discriminant(_2)`.
                        //
                        // `SetDiscriminant` not observed (should be ok?)
                        // `Deinit` not observed
                        //
                        // `StorageLive` & `StorageDead` may cover ranges that cover entire statement blocks or branching statements
                        // like if-else. Additionally, `StorageDead` often refers to places of variables outside the current block.
                        // They aren't really relevant to user provided code locations anyhow, should be save to skip.
                        //
                        // `Retag` not observed (requires `-Z mir-emit-retag`) but should not cause errors and are not part of user code
                        // `PlaceMention` seems ok (observed to range over the rvalue inline, not definition place)
                        // `AscribeUserType` seems ok
                        // `Coverage` not observed (requires `-Cinstrument-coverage`) but should not cause errors and are not part of user code
                        // `Intrinsic` not observed
                        // `ConstEvalCounter` not observed (but probably not part of user code?)
                        // `Nop` not observed
                        //
                        match &stmt.kind {
                            mir::StatementKind::Assign(box (_, mir::Rvalue::Use(operand))) => {
                                let constant = operand.constant();
                                if let Some(constant) = constant {
                                    if constant.ty().is_unit() {
                                        debug!("(ignored) stmt: --{:?}--({:?}) with span: {:?}", stmt, stmt.kind.name(), stmt.source_info.span);
                                        return acc;
                                    }
                                }
                                debug!("stmt: --{:?}--({:?}) with span: {:?}", stmt, stmt.kind.name(), stmt.source_info.span);
                                acc.map_or(Some(stmt.source_info.span), |acc| Some(acc.to(stmt.source_info.span)))
                            },
                            mir::StatementKind::FakeRead(..) |
                            mir::StatementKind::StorageLive(..) |
                            mir::StatementKind::StorageDead(..) |
                            mir::StatementKind::Retag(..) |
                            mir::StatementKind::Coverage(..) |
                            mir::StatementKind::ConstEvalCounter => {
                                debug!("(ignored) stmt: --{:?}--({:?}) with span: {:?}", stmt, stmt.kind.name(), stmt.source_info.span);
                                acc
                            },
                            _ => {
                                debug!("stmt: --{:?}--({:?}) with span: {:?}", stmt, stmt.kind.name(), stmt.source_info.span);
                                acc.map_or(Some(stmt.source_info.span), |acc| Some(acc.to(stmt.source_info.span)))
                            }
                        }
                });
                let label = format!("bb_{}", block.as_usize());
                if let Some(block_span) = block_span{
                    self.vcx.insert_block_span((self.def_id, label), block_span);
                } else {
                    debug!("no spans for block {label}!");
                }
            }
        }

        self.encoded_blocks.push(
            self.vcx.mk_cfg_block(
                self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
                self.vcx.alloc_slice(&stmts),
                terminator
            )
        );
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'vir>,
        location: mir::Location,
    ) {
>>>>>>> ide/rewrite-2023-assistant-features
        // TODO: these should not be ignored, but should havoc the local instead
        // This clears up the noise a bit, making sure StorageLive and other
        // kinds do not show up in the comments.
        // TODO: also make sure we don't ignore PCG annotations for these,
        //   *if* the pcs calls for mid-statement are moved later.
        const IGNORE_NOP_STMTS: bool = true;
        if IGNORE_NOP_STMTS {
            match &statement.kind {
                mir::StatementKind::StorageLive(..) | mir::StatementKind::StorageDead(..) => {
                    return;
                }
                _ => {}
            }
        }

        let span = statement.source_info.span;

        match &statement.kind {
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                // What are we assigning to?
<<<<<<< HEAD
                let proj_enc = self
                    .encode_place(Place::from(*dest))
                    .expr
                    .expect_predicate();
=======
                let proj_ref = self.encode_place(Place::from(*dest)).expr;
>>>>>>> ide/rewrite-2023-assistant-features

                let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());

                // The snapshot of the value that we are assigning.
                let rval_enc = match rvalue {
                    mir::Rvalue::Use(op) => Some(self.encode_operand_snap(op)),

                    //mir::Rvalue::Repeat(Operand<'vir>, Const<'vir>) => {}
<<<<<<< HEAD
=======
                    //mir::Rvalue::Ref(Region<'vir>, BorrowKind, Place<'vir>) => {}
>>>>>>> ide/rewrite-2023-assistant-features
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'vir>) => {}
                    //mir::Rvalue::Len(Place<'vir>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'vir>, Ty<'vir>) => {}
<<<<<<< HEAD
                    mir::Rvalue::BinaryOp(op, box (l, r)) => {
=======

                    rv@mir::Rvalue::BinaryOp(op, box (l, r)) |
                    rv@mir::Rvalue::CheckedBinaryOp(op, box (l, r)) => {
>>>>>>> ide/rewrite-2023-assistant-features
                        let l_ty = l.ty(self.local_decls, self.vcx.tcx());
                        let r_ty = r.ty(self.local_decls, self.vcx.tcx());
                        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
                        let task = if op.is_overflowing() {
                            CheckedBinOp(rvalue_ty, *op, l_ty, r_ty)
                        } else {
                            BinOp(rvalue_ty, *op, l_ty, r_ty)
                        };
                        let binop_function = self
                            .deps
                            .require_ref::<MirBuiltinEnc>(task)
                            .unwrap()
                            .bin_op()
                            .unwrap();
                        Some(
                            binop_function(
                                self.encode_operand_snap(l).downcast_ty(),
                                self.encode_operand_snap(r).downcast_ty(),
                            )
                            .upcast_ty(),
                        )
                    }

                    //mir::Rvalue::NullaryOp(NullOp, Ty<'vir>) => {}
<<<<<<< HEAD
=======

>>>>>>> ide/rewrite-2023-assistant-features
                    mir::Rvalue::UnaryOp(unop, operand) => {
                        let operand_ty = operand.ty(self.local_decls, self.vcx.tcx());
                        let unop_function = self
                            .deps
                            .require_ref::<MirBuiltinEnc>(crate::encoders::MirBuiltinEncTask::UnOp(
                                rvalue_ty, *unop, operand_ty,
                            ))
                            .unwrap()
                            .un_op()
                            .unwrap();
                        Some(
                            unop_function(self.encode_operand_snap(operand).downcast_ty())
                                .upcast_ty(),
                        )
                        /*
                        assert!(source.projection.is_empty());
                        let source_version = self.ssa_analysis.version.get(&(location, source.local)).unwrap();
                        let source_name = vir::vir_format_identifier!(self.vcx, "_{}s_{}", source.local.index(), source_version);

                        let unop_function = self.deps.require_ref::<crate::encoders::MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                *unop,
                                source.ty(self.local_decls, self.vcx.tcx()).ty,
                            ),
                        ).unwrap().name;
                        Some(self.vcx.mk_func_app(
                            unop_function,
                            &[self.vcx.mk_local_ex(source_name)],
                        ))*/
                    }

                    mir::Rvalue::Aggregate(
                        box kind @ (mir::AggregateKind::Adt(..) | mir::AggregateKind::Tuple),
                        fields,
                    ) => {
                        let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                        let sl = match kind {
                            mir::AggregateKind::Adt(_, vidx, _, _, _) => {
                                e_rvalue_ty.get_variant_any(*vidx)
                            }
                            _ => e_rvalue_ty.expect_structlike(),
                        };
                        // let field_tys = fields.iter()
                        //     .map(|field| {
                        //         let ty = field.ty(self.local_decls, self.vcx.tcx());
                        //         self.deps.require_dep::<RustTyCastersEnc<CastTypePure>>(ty).unwrap()
                        //     })
                        //     .collect::<Vec<_>>();
                        // let ty_caster = self.deps.require_dep::<AggregateSnapArgsCastEnc>(
                        //     AggregateSnapArgsCastEncTask {
                        //         tys: field_tys,
                        //         aggregate_type: kind.into()
                        //     }
                        // ).unwrap();
                        let field_snaps = fields
                            .iter()
                            .map(|field| self.encode_operand_snap(field))
                            .collect::<Vec<_>>();
                        // let casted_args = ty_caster.apply_casts(self.vcx, field_snaps.into_iter());
                        Some(sl.field_snaps_to_snap(field_snaps).upcast_ty())
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx());
<<<<<<< HEAD
                        let ty = self.ty_use_impure(place_ty.ty);
                        let place_expr = self.encode_place(Place::from(*place)).expr;

                        Some(
                            match ty
                                .get_enumlike()
                                .filter(|_| place_ty.variant_index.is_none())
                            {
                                Some(el) => {
                                    if let Some(snap) = place_expr.snap {
                                        let ty = self.ty_use_pure(place_ty.ty).expect_enumlike();
                                        ty.snap_to_discr_snap(snap.downcast_ty())
                                    } else {
                                        let place_expr = place_expr.expect_predicate();
                                        self.vcx.mk_unfolding_expr(
                                            ty.ref_to_pred_app(
                                                place_expr,
                                                Some(self.vcx.mk_wildcard()),
                                            ),
                                            el.discr_ty()
                                                .ref_to_snap(el.discr(place_expr))
                                                .downcast_ty(),
                                        )
                                    }
                                }
                                None => {
                                    // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                    let zero = self.vcx.mk_uint::<0>();
                                    (e_rvalue_ty.expect_primitive().prim_to_snap)(zero.upcast_ty())
                                }
=======
                        let ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                        let place_expr = self.encode_place(Place::from(*place)).expr;

                        match ty.generic_predicate.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(el) => {
                                let discr_expr = self.vcx.mk_field_expr(place_expr, el.as_ref().unwrap().discr);
                                self.vcx.mk_unfolding_expr(ty.ref_to_pred_app(self.vcx, place_expr, Some(self.vcx.mk_wildcard())), discr_expr)
>>>>>>> ide/rewrite-2023-assistant-features
                            }
                            .upcast_ty(),
                        )
                    }
                    mir::Rvalue::Ref(_reg, _kind, place) => {
                        Some(match rvalue_ty.kind() {
                            TyKind::Ref(.., ty::Mutability::Not) => {
                                let (address, snap, _, _) = self.encode_place_snap((*place).into());
                                let inner = self.ty_use_pure(rvalue_ty).expect_immref();
                                inner.prim_to_snap(address.expr.address, snap).upcast_ty()
                            }
                            TyKind::Ref(.., ty::Mutability::Mut) => {
                                let e_rvalue_ty = self.ty_use_pure(rvalue_ty);
                                let (place_expr, snap, _, _) =
                                    self.encode_place_snap(Place::from(*place));

                                // The snapshot of the referenced value should be encoded as a generic `Param`
                                let inner = e_rvalue_ty.expect_mutref();
                                inner
                                    .prim_to_snap(place_expr.expr.expect_predicate(), snap)
                                    .upcast_ty()
                            }
                            _ => unreachable!(),
                        })
                    }

                    //mir::Rvalue::Discriminant(Place<'vir>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'vir>, Ty<'vir>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'vir>) => {}
<<<<<<< HEAD
                    _ => None,
=======
                    other => {
                        tracing::error!("unsupported rvalue {other:?}");
                        self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "rvalue {rvalue:?}"))
                    }
>>>>>>> ide/rewrite-2023-assistant-features
                };

                if let Some(rval_enc) = rval_enc {
                    // TODO: this is to do FPCS repacks after accessing the rvalue
                    //let e_rvalue_ty = self.deps.require_local::<TyImpureEnc>(rvalue_ty).unwrap();
                    //let (rval_var, rval_expr) = self.new_tmp(e_rvalue_ty.snapshot());
                    //self.stmt(self.vcx.mk_pure_assign_stmt(rval_expr, expr));

                    //self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);

                    let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                    assert!(dest_ty.variant_index.is_none());
                    let dest_ty_out = self.ty_use_impure(dest_ty.ty);
                    let method_assign_app =
                        dest_ty_out.apply_method_assign(self.vcx, proj_enc, rval_enc);

                    self.stmt(method_assign_app);
                } else {
                    self.vcx.with_span(span, |vcx| {
                        let error_msg = format!("unsupported rvalue {rvalue:?} might be reached");
                        vcx.handle_error("exhale.failed:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(&error_msg, span.into())])
                        });
                        self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                    });
                }
            }

            // no-ops
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop
            | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {}

            mir::StatementKind::Intrinsic(intrinsic_kind) => {
                let intrinsic_kind = intrinsic_kind.clone();
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            format!("unsupported intrinsic statement {intrinsic_kind:?} might be reached"),
                            span.into(),
                        )])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                });
            }

            mir::StatementKind::Retag(..)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::Deinit(..) => unreachable!(
                "the statement kind {:?} is not allowed in the MIR analysis phase",
                statement.kind
            ),
        }
        self.new_after_label(location);
    }

<<<<<<< HEAD
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        if self.deps.check_cycle().is_err() {
            return;
        }

        comment!(self, "[MIR] {location:?}: {:?}", terminator.kind);
        let span = terminator.source_info.span;

        let current_fpcs = self.current_fpcs.take().unwrap();
        let cfpcs = &current_fpcs.statements[location.statement_index];
        for phase in EvalStmtPhase::phases() {
            comment!(self, "PCG (T) {phase}");
            self.pcg_actions(&cfpcs.states[phase], cfpcs.actions(phase), false);
        }
        self.current_fpcs = Some(current_fpcs);
=======
    fn visit_terminator(
        &mut self,
        terminator: &mir::Terminator<'vir>,
        location: mir::Location,
    ) {
        self.stmt(self.vcx.mk_comment_stmt(
            // TODO: also add bb and location for better debugging?
            vir::vir_format!(self.vcx, "{:?}", terminator.kind),
        ));
        let span = terminator.source_info.span;
>>>>>>> ide/rewrite-2023-assistant-features

        let terminator = match &terminator.kind {
            mir::TerminatorKind::Goto { target }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx());
                let discr_ty = self.ty_use_pure(discr_ty_rs).expect_primitive();

                let goto_targets = self.vcx.alloc_slice(
                    &targets
                        .iter()
                        .enumerate()
                        .map(|(idx, (value, target))| {
                            assert_eq!(
                                self.current_fpcs.as_ref().unwrap().terminator.succs[idx].block(),
                                target
                            );

                            let current_fpcs = self.current_fpcs.take().unwrap();
                            let borrows = &current_fpcs.statements.last().unwrap().states
                                [EvalStmtPhase::PostMain];
                            let mut extra_stmts =
                                self.collect_pcs_succ(borrows, &current_fpcs.terminator.succs[idx]);
                            self.current_fpcs = Some(current_fpcs);
                            extra_stmts.push(self.set_from_to_flag(location.block, target));

                            self.vcx.mk_goto_if_target(
                                discr_ty.expr_from_bits(discr_ty_rs, value).as_dyn(),
                                self.vcx
                                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                                self.vcx.alloc_slice(&extra_stmts),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                let goto_otherwise = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(
                    targets.otherwise().as_usize(),
                ));

                let otherwise_succ_idx = goto_targets.len();
                assert_eq!(
                    self.current_fpcs.as_ref().unwrap().terminator.succs[otherwise_succ_idx]
                        .block(),
                    targets.otherwise()
                );

                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    &current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain];
                let mut otherwise_stmts = self
                    .collect_pcs_succ(borrows, &current_fpcs.terminator.succs[otherwise_succ_idx]);
                self.current_fpcs = Some(current_fpcs);
                otherwise_stmts.push(self.set_from_to_flag(location.block, targets.otherwise()));

                let discr_ex =
                    (discr_ty.snap_to_prim)(self.encode_operand_snap(discr).downcast_ty());
                self.vcx.mk_goto_if_stmt(
                    discr_ex.as_dyn(), // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return => {
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows = current_fpcs.statements.last().unwrap().states
                    [EvalStmtPhase::PostMain]
                    .borrow_pcg();
                let wand_packages = self.package_wands(borrows);
                self.current_fpcs = Some(current_fpcs);
                self.stmts(wand_packages);

                self.vcx
                    .mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::End))
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
<<<<<<< HEAD
                // emit the current block, create a new label for the terminator
                // TODO: should we do this for any other terminators?
                let current_block = match self.current_block_label {
                    Some(vir::CfgBlockLabelData::BasicBlock(block)) => *block,
                    _ => unreachable!(),
                };
                self.encoded_blocks.push(
                    self.vcx.mk_cfg_block(
                        self.current_block_label
                            .replace(
                                self.vcx.alloc(vir::CfgBlockLabelData::BasicBlockTerminator(
                                    current_block,
                                )),
                            )
                            .unwrap(),
                        &[],
                        self.vcx
                            .alloc_slice(&self.current_stmts.replace(Vec::new()).unwrap()),
                        self.vcx
                            .mk_goto_stmt(self.vcx.alloc(
                                vir::CfgBlockLabelData::BasicBlockTerminator(current_block),
                            )),
                    ),
                );

                let func_ty = func.ty(self.body, self.vcx.tcx());
                let (func_def_id, caller_substs) =
                    RustSignature::get_def_id_and_caller_substs(func_ty);
                let is_pure = crate::encoders::with_proc_spec(
                    SpecQuery::GetProcKind(
                        func_def_id,
                        ty::List::identity_for_item(self.vcx.tcx(), func_def_id),
                    ),
                    |spec| spec.kind.is_pure().unwrap_or_default(),
                )
                .unwrap_or_default();

                let dest = self
                    .encode_place(Place::from(*destination))
                    .expr
                    .expect_predicate();
                if is_pure {
                    let pure_func = self
                        .deps
                        .require_dep::<FunctionCallEnc>(CallTaskDescription::new(
                            self.def_id,
                            caller_substs,
                            func_def_id,
                        ))
                        .unwrap();
                    let snap_args = args
                        .iter()
                        .map(|arg| self.encode_operand_snap(&arg.node))
                        .collect::<Vec<_>>();
                    let pure_func_app = pure_func.call(snap_args);
=======
                let (func_def_id, caller_substs) = self.get_def_id_and_caller_substs(func);
                let is_pure = crate::encoders::with_proc_spec(func_def_id, |spec| {
                    // FIXME: WIP. only handling inherent specs for now
                    if config::show_ide_info() {
                        let mut spans: Vec<Span> = Vec::new();
                        let tcx = self.vcx().tcx();
                        if let Some(pre_def_ids) = spec.pres.expect_empty_or_inherent() {
                            let mut pre_spans = pre_def_ids
                                .iter()
                                .map(|pre_def_id| tcx.def_span(pre_def_id))
                                .collect::<Vec<Span>>();
                            spans.append(&mut pre_spans);
                        }
                        if let Some(post_def_ids) = spec.posts.expect_empty_or_inherent() {
                            let mut post_spans = post_def_ids
                                .iter()
                                .map(|pre_def_id| tcx.def_span(pre_def_id))
                                .collect::<Vec<Span>>();
                            spans.append(&mut post_spans);
                        }
                        if let Some(pledges) = spec.pledges.expect_empty_or_inherent() {
                            let mut pledge_spans = pledges
                                .iter()
                                .map(|pledge| {
                                    let rhs = tcx.def_span(pledge.rhs);
                                    if let Some(lhs) = pledge.lhs { tcx.def_span(lhs).to(rhs) }
                                    else { rhs }
                                }).collect::<Vec<Span>>();
                            spans.append(&mut pledge_spans);
                        }
                        // FIXME: not detecting the pure annotation in local-testing/generics/mono.rs
                        if let Some(Some(purity_def_id)) = spec.purity.expect_empty_or_inherent() {
                            spans.push(tcx.def_span(purity_def_id));
                        }
                        if let Some(Some(terminates_def_id)) = spec.terminates.expect_empty_or_inherent() {
                            spans.push(tcx.def_span(terminates_def_id.to_def_id()));
                        }
                        let krate = tcx.crate_name(func_def_id.krate);
                        let defpath = tcx.def_path_str(func_def_id);
                        let unique_item_name = format!("{}::{}", krate, defpath);
                        self.vcx().push_call_contract_span(
                            unique_item_name,
                            span.clone(),
                            spans,
                            tcx.sess.source_map(),
                        )
                    }

                    spec.kind.is_pure().unwrap_or_default()
                }).unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination)).expr;

                let task = (func_def_id, self.def_id);
                let sig = self.vcx().tcx().fn_sig(func_def_id);
                let sig = if self.monomorphize {
                    let param_env = self.vcx().tcx().param_env(self.def_id);
                    self.vcx().tcx().subst_and_normalize_erasing_regions(
                        caller_substs,
                        param_env,
                        sig
                    )
                } else {
                    sig.instantiate_identity()
                };
                let fn_arg_tys = sig
                    .inputs()
                    .iter()
                    .map(|i| i.skip_binder())
                    .copied()
                    .collect::<Vec<_>>();
                if is_pure {
                    let pure_func_app = self.encode_pure_func_app(
                        func_def_id,
                        sig,
                        caller_substs,
                        args,
                        destination,
                        self.def_id,
                        &()
                    );
>>>>>>> ide/rewrite-2023-assistant-features

                    let return_ty = destination.ty(self.local_decls, self.vcx.tcx()).ty;
                    let assign_stmt = self.ty_use_impure(return_ty).apply_method_assign(
                        self.vcx,
                        dest,
                        pure_func_app,
                    );

                    self.stmt(assign_stmt);
                } else {
<<<<<<< HEAD
                    let Ok(func_out) =
                        self.deps
                            .require_dep::<encoders::MethodCallEnc>(CallTaskDescription::new(
                                self.def_id,
                                caller_substs,
                                func_def_id,
                            ))
                    else {
                        self.current_terminator = Some(
                            self.vcx
                                .mk_dummy_stmt(vir::vir_format!(self.vcx, "recursion",)),
                        );
                        return;
                    };

                    let method_in = args
                        .iter()
                        .map(|arg| self.encode_operand(&arg.node))
                        .collect::<Vec<_>>();

                    let call = func_out.call(method_in, dest);

                    let label_pre = self.new_label("pre");
                    self.vcx.with_span(span, |vcx| {
                        vcx.handle_error(
                            "call.precondition:assertion.false",
                            move |reason_span_opt| {
                                let mut error = PrustiError::verification(
                                    "precondition might not hold",
                                    span.into(),
                                );
                                if let Some(reason_span) = reason_span_opt {
                                    error.add_note_mut(
                                        "the failing precondition is here",
                                        Some(reason_span.into()),
                                    );
                                }
                                Some(vec![error])
                            },
                        );
                        self.stmts(call);
                    });
                    let label_post = self.new_label("post");
                    self.call_labels
                        .insert(location.block, (label_pre, label_post));
=======
                    let func_out = self
                        .deps
                        .require_ref::<encoders::MirImpureEnc>(
                            FunctionCallTaskDescription::new(
                                task.0, caller_substs, task.1
                            )
                        )
                        .unwrap();


                    let method_in = args.iter().map(|arg| self.encode_operand(arg)).collect::<Vec<_>>();


                    for ((fn_arg_ty, arg), arg_ex) in fn_arg_tys.iter().zip(args.iter()).zip(method_in.iter()) {
                        let local_decls = self.local_decls_src();
                        let tcx = self.vcx().tcx();
                        let arg_ty = arg.ty(local_decls, tcx);
                        let caster = self.deps()
                            .require_ref::<CastToEnc<CastTypeImpure>>(CastArgs {
                                expected: *fn_arg_ty,
                                actual: arg_ty
                            })
                            .unwrap();
                        // In this context, `apply_cast_if_necessary` returns
                        // the impure operation to perform the cast
                        if let Some(stmt) = caster.apply_cast_if_necessary(self.vcx(), arg_ex) {
                            self.stmt(stmt);
                        }
                    }

                    let mut method_args =
                        std::iter::once(dest).chain(method_in).collect::<Vec<_>>();
                    let mono = self.monomorphize;
                    let encoded_ty_args = self
                        .deps()
                        .require_local::<LiftedFuncAppTyParamsEnc>(
                            (mono, caller_substs)
                        )
                        .unwrap()
                        .iter()
                        .map(|ty| ty.expr(self.vcx()));

                    method_args.extend(encoded_ty_args);

                    self.vcx().with_span(span, |vcx| {
                        vcx.handle_error("call.precondition:assertion.false", move |reason_span_opt| {
                            let mut error = PrustiError::verification("precondition might not hold", span.into());
                            if let Some(reason_span) = reason_span_opt {
                                error.add_note_mut("the failing precondition is here", Some(reason_span.into()));
                            }
                            Some(vec![error])
                        });
                        self.stmt(self.vcx.alloc(vir::StmtGenData::new(
                            self.vcx.alloc(func_out.method_ref.apply(self.vcx, &method_args)),
                        )));
                    });
                    let expected_ty = destination.ty(self.local_decls_src(), self.vcx.tcx()).ty;
                    let fn_result_ty = sig.output().skip_binder();
                    let result_cast = self
                        .deps()
                        .require_ref::<CastToEnc<CastTypeImpure>>(CastArgs {
                            expected: expected_ty,
                            actual: fn_result_ty,
                        })
                        .unwrap();
                    if let Some(stmt) = result_cast.apply_cast_if_necessary(self.vcx, dest) {
                        self.stmt(stmt);
                    }
>>>>>>> ide/rewrite-2023-assistant-features
                }

                target
                    .map(|target| {
                        const REAL_TARGET_SUCC_IDX: usize = 0;
                        // Ensure that the terminator succ that we use for the repacks is the correct one
                        assert_eq!(
                            self.current_fpcs.as_ref().unwrap().terminator.succs
                                [REAL_TARGET_SUCC_IDX]
                                .block(),
                            target
                        );
                        let current_fpcs = self.current_fpcs.take().unwrap();
                        let borrows = current_fpcs.statements.last().unwrap().states
                            [EvalStmtPhase::PostMain]
                            .clone();
                        self.pcs_succ(
                            &borrows,
                            &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                        );
                        self.current_fpcs = Some(current_fpcs);
                        let set_flag = self.set_from_to_flag(location.block, target);
                        self.stmt(set_flag);

                        self.vcx.mk_goto_stmt(
                            self.vcx
                                .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                        )
                    })
                    .unwrap_or_else(|| {
                        // TODO: detect panic causes, adjust message accordingly
<<<<<<< HEAD
                        self.vcx.with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "unreachable statement might be reached",
                                    span.into(),
                                )])
=======
                        self.vcx().with_span(span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification("unreachable statement might be reached", span.into())])
>>>>>>> ide/rewrite-2023-assistant-features
                            });
                            self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                            self.vcx.mk_assume_false_stmt()
                        })
                    })
<<<<<<< HEAD
            }
            // If we are not checking for overflows, encode an overflow-checking
            // assertion as a goto.
            mir::TerminatorKind::Assert { msg, target, .. }
                if !config::check_overflows()
                    && matches!(
                        **msg,
                        mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..)
                    ) =>
            {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
=======
>>>>>>> ide/rewrite-2023-assistant-features
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                ..
            } => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(
                    &self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX]
                        .block(),
                    target,
                );
                let current_fpcs = self.current_fpcs.take().unwrap();
                let borrows =
                    current_fpcs.statements.last().unwrap().states[EvalStmtPhase::PostMain].clone();
                self.pcs_succ(
                    &borrows,
                    &current_fpcs.terminator.succs[REAL_TARGET_SUCC_IDX],
                );
                self.current_fpcs = Some(current_fpcs);

                let e_bool = self.ty_use_pure(self.vcx.tcx().types.bool);
                let enc = self.encode_operand_snap(cond).downcast_ty();
                let enc = (e_bool.expect_primitive().snap_to_prim)(enc);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self.vcx.mk_eq_expr(enc, expected);
                let error_msg = match **msg {
                    mir::AssertMessage::BoundsCheck { .. } => "bounds check may fail",
                    mir::AssertMessage::Overflow(..) | mir::AssertMessage::OverflowNeg(..) => {
                        "operation may overflow"
                    }
                    mir::AssertMessage::DivisionByZero(..)
                    | mir::AssertMessage::RemainderByZero(..) => "division by zero may occur",
                    mir::AssertMessage::ResumedAfterReturn(..) => {
                        "execution may continue after return"
                    }
                    mir::AssertMessage::ResumedAfterPanic(..) => {
                        "execution may continue after panic"
                    }
                    mir::AssertMessage::MisalignedPointerDereference { .. } => {
                        "misaligned pointer may be dereferenced"
                    }
                    mir::AssertKind::ResumedAfterDrop(..) => "execution may continue after drop",
                    mir::AssertKind::NullPointerDereference => "null pointer may be dereferenced",
                    mir::AssertKind::InvalidEnumConstruction(..) => {
                        "invalid enum construction may occur"
                    }
                };
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(error_msg, span.into())])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(assert));
                });
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                self.vcx.mk_goto_stmt(target_bb)
            }
<<<<<<< HEAD
            mir::TerminatorKind::Unreachable => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::verification(
                        "unreachable statement might be reached",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
=======
            mir::TerminatorKind::Unreachable => {
                self.vcx().with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification("unreachable statement might be reached", span.into())])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                    self.vcx.mk_assume_false_stmt()
                })
            }
>>>>>>> ide/rewrite-2023-assistant-features

            mir::TerminatorKind::Drop { target, .. } => {
                let set_flag = self.set_from_to_flag(location.block, *target);
                self.stmt(set_flag);
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }

            mir::TerminatorKind::UnwindResume | mir::TerminatorKind::UnwindTerminate(..) => {
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::unsupported(
                            "unwind paths are not supported",
                            span.into(),
                        )])
                    });
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                    self.vcx.mk_assume_false_stmt()
                })
            }

            mir::TerminatorKind::TailCall { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "tail calls are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::Yield { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "yield statements are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::CoroutineDrop => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "coroutines are not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
            mir::TerminatorKind::InlineAsm { .. } => self.vcx.with_span(span, |vcx| {
                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                    Some(vec![PrustiError::unsupported(
                        "inline assembly is not supported",
                        span.into(),
                    )])
                });
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
                self.vcx.mk_assume_false_stmt()
            }),
        };
        self.new_after_label(location);
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
