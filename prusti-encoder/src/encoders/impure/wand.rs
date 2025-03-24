use std::collections::BTreeSet;

use pcs::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, BorrowPCGEdgeRef},
        edge::{abstraction::AbstractionType, kind::BorrowPCGEdgeKind},
        graph::BorrowsGraph,
        region_projection::RegionProjection,
        unblock_graph::UnblockGraph,
    },
    combined_pcs::{EvalStmtPhase, PCGNode, PcgSuccessor},
    free_pcs::PcgBasicBlock,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace},
};
use task_encoder::TaskEncoder;

use crate::encoders::ImpureEncVisitor;

use super::r#loop::WandOldOuter;

type Inputs<'a> = BTreeSet<PCGNode<'a, MaybeRemotePlace<'a>, MaybeRemotePlace<'a>>>;
type Outputs<'a> = BTreeSet<RegionProjection<'a, MaybeOldPlace<'a>>>;

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(crate) fn ignore_abstraction_edge(at: &AbstractionType<'vir>) -> bool {
        let inputs: Inputs<'vir> = at.inputs();
        inputs
            .iter()
            .any(|i| matches!(i, PCGNode::Place(MaybeRemotePlace::Remote(_))))
    }

    pub(super) fn get_abstraction_edges<'a>(
        g: &'a BorrowsGraph<'vir>,
    ) -> impl Iterator<Item = (BorrowPCGEdgeRef<'vir, 'a>, Inputs<'vir>, Outputs<'vir>)> + 'a {
        g.edges().filter_map(|edge| match edge.kind() {
            BorrowPCGEdgeKind::Abstraction(at) if !Self::ignore_abstraction_edge(at) => {
                Some((edge, at.inputs(), at.outputs()))
            }
            _ => None,
        })
    }

    pub(crate) fn pcs_wands(&mut self, curr_fpcs: &PcgBasicBlock<'vir>, pcs: &PcgSuccessor<'vir>) {
        // TODO: this should be done according to pcg annotations instead!
        if self.loop_analysis.loop_head_of(pcs.block()).is_none() {
            return;
        }
        let mut old_outer = WandOldOuter::Label(None);
        for (_edge, inputs, outputs) in Self::get_abstraction_edges(pcs.entry_graph()) {
            let mut proof_block = Vec::new();
            let mut wand_rhs = Vec::new();
            for i in inputs {
                self.encode_pcg_node(&i, &mut wand_rhs, &mut old_outer);
                proof_block.extend(self.to_unblock(curr_fpcs, i, &mut old_outer));
            }
            let mut wand_lhs = Vec::new();
            for i in outputs {
                let exprs = self.encode_region_projection(i, &mut old_outer);
                wand_lhs.extend(exprs);
            }
            let wand = self.vcx.mk_wand(
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
            );
            let proof_block = self.vcx.alloc_slice(&proof_block);
            self.stmt(self.vcx.mk_package_stmt(wand, proof_block));
        }
    }

    pub(crate) fn mk_wand(
        &mut self,
        inputs: Inputs<'vir>,
        outputs: Outputs<'vir>,
        label: Option<&'vir str>,
    ) -> &'vir vir::WandData<'vir> {
        let mut old_outer = WandOldOuter::Label(label);
        let mut wand_rhs = Vec::new();
        for i in inputs {
            self.encode_pcg_node(&i, &mut wand_rhs, &mut old_outer);
        }
        let mut wand_lhs = Vec::new();
        for i in outputs {
            let exprs = self.encode_region_projection(i, &mut old_outer);
            wand_lhs.extend(exprs);
        }
        self.vcx.mk_wand(
            self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
            self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
        )
    }

    fn to_unblock(
        &mut self,
        curr_fpcs: &PcgBasicBlock<'vir>,
        rhs: impl Into<PCGNode<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let cfpcs = curr_fpcs.statements.last().unwrap();
        let state = &cfpcs.borrows[EvalStmtPhase::PostMain];
        let ug = UnblockGraph::for_node(rhs, state, self.fpcs_analysis.repacker());

        let WandOldOuter::Label(label) = old_outer else {
            unreachable!()
        };
        let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
        let actions = ug.actions(self.fpcs_analysis.repacker()).unwrap();
        let package_script = self.block(|visitor| {
            visitor.pcs_unblock_actions(&actions, Some(label));
        });
        package_script
    }
}
