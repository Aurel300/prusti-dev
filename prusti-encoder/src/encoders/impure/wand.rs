use std::collections::BTreeSet;

use pcs::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, BorrowPCGEdgeRef},
        edge::kind::BorrowPCGEdgeKind,
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

type Inputs<'a> = BTreeSet<PCGNode<'a, MaybeRemotePlace<'a>, MaybeRemotePlace<'a>>>;
type Outputs<'a> = BTreeSet<RegionProjection<'a, MaybeOldPlace<'a>>>;

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(super) fn get_abstraction_edges<'a>(
        g: &'a BorrowsGraph<'vir>,
    ) -> impl Iterator<Item = (BorrowPCGEdgeRef<'vir, 'a>, Inputs<'vir>, Outputs<'vir>)> + 'a {
        g.edges().filter_map(|edge| {
            match edge.kind() {
                BorrowPCGEdgeKind::Abstraction(at) => {
                    let inputs: Inputs<'vir> = at.inputs();
                    let mut is = inputs.iter();
                    if is.any(|i| matches!(i, PCGNode::Place(MaybeRemotePlace::Remote(_)))) {
                        // BUG in the pcg
                        return None;
                    } else {
                        let outputs: Outputs<'vir> = at.outputs();
                        Some((edge, inputs, outputs))
                    }
                }
                _ => None,
            }
        })
    }

    pub(crate) fn pcs_wands(&mut self, curr_fpcs: &PcgBasicBlock<'vir>, pcs: &PcgSuccessor<'vir>) {
        if self.loop_analysis.loop_head_of(pcs.block()).is_none() {
            return;
        }
        // TODO: use a label+old instead
        let block = curr_fpcs.statements.first().unwrap();
        let mut bb = 10 * (block.location.block.as_usize() + 1);
        for (_edge, inputs, outputs) in Self::get_abstraction_edges(pcs.entry_graph()) {
            let mut proof_block = Vec::new();
            let mut let_bind = Vec::new();
            let mut wand_rhs = Vec::new();
            for i in inputs {
                self.encode_pcg_node(&i, &mut wand_rhs, &mut let_bind, bb);
                proof_block.extend(self.to_unblock(curr_fpcs, i));
            }
            let mut wand_lhs = Vec::new();
            for i in outputs {
                let exprs = self.encode_region_projection(i, &mut let_bind, bb);
                wand_lhs.extend(exprs);
            }
            let wand = self.vcx.mk_wand(
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
            );
            for (name, expr) in let_bind {
                let ty = expr.ty();
                let local = vir::vir_local_decl! { self.vcx; [name] : [ty] };
                self.stmt(self.vcx.mk_local_decl_stmt(local, Some(expr)));
            }
            let proof_block = self.vcx.alloc_slice(&proof_block);
            self.stmt(self.vcx.mk_package_stmt(wand, proof_block));
            bb += 1;
        }
    }

    fn to_unblock(
        &mut self,
        curr_fpcs: &PcgBasicBlock<'vir>,
        rhs: impl Into<PCGNode<'vir>>,
    ) -> Vec<vir::Stmt<'vir>> {
        let state = &curr_fpcs.statements.last().unwrap().borrows[EvalStmtPhase::PostMain];
        let ug = UnblockGraph::for_node(rhs, state, self.fpcs_analysis.repacker());

        let actions = ug.actions(self.fpcs_analysis.repacker()).unwrap();
        let package_script = self.block(|visitor| {
            visitor.pcs_unblock_actions(&actions);
        });
        package_script
    }
}
