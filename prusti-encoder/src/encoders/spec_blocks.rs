use pcg::r#loop::LoopAnalysis;
use prusti_interface::specs::is_spec_fn;
use prusti_rustc_interface::{
    abi::FieldIdx,
    data_structures::fx::FxHashMap,
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::{DefId, LocalDefId},
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

pub enum SpecBlockKind<'tcx> {
    LoopInvariant {
        ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
        substs: ty::GenericArgsRef<'tcx>,
        args: IndexVec<FieldIdx, mir::Operand<'tcx>>,
    },
}

pub struct SpecBlocksEnc;
#[derive(Clone, Copy)]
pub struct SpecBlocksEncOutput<'vir> {
    block_specs: &'vir FxHashMap<mir::BasicBlock, Vec<SpecBlockKind<'vir>>>,
    specs_for: &'vir FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>>,
}

impl<'vir> SpecBlocksEncOutput<'vir> {
    pub fn loop_invariants(&self, block: mir::BasicBlock) -> Option<impl Iterator<Item = (ty::Ty<'vir>, LocalDefId, ty::GenericArgsRef<'vir>, &'vir IndexVec<FieldIdx, mir::Operand<'vir>>)> + 'vir> {
        let spec_blocks = self.specs_for.get(&block)?;
        Some(spec_blocks
            .iter()
            .flat_map(|spec_block| &self.block_specs[spec_block])
            .filter_map(|kind| match kind {
                SpecBlockKind::LoopInvariant { ty, def_id, substs, args } => Some((*ty, *def_id, *substs, args)),
            }))
    }

    pub fn is_spec_block(&self, block: mir::BasicBlock) -> bool {
        self.block_specs.keys().any(|key| *key == block)
    }
}

pub type SpecBlocksEncError = ();

impl TaskEncoder for SpecBlocksEnc {
    task_encoder::encoder_cache!(SpecBlocksEnc);

    type TaskDescription<'vir> = DefId;

    type OutputFullLocal<'vir> = SpecBlocksEncOutput<'vir>;

    type EncodingError = SpecBlocksEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let body = vcx
                .body_mut()
                .get_impure_fn_body(task_key.expect_local(), ty::GenericArgs::identity_for_item(vcx.tcx(), *task_key), None);
            let loop_analysis = LoopAnalysis::find_loops(&body);
            let mut visitor = SpecBlocksVisitor {
                body: &body,
                tcx: vcx.tcx(),
                block_specs: Default::default(),
                current_kinds: None,
            };
            use mir::visit::Visitor;
            visitor.visit_body(&body);
            let mut specs_for: FxHashMap<mir::BasicBlock, Vec<mir::BasicBlock>> = Default::default();
            for (block, kinds) in &visitor.block_specs {
                for kind in kinds {
                    match kind {
                        SpecBlockKind::LoopInvariant { .. } => {
                            let inner_loop_head = loop_analysis[loop_analysis.innermost_loop(*block).unwrap()];
                            specs_for.entry(inner_loop_head)
                                .or_default()
                                .push(*block);
                        }
                    }
                }
            }
            Ok((SpecBlocksEncOutput {
                block_specs: vcx.alloc(visitor.block_specs),
                specs_for: vcx.alloc(specs_for),
            }, ()))
        })
    }
}

struct SpecBlocksVisitor<'tcx, 'vis> {
    body: &'vis mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    block_specs: FxHashMap<mir::BasicBlock, Vec<SpecBlockKind<'tcx>>>,
    current_kinds: Option<Vec<SpecBlockKind<'tcx>>>,
}

impl<'tcx, 'vis> mir::visit::Visitor<'tcx> for SpecBlocksVisitor<'tcx, 'vis> {
    fn visit_basic_block_data(
        &mut self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'tcx>,
    ) {
        self.current_kinds = Some(Vec::new());
        self.super_basic_block_data(block, data);
        let spec_kinds = self.current_kinds.take().unwrap();
        if !spec_kinds.is_empty() {
            println!("{block:?} is a spec block, with statements: {:?}", data.statements);
            self.block_specs.insert(block, spec_kinds);
        }
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'tcx>,
        _location: mir::Location,
    ) {
        match &statement.kind {
            mir::StatementKind::Assign(assgn) => {
                let mir::Rvalue::Aggregate(aggr, args) = &assgn.1 else { return; };
                let mir::AggregateKind::Closure(def_id, substs) = &**aggr else { return; };
                if is_spec_fn(self.tcx, *def_id) {
                    self.current_kinds.as_mut().unwrap().push(SpecBlockKind::LoopInvariant {
                        ty: assgn.1.ty(self.body, self.tcx),
                        def_id: def_id.expect_local(),
                        substs,
                        args: args.clone(),
                    });
                }
            }
            _ => (),
        }
    }
}
