use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
    type_ir::sty::TyKind, ast,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use std::collections::HashMap;
use crate::encoders::{ViperTupleEncoder, TypeEncoder};

pub struct MirPureEncoder;

#[derive(Clone, Debug)]
pub enum MirPureEncoderError {
    UnsupportedStatement,
    UnsupportedTerminator,
}

// TODO: does this need to be `&'vir [..]`?
type ExprInput<'vir> = (DefId, &'vir [vir::Expr<'vir>]);
type ExprRet<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone, Debug)]
pub struct MirPureEncoderOutput<'vir> {
    // TODO: is this a good place for argument types?
    //pub arg_tys: &'vir [Type<'vir>],
    pub expr: ExprRet<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirPureEncoder> = RefCell::new(Default::default());
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PureKind {
    Closure,
    Spec,
    Pure,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MirPureEncoderTask<'tcx> {
    // TODO: depth of encoding should be in the lazy context rather than here;
    //   can we integrate the lazy context into the identifier system?
    pub encoding_depth: usize,
    pub kind: PureKind,
    pub parent_def_id: DefId, // ID of the function
    pub promoted: Option<mir::Promoted>, // ID of a constant within the function
    pub param_env: ty::ParamEnv<'tcx>, // param environment at the usage site
    pub substs: ty::GenericArgsRef<'tcx>, // type substitutions at the usage site
    pub caller_def_id: DefId, // Caller/Use DefID
}

impl TaskEncoder for MirPureEncoder {
    type TaskDescription<'tcx> = MirPureEncoderTask<'tcx>;

    type TaskKey<'tcx> = (
        usize, // encoding depth
        PureKind, // encoding a pure function?
        DefId, // ID of the function
        Option<mir::Promoted>, // ID of a constant within the function, or `None` if encoding the function itself
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        DefId, // Caller/Use DefID
    );

    type OutputFullLocal<'vir> = MirPureEncoderOutput<'vir>;

    type EncodingError = MirPureEncoderError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
       where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, MirPureEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'tcx>(task: &Self::TaskDescription<'tcx>) -> Self::TaskKey<'tcx> {
        (
            // TODO
            task.encoding_depth,
            task.kind,
            task.parent_def_id,
            None,
            task.substs,
            task.caller_def_id,
        )
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        deps.emit_output_ref::<Self>(*task_key, ());

        let (_, kind, def_id, promoted, substs, caller_def_id) = *task_key;

        tracing::debug!("encoding {def_id:?}");
        let expr = vir::with_vcx(move |vcx| {
            //let body = vcx.tcx.mir_promoted(local_def_id).0.borrow();
            let body = match kind {
                PureKind::Closure => vcx.body.borrow_mut().get_closure_body(def_id, substs, caller_def_id),
                PureKind::Spec => vcx.body.borrow_mut().get_spec_body(def_id, substs, caller_def_id),
                PureKind::Pure => vcx.body.borrow_mut().get_pure_fn_body(def_id, substs, caller_def_id),
            };

            let expr_inner = Encoder::new(vcx, task_key.0, def_id, &body, deps).encode_body();

            // We wrap the expression with an additional lazy that will perform
            // some sanity checks. These requirements cannot be expressed using
            // only the type system.
            vcx.mk_lazy_expr(
                vir::vir_format!(vcx, "pure body {def_id:?}"),
                Box::new(move |vcx, lctx: ExprInput<'_>| {
                    // check: are we actually providing arguments for the
                    //   correct `DefId`?
                    assert_eq!(lctx.0, def_id);

                    // check: are we providing the expected number of arguments?
                    assert_eq!(lctx.1.len(), body.arg_count);

                    use vir::Reify;
                    expr_inner.0.reify(vcx, lctx)
                }),
            )
        });
        tracing::debug!("finished {def_id:?}");

        Ok((MirPureEncoderOutput { expr }, ()))
    }
}

#[derive(Debug, Default)]
struct Update<'vir> {
    binds: Vec<UpdateBind<'vir>>,
    versions: HashMap<mir::Local, usize>,
}

#[derive(Debug)]
enum UpdateBind<'vir> {
    Local(mir::Local, usize, ExprRet<'vir>),
    Phi(usize, ExprRet<'vir>),
}

impl<'vir> Update<'vir> {
    fn new() -> Self {
        Default::default()
    }

    fn merge(self, newer: Self) -> Self {
        Self {
            binds: self.binds.into_iter().chain(newer.binds.into_iter()).collect(),
            versions: self.versions.into_iter().chain(newer.versions.into_iter()).collect(),
        }
    }

    fn add_to_map(&self, curr_ver: &mut HashMap<mir::Local, usize>) {
        for (local, ver) in &self.versions {
            curr_ver.insert(*local, *ver);
        }
    }
}

struct Encoder<'tcx, 'vir: 'enc, 'enc>
{
    vcx: &'vir vir::VirCtxt<'tcx>,
    encoding_depth: usize,
    def_id: DefId,
    body: &'enc mir::Body<'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir>,
    visited: IndexVec<mir::BasicBlock, bool>,
    version_ctr: IndexVec<mir::Local, usize>,
    phi_ctr: usize,
}

impl<'tcx, 'vir: 'enc, 'enc> Encoder<'tcx, 'vir, 'enc>
{
    fn new(
        vcx: &'vir vir::VirCtxt<'tcx>,
        encoding_depth: usize,
        def_id: DefId,
        body: &'enc mir::Body<'tcx>,
        deps: &'enc mut TaskEncoderDependencies<'vir>,
    ) -> Self {
        assert!(!body.basic_blocks.is_cfg_cyclic(), "MIR pure encoding does not support loops");

        Self {
            vcx,
            encoding_depth,
            def_id,
            body,
            deps,
            visited: IndexVec::from_elem_n(false, body.basic_blocks.len()),
            version_ctr: IndexVec::from_elem_n(0, body.local_decls.len()),
            phi_ctr: 0,
        }
    }

    fn mk_local(
        &self,
        local: mir::Local,
        version: usize,
    ) -> &'vir str {
        vir::vir_format!(self.vcx, "_{}_{}s_{}", self.encoding_depth, local.as_usize(), version)
    }

    fn mk_local_ex(
        &self,
        local: mir::Local,
        version: usize,
    ) -> ExprRet<'vir> {
        self.vcx.mk_local_ex(self.mk_local(local, version))
    }

    fn mk_phi(
        &self,
        idx: usize,
    ) -> &'vir str {
        vir::vir_format!(self.vcx, "_{}_phi_{}", self.encoding_depth, idx)
    }

    fn mk_phi_acc(
        &self,
        tuple_ref: crate::encoders::ViperTupleEncoderOutputRef<'vir>,
        idx: usize,
        elem_idx: usize,
    ) -> ExprRet<'vir> {
        tuple_ref.mk_elem(self.vcx, self.vcx.mk_local_ex(self.mk_phi(idx)), elem_idx)
    }

    fn bump_version(
        &mut self,
        update: &mut Update<'vir>,
        local: mir::Local,
        expr: ExprRet<'vir>,
    ) {
        let new_version = self.version_ctr[local];
        self.version_ctr[local] += 1;
        update.binds.push(UpdateBind::Local(local, new_version, expr));
        update.versions.insert(local, new_version);
    }

    fn reify_binds(
        &self,
        update: Update<'vir>,
        expr: ExprRet<'vir>,
    ) -> ExprRet<'vir> {
        update.binds.iter()
            .rfold(expr, |expr, bind| match bind {
                UpdateBind::Local(local, ver, val) =>
                    self.vcx.mk_let_expr(self.mk_local(*local, *ver), val, expr),
                UpdateBind::Phi(idx, val) =>
                    self.vcx.mk_let_expr(self.mk_phi(*idx), val, expr),
            })
    }

    fn reify_branch(
        &self,
        tuple_ref: &crate::encoders::ViperTupleEncoderOutputRef<'vir>,
        mod_locals: &Vec<mir::Local>,
        curr_ver: &HashMap<mir::Local, usize>,
        update: Update<'vir>,
    ) -> ExprRet<'vir> {
        let tuple_args = mod_locals.iter().map(|local| self.mk_local_ex(
            *local,
            update.versions.get(local).copied().unwrap_or_else(|| {
                // TODO: remove (debug)
                if !curr_ver.contains_key(&local) {
                    tracing::error!("unknown version of local! {}", local.as_usize());
                    return 0xff
                }
                curr_ver[local]
            }),
        )).collect::<Vec<_>>();
        self.reify_binds(
            update,
            tuple_ref.mk_cons(self.vcx, &tuple_args),
        )
    }

    fn encode_body(&mut self) -> ExprRet<'vir> {
        let mut init = Update::new();
        init.versions.insert(mir::RETURN_PLACE, 0);
        for local in 1..=self.body.arg_count {
            let local_ex = self.vcx.mk_lazy_expr(
                vir::vir_format!(self.vcx, "pure in _{local}"),
                Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[local - 1].0),
            );
            init.binds.push(UpdateBind::Local(local.into(), 0, local_ex));
            init.versions.insert(local.into(), 0);
        }

        let (_, update) = self.encode_cfg(
            &init.versions,
            mir::START_BLOCK,
            None,
        );

        let res = init.merge(update);
        let ret_version = res.versions.get(&mir::RETURN_PLACE).copied().unwrap_or(0);

        self.reify_binds(res, self.mk_local_ex(mir::RETURN_PLACE, ret_version))
    }

    fn encode_cfg(
        &mut self,
        curr_ver: &HashMap<mir::Local, usize>,
        curr: mir::BasicBlock,
        branch_point: Option<mir::BasicBlock>,
    ) -> (mir::BasicBlock, Update<'vir>) {
        let dominators = self.body.basic_blocks.dominators();
        // We should never actually reach the join point bb: we should catch
        // this case and stop recursion in the `Goto` branch below. If this
        // assert fails we we may need to add catches in the other branches.
        debug_assert!(match (dominators.immediate_dominator(curr), branch_point) {
            (Some(immediate_dominator), Some(branch_point)) if immediate_dominator == branch_point =>
                // We could also be immediately dominated by the join point if we
                // are the next bb right after the `SwitchInt`.
                self.body.basic_blocks.predecessors()[curr].contains(&branch_point),
            _ => true,
        }, "reached join point bb {curr:?} (bp {branch_point:?})");

        // walk block statements first
        let mut new_curr_ver = curr_ver.clone();
        let stmt_update = self.body[curr].statements.iter()
            .fold(Update::new(), |update, stmt| {
                let newer = self.encode_stmt(&new_curr_ver, stmt);
                newer.add_to_map(&mut new_curr_ver);
                update.merge(newer)
            });

        // then walk terminator
        let term = self.body[curr].terminator.as_ref().unwrap();
        match &term.kind {
            &mir::TerminatorKind::Goto { target } => {
                match (dominators.immediate_dominator(target), branch_point) {
                    // As soon as we are about to step to a bb where the
                    // immediate dominator is the last branch point, we stop.
                    // Walking the rest of the CFG is handled in a parent call.
                    (Some(immediate_dominator), Some(branch_point))
                        if immediate_dominator == branch_point =>
                        // We are done with the current fragment of the CFG, the
                        // rest is handled in a parent call.
                        (target, stmt_update),
                    _ => {
                        // If you hit this then the join point algorithm
                        // probably not working correctly.
                        unreachable!("goto target not a join point {curr:?} -> {target:?} (branch point {branch_point:?})")
                    }
                }
            }

            mir::TerminatorKind::SwitchInt { discr, targets } => {
                // encode the discriminant operand
                let discr_expr = self.encode_operand(&new_curr_ver, discr);
                let discr_ty_out = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    discr.ty(self.body, self.vcx.tcx),
                ).unwrap();

                // walk `curr` -> `targets[i]` -> `join` for each target. The
                // join point is identified by reaching a bb where
                // `dominators.immediate_dominator(bb)` is equal to the bb of
                // the branch point (so pass `branch_point: Some(curr)`).
                // TODO: indexvec?
                let mut updates = targets.all_targets().iter()
                    .map(|target| self.encode_cfg(&new_curr_ver, *target, Some(curr)))
                    .collect::<Vec<_>>();

                // find locals updated in any of the results, which were also
                // defined before the branch
                let mut mod_locals = updates.iter()
                    .map(|(_, update)| update.versions.keys())
                    .flatten()
                    .filter(|local| new_curr_ver.contains_key(&local))
                    .copied()
                    .collect::<Vec<_>>();
                mod_locals.sort();
                mod_locals.dedup();

                // for each branch, create a Viper tuple of the updated locals
                let tuple_ref = self.deps.require_ref::<crate::encoders::ViperTupleEncoder>(
                    mod_locals.len(),
                ).unwrap();
                let (join, otherwise_update) = updates.pop().unwrap();
                println!("join: {curr:?} -> {join:?}");
                debug_assert!(updates.iter().all(|(other, _)| join == *other));
                let phi_expr = targets.iter()
                    .zip(updates.into_iter())
                    .fold(
                        self.reify_branch(&tuple_ref, &mod_locals, &new_curr_ver, otherwise_update),
                        |expr, ((cond_val, target), (_, branch_update))| self.vcx.mk_ternary_expr(
                            self.vcx.mk_bin_op_expr(
                                vir::BinOpKind::CmpEq,
                                discr_expr,
                                discr_ty_out.expr_from_u128(cond_val).lift()
                            ),
                            self.reify_branch(&tuple_ref, &mod_locals, &new_curr_ver, branch_update),
                            expr,
                        ),
                    );

                // assign tuple into a `phi` variable
                let phi_idx = self.phi_ctr;
                self.phi_ctr += 1;
                let mut phi_update = Update::new();
                phi_update.binds.push(UpdateBind::Phi(phi_idx, phi_expr));

                // update locals by destructuring `phi` variable
                // TODO: maybe this is unnecessary, we could instead use tuple
                //   access directly instead of the locals going forward?
                for (elem_idx, local) in mod_locals.iter().enumerate() {
                    let expr = self.mk_phi_acc(tuple_ref.clone(), phi_idx, elem_idx);
                    self.bump_version(&mut phi_update, *local, expr);
                    new_curr_ver.insert(*local, phi_update.versions[local]);
                }

                // walk `join` -> `end`
                let (end, end_update) = self.encode_cfg(&new_curr_ver, join, branch_point);
                (end, stmt_update.merge(phi_update.merge(end_update)))
            }

            mir::TerminatorKind::Return => {
                assert_eq!(branch_point, None);
                return (curr, stmt_update);
            }

            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                // TODO: extracting FnDef given func could be extracted? (duplication in impure)
                let func_ty = func.ty(self.body, self.vcx.tcx);
                let expr = match func_ty.kind() {
                    &TyKind::FnDef(def_id, arg_tys) => {
                        // A fn call in pure can only be one of two kinds: a
                        // call to another pure function, or a call to a prusti
                        // builtin function.
                        let is_pure = crate::encoders::with_proc_spec(def_id, |def_spec|
                            def_spec.kind.is_pure().unwrap_or_default()
                        ).unwrap_or_default();
                        if is_pure {
                            let pure_func = self.deps.require_ref::<crate::encoders::MirFunctionEncoder>(
                                (def_id, arg_tys, self.def_id)
                            ).unwrap().function_ref;
                            let encoded_args = args.iter()
                                .map(|oper| self.encode_operand(&new_curr_ver, oper))
                                .collect::<Vec<_>>();
                            pure_func.apply(self.vcx, &encoded_args)
                        } else {
                            self.encode_prusti_builtin(&new_curr_ver, def_id, arg_tys, args)
                        }
                    }
                    _ => todo!(),
                };

                let mut term_update = Update::new();
                assert!(destination.projection.is_empty());
                self.bump_version(&mut term_update, destination.local, expr);
                term_update.add_to_map(&mut new_curr_ver);

                // walk rest of CFG
                let (end,  end_update) = self.encode_cfg(&new_curr_ver, target.unwrap(), branch_point);

                (end,  stmt_update.merge(term_update).merge(end_update))
            }

            k => todo!("terminator kind {k:?}"),
        }
    }

    fn encode_stmt(
        &mut self,
        curr_ver: &HashMap<mir::Local, usize>,
        stmt: &mir::Statement<'tcx>,
    ) -> Update<'vir> {
        let mut update = Update::new();
        match &stmt.kind {
            &mir::StatementKind::StorageLive(local) => {
                let new_version = self.version_ctr[local];
                self.version_ctr[local] += 1;
                update.versions.insert(local, new_version);
            },
            mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::PlaceMention(..) => {}, // nop
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                assert!(dest.projection.is_empty());
                let expr = self.encode_rvalue(curr_ver, rvalue);
                self.bump_version(&mut update, dest.local, expr);
            }
            k => todo!("statement kind {k:?}"),
        }
        update
    }

    fn encode_rvalue(
        &mut self,
        curr_ver: &HashMap<mir::Local, usize>,
        rvalue: &mir::Rvalue<'tcx>,
    ) -> ExprRet<'vir> {
        match rvalue {
            mir::Rvalue::Use(op) => self.encode_operand(curr_ver, op),
            // Repeat
            mir::Rvalue::Ref(_, _, place) => self.encode_place(curr_ver, place),
            // ThreadLocalRef
            // AddressOf
            // Len
            // Cast
            mir::Rvalue::BinaryOp(op, box (l, r)) => {
                let ty_l = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    l.ty(self.body, self.vcx.tcx),
                ).unwrap().expect_prim().snap_to_prim;
                let ty_r = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    r.ty(self.body, self.vcx.tcx),
                ).unwrap().expect_prim().snap_to_prim;
                let ty_rvalue = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    rvalue.ty(self.body, self.vcx.tcx),
                ).unwrap().expect_prim().prim_to_snap;

                ty_rvalue.apply(self.vcx,
                    [self.vcx.mk_bin_op_expr(
                        op.into(),
                        ty_l.apply(self.vcx, [self.encode_operand(curr_ver, l)]),
                        ty_r.apply(self.vcx, [self.encode_operand(curr_ver, r)])
                    )],
                )
            }
            // CheckedBinaryOp
            // NullaryOp
            mir::Rvalue::UnaryOp(op, expr) => {
                let ty_expr = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    expr.ty(self.body, self.vcx.tcx),
                ).unwrap().expect_prim().snap_to_prim;
                let ty_rvalue = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    rvalue.ty(self.body, self.vcx.tcx),
                ).unwrap().expect_prim().prim_to_snap;

                ty_rvalue.apply(self.vcx,
                    [self.vcx.mk_unary_op_expr(
                        op.into(),
                        ty_expr.apply(self.vcx, [self.encode_operand(curr_ver, expr)]),
                    )]
                )
            }
            // Discriminant
            mir::Rvalue::Aggregate(box kind, fields) => match kind {
                mir::AggregateKind::Tuple if fields.len() == 0 =>
                    // TODO: why is this not a constant?
                    self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "s_Tuple0_cons()")),
                mir::AggregateKind::Closure(..) => {
                    // TODO: only when this is a spec closure?
                    let tuple_ref = self.deps.require_ref::<crate::encoders::ViperTupleEncoder>(
                        fields.len(),
                    ).unwrap();
                    tuple_ref.mk_cons(self.vcx, &fields.iter()
                        .map(|field| self.encode_operand(curr_ver, field))
                        .collect::<Vec<_>>())
                }
                _ => todo!("Unsupported Rvalue::AggregateKind: {kind:?}"),
            }
            mir::Rvalue::CheckedBinaryOp(binop, box (l, r)) => {
                let binop_function = self.deps.require_ref::<crate::encoders::MirBuiltinEncoder>(
                    crate::encoders::MirBuiltinEncoderTask::CheckedBinOp(
                        rvalue.ty(self.body, self.vcx.tcx),
                        *binop,
                        l.ty(self.body, self.vcx.tcx),
                        r.ty(self.body, self.vcx.tcx),
                    ),
                ).unwrap().function;
                binop_function.apply(self.vcx, &[
                    self.encode_operand(curr_ver, l),
                    self.encode_operand(curr_ver, r),
                ])
            }
            // ShallowInitBox
            // CopyForDeref
            k => {
                //dbg!(self.body);
                todo!("rvalue {k:?}")
            }
        }
    }

    fn encode_operand(
        &mut self,
        curr_ver: &HashMap<mir::Local, usize>,
        operand: &mir::Operand<'tcx>,
    ) -> ExprRet<'vir> {
        match operand {
            mir::Operand::Copy(place)
            | mir::Operand::Move(place) => self.encode_place(curr_ver, place),
            mir::Operand::Constant(box constant) => {
                // TODO: duplicated from mir_impure!
                match constant.literal {
                    mir::ConstantKind::Val(const_val, const_ty) => {
                        match const_ty.kind() {
                            ty::TyKind::Tuple(tys) if tys.len() == 0 =>
                                self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "s_Tuple0_cons()")),
                            ty::TyKind::Int(int_ty) => {
                                let scalar_val = const_val.try_to_scalar_int().unwrap();
                                self.vcx.mk_todo_expr(
                                    vir::vir_format!(
                                        self.vcx,
                                        "s_Int_{}_cons({})",
                                        int_ty.name_str(),
                                        scalar_val.try_to_int(scalar_val.size()).unwrap()
                                    )
                                )
                            }
                            ty::TyKind::Uint(uint_ty) => {
                                let scalar_val = const_val.try_to_scalar_int().unwrap();
                                self.vcx.mk_todo_expr(
                                    vir::vir_format!(
                                        self.vcx,
                                        "s_Uint_{}_cons({})",
                                        uint_ty.name_str(),
                                        scalar_val.try_to_uint(scalar_val.size()).unwrap()
                                    )
                                )
                            }
                            ty::TyKind::Bool =>
                                self.vcx.mk_todo_expr(
                                    vir::vir_format!(self.vcx, "s_Bool_cons({})", const_val.try_to_bool().unwrap())
                                ),
                            unsupported_ty => todo!("unsupported constant literal type: {unsupported_ty:?}"),
                        }
                    }
                    unsupported_literal => todo!("unsupported constant literal: {unsupported_literal:?}"),
                }
            }
        }
    }

    fn encode_place(
        &mut self,
        curr_ver: &HashMap<mir::Local, usize>,
        place: &mir::Place<'tcx>,
    ) -> ExprRet<'vir> {
        // TODO: remove (debug)
        if !curr_ver.contains_key(&place.local) {
            tracing::error!("unknown version of local! {}", place.local.as_usize());
            return self.vcx.mk_todo_expr(
                vir::vir_format!(self.vcx, "unknown_version_{}", place.local.as_usize())
            );
        }

        let mut place_ty =  mir::tcx::PlaceTy::from_ty(self.body.local_decls[place.local].ty);
        let mut expr = self.mk_local_ex(place.local, curr_ver[&place.local]);
        for elem in place.projection {
            expr = self.encode_place_element(place_ty.ty, elem, expr);
            place_ty = place_ty.projection_ty(self.vcx.tcx, elem);
        }
        expr
    }

    fn encode_place_element(&mut self, ty: ty::Ty<'tcx>, elem: mir::PlaceElem<'tcx>, expr: ExprRet<'vir>) -> ExprRet<'vir> {
         match elem {
            mir::ProjectionElem::Deref =>
                expr,
            mir::ProjectionElem::Field(field_idx, _) => {
                let field_idx= field_idx.as_usize();
                match ty.kind() {
                    TyKind::Closure(_def_id, args) => {
                        let upvars = args.as_closure().upvar_tys().iter().collect::<Vec<_>>().len();
                        let tuple_ref = self.deps.require_ref::<ViperTupleEncoder>(
                            upvars,
                        ).unwrap();
                        tuple_ref.mk_elem(self.vcx, expr, field_idx)
                    }
                    _ => {
                        let e_ty = self.deps.require_ref::<TypeEncoder>(ty).unwrap();
                        let struct_like = e_ty.expect_structlike();
                        let proj = struct_like.field_access[field_idx].read;
                        proj.apply(self.vcx, [expr])
                    }
                }
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn encode_prusti_builtin(&mut self, curr_ver: &HashMap<mir::Local, usize>, def_id: DefId, arg_tys: ty::GenericArgsRef<'tcx>, args: &Vec<mir::Operand<'tcx>>) -> ExprRet<'vir> {
        #[derive(Debug)]
        enum PrustiBuiltin {
            Forall,
            SnapshotEquality,
        }

        // TODO: this attribute extraction should be done elsewhere?
        let attrs = self.vcx.tcx.get_attrs_unchecked(def_id);
        let normal_attrs = attrs.iter()
            .filter(|attr| !attr.is_doc_comment())
            .map(|attr| attr.get_normal_item()).collect::<Vec<_>>();
        let mut builtin = None;
        for attr in normal_attrs.iter()
            .filter(|item| item.path.segments.len() == 2
                && item.path.segments[0].ident.as_str() == "prusti"
                && item.path.segments[1].ident.as_str() == "builtin") {
            match &attr.args {
                ast::AttrArgs::Eq(
                    _,
                    ast::AttrArgsEq::Hir(lit),
                ) => {
                    assert!(builtin.is_none(), "multiple prusti::builtin");
                    builtin = Some(match lit.symbol.as_str() {
                        "forall" => PrustiBuiltin::Forall,
                        "snapshot_equality" => PrustiBuiltin::SnapshotEquality,
                        other => panic!("illegal prusti::builtin ({other})"),
                    });
                }
                _ => panic!("illegal prusti::builtin"),
            }
        }

        match builtin.expect("call to unknown non-pure function in pure code") {
            PrustiBuiltin::SnapshotEquality => {
                assert_eq!(args.len(), 2);
                let lhs = self.encode_operand(&curr_ver, &args[0]);
                let rhs = self.encode_operand(&curr_ver, &args[1]);
                let eq_expr  = self.vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    lhs,
                    rhs,
                );

                let bool_cons = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    self.vcx.tcx.types.bool,
                ).unwrap().expect_prim().prim_to_snap;
                bool_cons.apply(self.vcx, [eq_expr])
            }
            PrustiBuiltin::Forall => {
                assert_eq!(arg_tys.len(), 2);
                let (qvar_tys, upvar_tys, cl_def_id) = match arg_tys[1].expect_ty().kind() {
                    TyKind::Closure(cl_def_id, cl_args) => (
                        match cl_args.as_closure().sig().skip_binder().inputs()[0].kind() {
                            TyKind::Tuple(list) => list,
                            _ => unreachable!(),
                        },
                        cl_args.as_closure().upvar_tys().iter().collect::<Vec<_>>(),
                        *cl_def_id,
                    ),
                    _ => panic!("illegal prusti::forall"),
                };

                let qvars = self.vcx.alloc_slice(&qvar_tys.iter()
                    .enumerate()
                    .map(|(idx, qvar_ty)| {
                        let ty_out = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                            qvar_ty,
                        ).unwrap();
                        self.vcx.mk_local_decl(
                            vir::vir_format!(self.vcx, "qvar_{}_{idx}", self.encoding_depth),
                            ty_out.snapshot,
                        )
                    })
                    .collect::<Vec<_>>());
                //let qvar_tuple_ref = self.deps.require_ref::<crate::encoders::ViperTupleEncoder>(
                //    qvars.len(),
                //).unwrap();
                //let upvar_tuple_ref = self.deps.require_ref::<crate::encoders::ViperTupleEncoder>(
                //    upvar_tys.len(),
                //).unwrap();

                let mut reify_args = vec![];
                // TODO: big hack!
                //   the problem is that we expect this to
                //   be a simple Expr, but `encode_operand`
                //   returns an ExprRet; do we need ExprRet
                //   to be piped throughout this encoder?
                //   alternatively, can we have an "unlift"
                //   operation, which will work like reify
                //   but panicking on a Lazy(..)?
                reify_args.push(unsafe {
                    std::mem::transmute(self.encode_operand(&curr_ver, &args[1]))
                });
                reify_args.extend((0..qvars.len())
                    .map(|idx| self.vcx.mk_local_ex(
                        vir::vir_format!(self.vcx, "qvar_{}_{idx}", self.encoding_depth),
                    )));

                // TODO: recursively invoke MirPure encoder to encode
                // the body of the closure; pass the closure as the
                // variable to use, then closure access = tuple access
                // (then hope to optimise this away later ...?)
                use vir::Reify;
                let body = self.deps.require_local::<MirPureEncoder>(
                    MirPureEncoderTask {
                        encoding_depth: self.encoding_depth + 1,
                        kind: PureKind::Closure,
                        parent_def_id: cl_def_id,
                        promoted: None,
                        param_env: self.vcx.tcx.param_env(cl_def_id),
                        substs: ty::List::identity_for_item(self.vcx.tcx, cl_def_id),
                        caller_def_id: self.def_id,
                    }
                ).unwrap().expr
                // arguments to the closure are
                // - the closure itself
                // - the qvars
                    .reify(self.vcx, (
                        cl_def_id,
                        self.vcx.alloc_slice(&reify_args),
                    ))
                    .lift();

                let bool = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    self.vcx.tcx.types.bool,
                ).unwrap();
                let bool = bool.expect_prim();

                bool.prim_to_snap.apply(self.vcx, [self.vcx.mk_forall_expr(
                    qvars,
                    &[], // TODO
                    bool.snap_to_prim.apply(self.vcx, [body]),
                )])
            }
        }
    }
}
