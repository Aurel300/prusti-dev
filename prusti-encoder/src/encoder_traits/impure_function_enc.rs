use prusti_rustc_interface::middle::{ty, mir};
use prusti_interface::specs::typed::ProcedureKind;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{self, MethodIdent, UnknownArity, ViperIdent};

use crate::encoders::{
    lifted::func_def_ty_params::LiftedTyParamsEnc,
    ImpureEncVisitor,
    MirImpureEnc,
    MirLocalDefEnc,
    MirSpecEnc,
    rust_ty_predicates::RustTyPredicatesEnc,
    predicate,
};

use super::function_enc::FunctionEnc;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncError;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for ImpureFunctionEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

const ENCODE_REACH_BB: bool = false;

pub trait ImpureFunctionEnc
where
    Self: 'static
        + Sized
        + FunctionEnc
        + for<'vir> TaskEncoder<OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>>,
{
    /// Generates the identifier for the method; for a monomorphic encoding,
    /// this should be a name including (mangled) type arguments
    fn mk_method_ident<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        task_key: &Self::TaskKey<'vir>,
    ) -> ViperIdent<'vir>;

    fn encode<'vir>(
        task_key: Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<
        ImpureFunctionEncOutput<'vir>,
        EncodeFullError<'vir, Self>,
    > {
        let def_id = Self::get_def_id(&task_key);
        let caller_def_id = Self::get_caller_def_id(&task_key);
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;
            let substs = Self::get_substs(vcx, &task_key);
            let local_defs = deps
                .require_local::<MirLocalDefEnc>((def_id, substs, caller_def_id))?;

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters
            let arg_count = local_defs.arg_count + 1;

            let method_name = Self::mk_method_ident(vcx, &task_key);
            let mut args = vec![&vir::TypeData::Ref; arg_count];
            let param_ty_decls = deps
                .require_local::<LiftedTyParamsEnc>(substs)?
                .iter()
                .map(|g| g.decl())
                .collect::<Vec<_>>();
            args.extend(param_ty_decls.iter().map(|decl| decl.ty));
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let method_ref = MethodIdent::new(method_name, args);
            deps.emit_output_ref(task_key, ImpureFunctionEncOutputRef { method_ref })?;

            // Do not encode the method body if it is external, trusted or just
            // a call stub.
            let local_def_id = def_id.as_local().filter(|_| !trusted);
            let blocks = if let Some(local_def_id) = local_def_id {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);
                // let body = vcx.tcx().mir_promoted(local_def_id).0.borrow();

                let fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx());

                //let ssa_analysis = SsaAnalysis::analyse(&body);

                let block_count = body.basic_blocks.len();

                // Local count for the Viper method:
                // - one for each basic block;
                // - one (`Ref`) for each non-argument, non-return local.
                let _local_count = block_count + 1 * (body.local_decls.len() - arg_count);

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    let name_p = local_defs.locals[local].local.name;
                    start_stmts.push(
                        vcx.mk_local_decl_stmt(vir::vir_local_decl! { vcx; [name_p] : Ref }, None),
                    )
                }
                if ENCODE_REACH_BB {
                    start_stmts.extend((0..block_count).map(|block| {
                        let name = vir::vir_format!(vcx, "_reach_bb{block}");
                        vcx.mk_local_decl_stmt(
                            vir::vir_local_decl! { vcx; [name] : Bool },
                            Some(vcx.mk_todo_expr("false")),
                        )
                    }));
                }
                encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::Start),
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(vcx.alloc(vir::CfgBlockLabelData::BasicBlock(0))),
                ));

                let mut visitor = ImpureEncVisitor {
                    monomorphize: MirImpureEnc::monomorphize(),
                    vcx,
                    deps,
                    def_id,
                    substs,
                    local_decls: &body.local_decls,
                    //ssa_analysis,
                    fpcs_analysis,
                    local_defs,

                    tmp_ctr: 0,

                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                visitor.visit_body(&body);

                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    &[],
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));
                Some(vcx.alloc_slice(&visitor.encoded_blocks))
            } else {
                None
            };

            let proc_kind = crate::encoders::with_proc_spec(
                    def_id,
                    |def_spec| def_spec.proc_kind
                )
                .unwrap_or(ProcedureKind::Method);

            let spec = deps
                .require_local::<MirSpecEnc>((def_id, substs, None, false, false))?;
            let (spec_pres, spec_posts, spec_async_invs) = (spec.pres, spec.posts, spec.async_invariants);

            // TODO: fix capacity?
            let mut pres = Vec::with_capacity(arg_count - 1);
            let mut args = Vec::with_capacity(arg_count + substs.len());
            for arg_idx in 0..arg_count {
                let name_p = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != 0 {
                    pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                }
            }
            args.extend(param_ty_decls.iter());
            pres.extend(spec_pres);

            // in the case of an async body, we additionally require that the ghost fields
            // capturing the initial upvar state are equal to the upvar fields
            // as well as that all invariants hold initially
            if matches!(proc_kind, ProcedureKind::AsyncPoll) {
                let gen_ty = vcx.tcx().type_of(def_id).skip_binder();
                let fields = {
                    let gen_ty = deps.require_ref::<RustTyPredicatesEnc>(gen_ty)?;
                    gen_ty.generic_predicate.expect_structlike().snap_data.field_access
                };
                let upvar_tys = {
                    let ty::TyKind::Generator(_, args, _) = gen_ty.kind() else {
                        panic!("expected generator TyKind to be Generator");
                    };
                    args.as_generator().upvar_tys()
                };
                let n_upvars = upvar_tys.len();
                assert_eq!(fields.len(), 2 * upvar_tys.len());
                let gen_snap = local_defs.locals[1_u32.into()].impure_snap;
                for (i, ty) in upvar_tys.iter().enumerate() {
                    let field = fields[i].read.apply(vcx, [gen_snap]);
                    let ghost_field = fields[n_upvars + i].read.apply(vcx, [gen_snap]);
                    pres.push(vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, field, ghost_field));
                }

                for inv in spec_async_invs {
                    pres.push(inv);
                }
            }

            let mut posts = Vec::with_capacity(spec_posts.len() + 1);
            posts.push(local_defs.locals[mir::RETURN_PLACE].impure_pred);
            posts.extend(spec_posts);

            // in the case of a future constructor, we also ensure that the generator's upvar and
            // ghost fields are set correctly
            // NOTE: this detection mechanism is not always correct, specifically, it does not
            // correctly mark the future constructors of async fn's without specifications as such,
            // but this should not matter, as the caller cannot obtain guarantees about this
            // future type anyways
            if matches!(proc_kind, ProcedureKind::AsyncConstructor) {
                let gen_domain = local_defs.locals[0_u32.into()].ty;
                let fields = gen_domain.expect_structlike().snap_data.field_access;
                let n_upvars = local_defs.arg_count;
                assert_eq!(fields.len(), 2 * n_upvars);
                let gen_snap = local_defs.locals[0_u32.into()].impure_snap;
                for i in 0 .. n_upvars {
                    let arg = vcx.mk_old_expr(local_defs.locals[(i + 1).into()].impure_snap);
                    let upvar_field = fields[i].read.apply(vcx, [gen_snap]);
                    let ghost_field = fields[n_upvars + i].read.apply(vcx, [gen_snap]);
                    posts.push(vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, upvar_field, arg));
                    posts.push(vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, ghost_field, arg));
                }
            }

            Ok(ImpureFunctionEncOutput {
                method: vcx.mk_method(
                    method_ref,
                    vcx.alloc_slice(&args),
                    &[],
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    blocks,
                ),
            })
        })
    }
}
