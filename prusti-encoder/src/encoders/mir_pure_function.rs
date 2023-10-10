use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};


use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::Reify;

pub struct MirFunctionEncoder;

#[derive(Clone, Debug)]
pub enum MirFunctionEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutputRef<'vir> {
    pub method_name: &'vir str,
}
impl<'vir> task_encoder::OutputRefAny<'vir> for MirFunctionEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutput<'vir> {
    pub method: vir::Function<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirFunctionEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirFunctionEncoder {
    // TODO: local def id (+ promoted, substs, etc)
    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = MirFunctionEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncoderOutput<'vir>;

    type EncodingError = MirFunctionEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
        where F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirFunctionEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        use mir::visit::Visitor;
        vir::with_vcx(|vcx| {
            let def_id = task_key;
            let method_name = vir::vir_format!(vcx, "pure_{}", vcx.tcx.item_name(*def_id));
            deps.emit_output_ref::<Self>(*task_key, MirFunctionEncoderOutputRef {
                method_name,
            });

            let local_def_id = def_id.expect_local();
            let body = unsafe {
                prusti_interface::environment::mir_storage::retrieve_promoted_mir_body(vcx.tcx, local_def_id)
            };
            // let body = vcx.tcx.mir_promoted(local_def_id).0.borrow();

            //let ssa_analysis = SsaAnalysis::analyse(&body);

            let fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx);

            let local_types = body.local_decls.iter()
                .map(|local_decl| deps.require_ref::<crate::encoders::TypeEncoder>(
                    local_decl.ty,
                ).unwrap())
                .collect::<IndexVec<mir::Local, _>>();

            let specs = deps.require_local::<crate::encoders::SpecEncoder>(
                crate::encoders::SpecEncoderTask {
                    def_id: *def_id,
                }
            ).unwrap();

            let pre_args = vcx.alloc_slice(&(1..=body.arg_count)
                .map(|local| vcx.mk_func_app(
                    local_types[local.into()].function_snap,
                    &[vcx.mk_local_ex(
                        vir::vir_format!(vcx, "_{local}p"),
                    )],
                ))
                .collect::<Vec<vir::Expr<'_>>>());

            let spec_pres = specs.pres.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEncoder>(
                    crate::encoders::MirPureEncoderTask {
                        encoding_depth: 0,
                        parent_def_id: *spec_def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs: ty::List::identity_for_item(vcx.tcx, *spec_def_id),
                    }
                ).unwrap().expr;
                expr.reify(vcx, (*spec_def_id, pre_args))
            }).collect::<Vec<vir::Expr<'_>>>();

            // TODO: duplication ...
            let mut post_args = (1..=body.arg_count)
                .map(|local| vcx.mk_func_app(
                    local_types[local.into()].function_snap,
                    &[vcx.mk_local_ex(
                        vir::vir_format!(vcx, "_{local}p"),
                    )],
                ))
                .collect::<Vec<vir::Expr<'_>>>();
            post_args.push(vcx.mk_func_app(
                local_types[mir::RETURN_PLACE].function_snap,
                &[vcx.mk_local_ex(vir::vir_format!(vcx, "_0p"))],
            ));
            let post_args = vcx.alloc_slice(&post_args);
            let spec_posts = specs.posts.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEncoder>(
                    crate::encoders::MirPureEncoderTask {
                        encoding_depth: 0,
                        parent_def_id: *spec_def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs: ty::List::identity_for_item(vcx.tcx, *spec_def_id),
                    }
                ).unwrap().expr;
                expr.reify(vcx, (*spec_def_id, post_args))
            }).collect::<Vec<vir::Expr<'_>>>();

            let block_count = body.basic_blocks.reverse_postorder().len();

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
            let arg_count = 1 + 1 * body.arg_count;

            // Local count for the Viper method:
            // - one for each basic block;
            // - one (`Ref`) for each non-argument, non-return local.
            let _local_count = block_count + 1 * (body.local_decls.len() - body.arg_count - 1);

            let mut encoded_blocks = Vec::with_capacity(
                // extra blocks: Start, End
                2 + block_count,
            );
            let mut pres = Vec::new(); // TODO: capacity
            let mut start_stmts = (body.arg_count + 1..body.local_decls.len())
                .map(|local| {
                    let name_p = vir::vir_format!(vcx, "_{local}p");
                    vec![
                        vcx.alloc(vir::StmtData::LocalDecl(
                            vir::vir_local_decl! { vcx; [name_p] : Ref },
                            None,
                        )),
                        vcx.alloc(vir::StmtData::Inhale(
                            vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                                target: local_types[local.into()].predicate_name,
                                args: vcx.alloc_slice(&[
                                    vcx.mk_local_ex(name_p),
                                ]),
                            })))
                        )),
                    ]
                })
                .flatten()
                .collect::<Vec<_>>();
            
            encoded_blocks.push(vcx.alloc(vir::CfgBlockData {
                label: vcx.alloc(vir::CfgBlockLabelData::Start),
                stmts: vcx.alloc_slice(&start_stmts),
                terminator: vcx.alloc(vir::TerminatorStmtData::Goto(
                    vcx.alloc(vir::CfgBlockLabelData::BasicBlock(0)),
                )),
            }));

            let mut args = Vec::with_capacity(arg_count * 2);
            for arg_idx in 0..=body.arg_count {
                let name_p = vir::vir_format!(vcx, "_{arg_idx}p");
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                pres.push(vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                    target: local_types[arg_idx.into()].predicate_name,
                    args: vcx.alloc_slice(&[vcx.mk_local_ex(name_p)]),
                }))));
            }
            pres.extend(spec_pres);

            let mut posts = Vec::new(); // TODO: capacity
            posts.push(vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                target: local_types[mir::RETURN_PLACE].predicate_name,
                args: vcx.alloc_slice(&[vcx.mk_local_ex("_0p")]),
            }))));
            posts.extend(spec_posts);
           

            Ok((MirFunctionEncoderOutput {
                method: vcx.alloc(vir::FunctionData {
                    name: method_name,
                    args: vcx.alloc_slice(&args),
                    ret: &vir::TypeData::Int,
                    pres: vcx.alloc_slice(&pres),
                    posts: vcx.alloc_slice(&posts),
                    expr: None, //TODO
                }),
            }, ()))
        })
    }
}
