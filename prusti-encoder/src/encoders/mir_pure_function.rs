use prusti_rustc_interface::{middle::{mir, ty}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;
use std::cell::RefCell;

use crate::encoders::{
    MirPureEncoder, MirPureEncoderTask, SpecEncoder, SpecEncoderTask, TypeEncoder,
};
pub struct MirFunctionEncoder;

#[derive(Clone, Debug)]
pub enum MirFunctionEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutputRef<'vir> {
    pub function_name: &'vir str,
}
impl<'vir> task_encoder::OutputRefAny<'vir> for MirFunctionEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutput<'vir> {
    pub function: vir::Function<'vir>,
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirFunctionEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirFunctionEncoder {
    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = MirFunctionEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncoderOutput<'vir>;

    type EncodingError = MirFunctionEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirFunctionEncoder>) -> R,
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
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        vir::with_vcx(|vcx| {
            let def_id = *task_key;

            tracing::debug!("encoding {def_id:?}");

            let function_name = vir::vir_format!(vcx, "f_{}", vcx.tcx.item_name(def_id));
            deps.emit_output_ref::<Self>(*task_key, MirFunctionEncoderOutputRef { function_name });

            let local_def_id = def_id.expect_local();
            let body = vcx.body.borrow_mut().get_impure_fn_body_identity(local_def_id);

            let spec = deps.require_local::<crate::encoders::pure::spec::MirSpecEncoder>(
                (def_id, true)
            ).unwrap();

            let mut func_args = Vec::with_capacity(body.arg_count);

            for (arg_idx0, arg_local) in body.args_iter().enumerate() {
                let arg_idx = arg_idx0 + 1; // enumerate is 0 based but we want to start at 1

                let arg_decl = body.local_decls.get(arg_local).unwrap();
                let arg_type_ref = deps.require_ref::<TypeEncoder>(arg_decl.ty).unwrap();

                let name_p = vir::vir_format!(vcx, "_{arg_idx}p");
                func_args.push(vcx.alloc(vir::LocalDeclData {
                    name: name_p,
                    ty: arg_type_ref.snapshot,
                }));
            }

            // TODO: dedup with mir_pure
            let attrs = vcx.tcx.get_attrs_unchecked(def_id);
            let is_trusted = attrs
                .iter()
                .filter(|attr| !attr.is_doc_comment())
                .map(|attr| attr.get_normal_item())
                .any(|item| {
                    item.path.segments.len() == 2
                        && item.path.segments[0].ident.as_str() == "prusti"
                        && item.path.segments[1].ident.as_str() == "trusted"
                });

            let expr = if is_trusted {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_local::<MirPureEncoder>(MirPureEncoderTask {
                        encoding_depth: 0,
                        parent_def_id: def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(def_id),
                        substs: ty::List::identity_for_item(vcx.tcx, def_id),
                    })
                    .unwrap()
                    .expr;

                Some(expr.reify(vcx, (def_id, &spec.pre_args.split_last().unwrap().1)))
            };

            // Snapshot type of the return type
            let ret = deps
                .require_ref::<TypeEncoder>(body.return_ty())
                .unwrap()
                .snapshot;

            tracing::debug!("finished {def_id:?}");

            Ok((
                MirFunctionEncoderOutput {
                    function: vcx.alloc(vir::FunctionData {
                        name: function_name,
                        args: vcx.alloc_slice(&func_args),
                        ret,
                        pres: vcx.alloc_slice(&spec.pres),
                        posts: vcx.alloc_slice(&spec.posts),
                        expr,
                    }),
                },
                (),
            ))
        })
    }
}
