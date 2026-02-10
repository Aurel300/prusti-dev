use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, Reify};

use crate::{
    encoders::{
        MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
        mir_fn::{CallTaskDescription, RustSignature},
        pure::spec::MirSpecEncMode,
        ty::generics::{
            GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc,
            traits::TraitEnc,
        },
    },
    trait_support::is_function_with_body,
};

// Function wrapper

pub struct FunctionCallEnc;

#[derive(Debug, Clone)]
pub struct FunctionCallEncOutput<'vir> {
    function: FunctionEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    inputs: Vec<GArgCaster<'vir, Pure>>,
    output: GArgCaster<'vir, Pure>,
}

impl<'vir> FunctionCallEncOutput<'vir> {
    pub fn call_pure<Curr, Next>(
        &self,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        let a = args.iter_mut().zip(self.inputs.iter());
        for (arg, caster) in a {
            *arg = caster.cast_to_callee_ctx(*arg);
        }
        let call = self.function.function_ref.call()(
            &args,
            self.ty_args.get_ty(),
            self.ty_args.get_const(),
        );
        self.output.cast_to_caller_ctx(call)
    }

    pub fn call_impure<Curr, Next>(
        &self,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        let a = args.iter_mut().zip(self.inputs.iter());
        for (arg, caster) in a {
            *arg = caster.cast_to_callee_ctx(*arg);
        }
        let call =
            self.function.caller_ref.call()(&args, self.ty_args.get_ty(), self.ty_args.get_const());
        self.output.cast_to_caller_ctx(call)
    }
}

impl TaskEncoder for FunctionCallEnc {
    task_encoder::encoder_cache!(FunctionCallEnc);
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = FunctionCallEncOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (callee_def_id, function_ref) = vir::with_vcx(|vcx| {
            if task_key.resolve_trait_calls
                && let Some(assoc_item) = vcx.tcx().opt_associated_item(task_key.callee)
                && let Some(trait_def_id) = assoc_item.trait_container(vcx.tcx())
            {
                let trait_item_def_id = assoc_item.def_id;
                let trait_enc = deps.require_dep::<TraitEnc>(trait_def_id)?;
                let assoc_enc = trait_enc.assoc_funcs.get(&trait_item_def_id).unwrap();
                let function_ref = FunctionEncOutputRef {
                    caller_ref: assoc_enc.call_stub_pure_caller.unwrap(),
                    function_ref: assoc_enc.call_stub_pure_function.unwrap(),
                };
                return Ok((trait_item_def_id, function_ref));
            }
            let function_ref = deps.require_ref::<FunctionEnc>(task_key.callee)?;
            Ok((task_key.callee, function_ref))
        })?;
        let signature = RustSignature::new(callee_def_id);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Pure>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?;
        Ok((
            (),
            FunctionCallEncOutput {
                function: function_ref,
                ty_args,
                inputs,
                output,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        FunctionEnc::emit_outputs(program);
    }
}

// Function encoder

struct FunctionEnc;

#[derive(Debug, Clone)]
pub struct FunctionEncOutputRef<'vir> {
    caller_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    function_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
struct FunctionEncOutput<'vir> {
    caller: vir::Function<'vir>,
    function: vir::Function<'vir>,
}

#[derive(Clone, Debug)]
pub enum FunctionEncError {}

impl TaskEncoder for FunctionEnc {
    task_encoder::encoder_cache!(FunctionEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = FunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = FunctionEncOutput<'vir>;

    type EncodingError = FunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let def_id = *task_key;
            let trusted = crate::encoders::is_function_trusted(def_id);
            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: true,
            })?;

            tracing::debug!("encoding {def_id:?}");

            let caller_ident =
                vir::vir_format_identifier!(vcx, "cf_{}", vcx.tcx().def_path_str(def_id));
            let function_ident =
                vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().def_path_str(def_id));
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;
            let caller_ref = FunctionIdn::new(
                caller_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            let function_ref = FunctionIdn::new(
                function_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            deps.emit_output_ref(
                def_id,
                FunctionEncOutputRef {
                    caller_ref,
                    function_ref,
                },
            )?;

            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let spec =
                deps.require_dep::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::PureWithResult))?;

            let expr = if trusted || !is_function_with_body(vcx.tcx(), def_id) {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_dep::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx().param_env(def_id),
                        substs,
                        caller_def_id: None,
                    })?
                    .expr;
                let expr = expr.reify(vcx, (def_id, spec.pre_args));
                assert!(
                    expr.ty() == return_type,
                    "expected {:?}, got {:?}",
                    return_type,
                    expr.ty()
                );
                Some(expr)
            };

            // TODO: type preconditions do not currently work
            /*
            let arg_type_assertions = local_defs.args().map(|arg| {
                let snap = vcx.mk_local_ex(arg.local_snap);
                generics.ty_assertion(deps, snap, arg.rust_ty)
            }).collect::<Vec<_>>();
            */

            tracing::debug!("finished {def_id:?}");

            let mut pres = Vec::new(); // arg_type_assertions;
            pres.extend(spec.pres);

            // TODO: type preconditions do not currently work
            /*
            let ret = local_defs.ret();
            let snap = vcx.mk_result(ret.local_snap.ty());
            let ret_type_assertions = generics.ty_assertion(deps, snap, ret.rust_ty);
            */
            let mut posts = Vec::new(); // vec![ret_type_assertions];
            posts.extend(spec.posts.into_iter().map(|post| {
                // use inhale-exhale expression to prevent viper checking that
                // the function body expression satisfies the postcondition:
                // that's checked in the method encoding of this function.
                vcx.mk_inhale_exhale_expr(post, vcx.mk_bool::<true>())
            }));

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let wrapped_call = function_ref.call()(
                &func_args
                    .iter()
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
                generics.ty_exprs(),
                generics.const_exprs(),
            );
            let caller = vcx.mk_function(
                caller_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                Some(wrapped_call),
            );
            let function = vcx.mk_function(
                function_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                &[], // vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                expr,
            );
            Ok((FunctionEncOutput { caller, function }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_function(output.caller);
            program.add_function(output.function);
        }
    }
}
