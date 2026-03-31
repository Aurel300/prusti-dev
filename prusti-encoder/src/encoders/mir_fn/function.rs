use prusti_rustc_interface::{
    middle::ty,
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, Reify};

use crate::{
    encoders::{
        MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
        mir_fn::{CallTaskDescription, RustSignature},
        pure::spec::MirSpecEncMode,
        ty::generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc},
    },
    trait_support::is_function_with_body,
};

// Function wrapper

pub struct FunctionCallEnc;

pub enum CallingCtxt {
    Pure,
    PureRec,
    Impure,
}

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
        recursive: bool,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        let a = args.iter_mut().zip(self.inputs.iter());
        for (arg, caster) in a {
            *arg = caster.cast_to_callee_ctx(*arg);
        }
        let caller_ref =
            if recursive {
                self.function.limited_fn_ref
            } else {
                self.function.unlimited_fn_ref
            };
        let call = caller_ref.call()(&args, self.ty_args.get_ty(), self.ty_args.get_const());
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
        let (callee_def_id, assoc_enc) = task_key.trait_call(deps)?;
        let function_ref = if let Some(assoc_enc) = assoc_enc {
            FunctionEncOutputRef {
                unlimited_fn_ref: assoc_enc.call_stub_pure_function.unwrap(),
                // TODO I think this is fine for spec fns?
                limited_fn_ref: assoc_enc.call_stub_pure_function.unwrap(),
                caller_fn_ref: assoc_enc.call_stub_pure_caller.unwrap(),
            }
        } else {
            deps.require_ref::<FunctionEnc>(task_key.callee)?
        };
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
struct FunctionEncOutputRef<'vir> {
    unlimited_fn_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    caller_fn_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    limited_fn_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    // TODO remove
    // caller_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    // function_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
struct FunctionEncOutput<'vir> {
    defn_axiom: Option<vir::DomainAxiom<'vir>>,
    unlimited_fn: vir::DomainFunction<'vir>,
    limited_axiom: vir::DomainAxiom<'vir>,
    limited_fn: vir::DomainFunction<'vir>,
    caller_fn: vir::Function<'vir>,
    // TODO remove
    // caller: vir::Function<'vir>,
    // function: vir::Function<'vir>,
}

#[derive(Clone, Debug)]
pub enum FunctionEncError {}

impl TaskEncoder for FunctionEnc {
    task_encoder::encoder_cache!(FunctionEnc);
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = FunctionEncOutputRef<'vir>; // TODO should be different for pure & impure ctxt
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

            // TODO remove
            // let caller_ident =
            //     vir::vir_format_identifier!(vcx, "cf_{}", vcx.tcx().def_path_str(def_id));
            // let function_ident =
            //     vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().def_path_str(def_id));
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;

            let unlimited_fn_ref = {
                let ident = vir::vir_format_identifier!(
                    vcx,
                    "unlimited_{}",
                    vcx.tcx().def_path_str(def_id)
                );
                FunctionIdn::new(
                    ident,
                    (arg_types, generics.ty_args(), generics.const_args()),
                    return_type,
                )
            };
            let caller_fn_ref = {
                let ident =
                    vir::vir_format_identifier!(vcx, "caller_{}", vcx.tcx().def_path_str(def_id));
                FunctionIdn::new(
                    ident,
                    (arg_types, generics.ty_args(), generics.const_args()),
                    return_type,
                )
            };

            let limited_fn_ref = {
                let ident =
                    vir::vir_format_identifier!(vcx, "limited_{}", vcx.tcx().def_path_str(def_id));
                FunctionIdn::new(
                    ident,
                    (arg_types, generics.ty_args(), generics.const_args()),
                    return_type,
                )
            };

            deps.emit_output_ref(
                def_id,
                FunctionEncOutputRef {
                    unlimited_fn_ref,
                    caller_fn_ref,
                    limited_fn_ref,
                },
            )?;

            // TODO: type preconditions do not currently work
            /*
            let arg_type_assertions = local_defs.args().map(|arg| {
                let snap = vcx.mk_local_ex(arg.local_snap);
                generics.ty_assertion(deps, snap, arg.rust_ty)
            }).collect::<Vec<_>>();
            */

            tracing::debug!("finished {def_id:?}");

            let local_args = local_defs
                .local_decl_args()
                .map(|decl| vcx.mk_local_ex(decl))
                .collect::<Vec<_>>();

            let generic_args = generics
                .ty_decls()
                .iter()
                .map(|decl| vcx.mk_local_ex(decl))
                .collect::<Vec<_>>();

            let const_args = generics
                .const_decls()
                .iter()
                .map(|decl| vcx.mk_local_ex(decl))
                .collect::<Vec<_>>();

            let limited_fn = vcx.mk_domain_function(limited_fn_ref, false, None);

            let unlimited_fn_app = unlimited_fn_ref(
                &local_args,
                generics.ty_exprs(),
                generics.const_exprs(),
            );

            let arg_qvars = local_defs
                .local_decl_args()
                .map(|decl| decl.as_dyn())
                .chain(generics.ty_decls().iter().map(|decl| decl.as_dyn()))
                .chain(generics.const_decls().iter().map(|decl| decl.as_dyn()))
                .collect::<Vec<_>>();

            let limited_axiom = {
                let axiom_body = {
                    let limited_fn_app = limited_fn_ref(&local_args, &generic_args, &const_args);

                    vcx.mk_forall_expr(
                        vcx.alloc_slice(&arg_qvars),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[unlimited_fn_app])]),
                        vcx.mk_eq_expr(unlimited_fn_app, limited_fn_app),
                    )
                };

                let axiom_ident =
                    vir::vir_format_identifier!(vcx, "Limited_{}", vcx.tcx().def_path_str(def_id));

                vcx.mk_domain_axiom(axiom_ident, axiom_body)
            };

            let unlimited_fn = vcx.mk_domain_function(unlimited_fn_ref, false, None);

            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let spec = deps.require_dep::<MirSpecEnc>((def_id, true))?;

            let defn_axiom = if trusted || !is_function_with_body(vcx.tcx(), def_id) {
                None
            } else {
                let fn_body = deps
                    .require_dep::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx().param_env(def_id),
                        substs,
                        caller_def_id: None,
                    })?
                    .expr;
                let fn_body = fn_body.reify(vcx, (def_id, spec.pre_args));
                assert!(
                    fn_body.ty() == return_type,
                    "expected {:?}, got {:?}",
                    return_type,
                    fn_body.ty()
                );

                let axiom_body = {
                    let limited_fn_app =
                        limited_fn_ref(&local_args, &generic_args, &const_args).as_dyn();
                    let mut triggers = local_defs
                        .args()
                        .filter_map(|local_def| {
                            let trig = local_def.local_trig?.as_dyn();
                            Some(vcx.mk_trigger(&[trig, &limited_fn_app]))
                        })
                        .collect::<Vec<_>>();
                    triggers.push(vcx.mk_trigger(&[unlimited_fn_app]));

                    vcx.mk_forall_expr(
                        vcx.alloc_slice(&arg_qvars),
                        vcx.alloc_slice(&triggers[..]),
                        vcx.mk_eq_expr(unlimited_fn_app, fn_body),
                    )
                };

                let axiom_ident =
                    vir::vir_format_identifier!(vcx, "Defn_{}", vcx.tcx().def_path_str(def_id));

                Some(vcx.mk_domain_axiom(axiom_ident, axiom_body))
            };

            let mut pres = Vec::new(); // arg_type_assertions;
            pres.extend(spec.pres);

            // TODO: type preconditions do not currently work
            /*
            let ret = local_defs.ret();
            let snap = vcx.mk_result(ret.local_snap.ty());
            let ret_type_assertions = generics.ty_assertion(deps, snap, ret.rust_ty);
            */
            let posts = spec
                .posts
                .into_iter()
                .map(|post| {
                    // use inhale-exhale expression to prevent viper checking that
                    // the function body expression satisfies the postcondition:
                    // that's checked in the method encoding of this function.
                    vcx.mk_inhale_exhale_expr(post, vcx.mk_bool::<true>())
                })
                .collect::<Vec<_>>();

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let caller_fn = vcx.mk_function(
                caller_fn_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                None,
                Some(unlimited_fn_app),
            );

            Ok((
                FunctionEncOutput {
                    defn_axiom,
                    unlimited_fn,
                    limited_axiom,
                    limited_fn,
                    caller_fn,
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let mut domain_axioms = Vec::new();
        let mut domain_fns = Vec::new();
        for output in Self::all_outputs_local_no_errors() {
            if let Some(axiom) = output.defn_axiom {
                domain_axioms.push(axiom)
            };
            domain_fns.push(output.unlimited_fn);
            domain_axioms.push(output.limited_axiom);
            domain_fns.push(output.limited_fn);
            program.add_function(output.caller_fn);
        }

        vir::with_vcx(|vcx| {
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("PureFns"),
                &[],
                vcx.alloc_slice(&domain_axioms),
                vcx.alloc_slice(&domain_fns),
                None,
            );
            program.add_domain(domain);
        });
    }
}
