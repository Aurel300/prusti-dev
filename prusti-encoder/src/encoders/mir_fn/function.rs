use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, Reify};

use crate::encoders::{
    MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
    mir_fn::{CallTaskDescription, RustSignature},
    ty::generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc},
};

// Function wrapper

pub struct FunctionCallEnc;

pub enum CallingCtxt {
    Pure,
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
    pub fn call<Curr, Next>(
        &self,
        calling_ctxt: CallingCtxt,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        let a = args.iter_mut().zip(self.inputs.iter());
        for (arg, caster) in a {
            *arg = caster.cast_to_callee_ctx(*arg);
        }
        let call = match calling_ctxt {
            CallingCtxt::Pure => self.function.domain_fn_ref.call()(
                &args,
                self.ty_args.get_ty(),
                self.ty_args.get_const(),
            ),
            CallingCtxt::Impure => self.function.caller_fn_ref.call()(
                &args,
                self.ty_args.get_ty(),
                self.ty_args.get_const(),
            ),
        };
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
        let function_ref = deps.require_ref::<FunctionEnc>(task_key.callee)?;
        let signature = RustSignature::new(task_key.callee);
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
    domain_fn_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    caller_fn_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
struct FunctionEncOutput<'vir> {
    defn_axiom: Option<vir::DomainAxiom<'vir>>,
    domain_fn: vir::DomainFunction<'vir>,
    caller_fn: vir::Function<'vir>,
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

            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;

            let domain_fn_ref = {
                let ident =
                    vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().def_path_str(def_id));
                FunctionIdn::new(
                    ident,
                    (arg_types, generics.ty_args(), generics.const_args()), // NOTE: look here
                    return_type,
                )
            };

            let caller_fn_ref = {
                let ident =
                    vir::vir_format_identifier!(vcx, "caller_{}", vcx.tcx().def_path_str(def_id));
                FunctionIdn::new(
                    ident,
                    (arg_types, generics.ty_args(), generics.const_args()), // NOTE: look here
                    return_type,
                )
            };

            deps.emit_output_ref(
                def_id,
                FunctionEncOutputRef {
                    domain_fn_ref,
                    caller_fn_ref,
                },
            )?;

            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let spec = deps.require_dep::<MirSpecEnc>((def_id, true))?;

            // TODO: type preconditions do not currently work
            /*
            let arg_type_assertions = local_defs.args().map(|arg| {
                let snap = vcx.mk_local_ex(arg.local_snap);
                generics.ty_assertion(deps, snap, arg.rust_ty)
            }).collect::<Vec<_>>();
            */

            tracing::debug!("finished {def_id:?}");

            let domain_fn = vcx.mk_domain_function(domain_fn_ref, false, None);

            let domain_fn_app = domain_fn_ref(
                &local_defs
                    .local_decl_args()
                    .map(|decl| vcx.mk_local_ex(decl))
                    .collect::<Vec<_>>(),
                &generics
                    .ty_decls()
                    .iter()
                    .map(|decl| vcx.mk_local_ex(decl))
                    .collect::<Vec<_>>(),
                &generics
                    .const_decls()
                    .iter()
                    .map(|decl| vcx.mk_local_ex(decl))
                    .collect::<Vec<_>>(),
            );

            let defn_axiom = if trusted {
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
                    let mut qvars = local_defs
                        .local_decl_args()
                        .map(|decl| decl.as_dyn())
                        .collect::<Vec<_>>();
                    qvars.extend(generics.ty_decls().iter().map(|decl| decl.as_dyn()));
                    qvars.extend(generics.const_decls().iter().map(|decl| decl.as_dyn()));

                    vcx.mk_forall_expr(
                        vcx.alloc_slice(&qvars),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[domain_fn_app])]),
                        vcx.mk_eq_expr(domain_fn_app, fn_body),
                    )
                };

                let axiom_ident =
                    vir::vir_format_identifier!(vcx, "defn_{}", vcx.tcx().def_path_str(def_id));

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
            let mut posts = Vec::new(); // vec![ret_type_assertions];
            posts.extend(spec.posts);

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let caller_fn = vcx.mk_function(
                caller_fn_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                None,
                Some(domain_fn_app),
            );

            Ok((
                FunctionEncOutput {
                    defn_axiom,
                    domain_fn,
                    caller_fn,
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let mut defn_axioms = Vec::new();
        let mut domain_fns = Vec::new();
        for output in Self::all_outputs_local_no_errors() {
            if let Some(axiom) = output.defn_axiom {
                defn_axioms.push(axiom)
            };
            domain_fns.push(output.domain_fn);
            program.add_function(output.caller_fn);
        }
        vir::with_vcx(|vcx| {
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("PureFns"),
                &[],
                vcx.alloc_slice(&defn_axioms),
                vcx.alloc_slice(&domain_fns),
                None,
            );
            program.add_domain(domain);
        });
    }
}
