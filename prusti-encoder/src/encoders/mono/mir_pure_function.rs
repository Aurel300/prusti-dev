use prusti_rustc_interface::middle::mir;

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, FunctionIdent, Reify, UnknownArity};

use crate::encoders::{
    domain::DomainEnc,
    lifted::{
        func_def_ty_params::LiftedTyParamsEnc,
        ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
    },
    mir_pure::PureKind,
    mir_pure_function::{MirFunctionEncError, MirFunctionEncOutput, MirFunctionEncOutputRef},
    most_generic_ty::extract_type_params,
    GenericEnc, MirFunctionEnc, MirLocalDefEnc, MirPureEnc, MirPureEncTask, MirSpecEnc,
};

pub struct MirMonoFunctionEnc;

impl TaskEncoder for MirMonoFunctionEnc {
    task_encoder::encoder_cache!(MirMonoFunctionEnc);

    type TaskDescription<'vir> = <MirFunctionEnc as TaskEncoder>::TaskDescription<'vir>;

    type OutputRef<'vir> = MirFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncOutput<'vir>;

    type EncodingError = MirFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
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
        let (def_id, substs, caller_def_id) = *task_key;
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();

        vir::with_vcx(|vcx| {
            let local_defs = deps
                .require_local::<MirLocalDefEnc>((def_id, substs, Some(caller_def_id)))
                .unwrap();

            tracing::debug!("encoding {def_id:?}");

            let extra: String = substs.iter().map(|s| format!("_{s}")).collect();
            let (krate, index) = (caller_def_id.krate, caller_def_id.index.index());
            let function_name = vir::vir_format_identifier!(
                vcx,
                "f_{}{extra}_CALLER_{krate}_{index}",
                vcx.tcx().item_name(def_id)
            );
            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut ident_args = ty_arg_decls.iter().map(|arg| arg.ty()).collect::<Vec<_>>();
            ident_args.extend(
                (1..=local_defs.arg_count)
                    .map(mir::Local::from)
                    .map(|def_idx| local_defs.locals[def_idx].ty.snapshot),
            );
            let ident_args = UnknownArity::new(vcx.alloc_slice(&ident_args));
            let return_type = local_defs.locals[mir::RETURN_PLACE].ty;
            let function_ref = FunctionIdent::new(function_name, ident_args, return_type.snapshot);
            deps.emit_output_ref::<Self>(*task_key, MirFunctionEncOutputRef { function_ref });

            let spec = deps
                .require_local::<MirSpecEnc>((def_id, substs, None, true))
                .unwrap();

            let mut func_args = ty_arg_decls
                .iter()
                .map(|arg| arg.decl())
                .collect::<Vec<_>>();
            func_args.extend((1..=local_defs.arg_count).map(mir::Local::from).map(|arg| {
                vcx.alloc(vir::LocalDeclData {
                    name: local_defs.locals[arg].local.name,
                    ty: local_defs.locals[arg].ty.snapshot,
                })
            }));

            let expr = if trusted {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_local::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx().param_env(def_id),
                        substs,
                        caller_def_id: Some(caller_def_id),
                    })
                    .unwrap()
                    .expr;

                let expr = expr.reify(vcx, (def_id, spec.pre_args));
                assert!(
                    expr.ty() == return_type.snapshot,
                    "expected {:?}, got {:?}",
                    return_type.snapshot,
                    expr.ty()
                );
                Some(expr)
            };

            let sig = vcx.tcx().fn_sig(def_id);
            let input_tys = vcx
                .tcx()
                .subst_and_normalize_erasing_regions(substs, vcx.tcx().param_env(def_id), sig)
                .inputs()
                .iter()
                .map(|i| i.skip_binder())
                .copied()
                .collect::<Vec<_>>();
            let generic_enc = deps.require_ref::<GenericEnc>(()).unwrap();
            let type_preconditions = input_tys.iter().enumerate().filter_map(|(idx, ty)| {
                let vir_arg = local_defs.locals[mir::Local::from(idx + 1)];
                let vir_arg = vcx.mk_local_ex(vir_arg.local.name, vir_arg.ty.snapshot);
                let lifted_ty = deps
                    .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*ty)
                    .unwrap();
                match lifted_ty {
                    LiftedTy::Generic(generic) => Some(vcx.mk_eq_expr(
                        generic_enc.param_type_function.apply(vcx, [vir_arg]),
                        generic.expr(vcx),
                    )),
                    LiftedTy::Instantiated { args, .. } if !args.is_empty() => {
                        let domain_ref = deps
                            .require_ref::<DomainEnc>(extract_type_params(vcx.tcx(), *ty).0)
                            .unwrap();
                        Some(vcx.mk_eq_expr(
                            domain_ref.typeof_function.apply(vcx, [vir_arg]),
                            lifted_ty.expr(vcx),
                        ))
                    }
                    _ => None,
                }
            });

            tracing::debug!("finished {def_id:?}");

            let mut pres = spec.pres;
            pres.extend(type_preconditions);

            Ok((
                MirFunctionEncOutput {
                    function: vcx.mk_function(
                        function_name.to_str(),
                        vcx.alloc_slice(&func_args),
                        return_type.snapshot,
                        vcx.alloc_slice(&pres),
                        vcx.alloc_slice(&spec.posts),
                        expr,
                    ),
                },
                (),
            ))
        })
    }
}
