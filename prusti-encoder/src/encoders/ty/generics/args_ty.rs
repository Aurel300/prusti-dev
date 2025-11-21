use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::ViperIdent;

use crate::encoders::{
    ConstEnc,
    r#const::ConstEncTask,
    ty::{RustTyDecomposition, generics::params},
};

use super::{GArgs, GenericParamsEnc};

/// Encodes type arguments when calling a function in this context
pub struct GArgsTyEnc;

#[derive(Debug, Clone, Copy)]
pub struct GArgsTy<'vir> {
    ty_args: &'vir [vir::ExprTyVal<'vir>],
    const_args: &'vir [vir::ExprCSnap<'vir>],
}

impl<'vir> GArgsTy<'vir> {
    pub fn get_ty<Curr, Next>(&self) -> &'vir [vir::ExprGenTyVal<'vir, Curr, Next>] {
        let args = self.ty_args as *const [vir::ExprTyVal<'vir>]
            as *const [vir::ExprGenTyVal<'vir, Curr, Next>];
        unsafe { &*args }
    }

    pub fn get_const<Curr, Next>(&self) -> &'vir [vir::ExprGenCSnap<'vir, Curr, Next>] {
        let args = self.const_args as *const [vir::ExprCSnap<'vir>]
            as *const [vir::ExprGenCSnap<'vir, Curr, Next>];
        unsafe { &*args }
    }
}

impl TaskEncoder for GArgsTyEnc {
    task_encoder::encoder_cache!(GArgsTyEnc);
    type TaskDescription<'tcx> = GArgs<'tcx>;
    type OutputFullDependency<'vir> = GArgsTy<'vir>;
    type OutputFullLocal<'vir> = Option<vir::Domain<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in GArgsTyEnc::all_outputs_local_no_errors() {
            if let Some(dom) = output {
                program.add_domain(dom);
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let params = deps.require_dep::<GenericParamsEnc>(task_key.context)?;
        let mut builder = params::Builder {
            functions: Vec::new(),
            axioms: Vec::new(),
            domain_name: "",
        };
        let ty_args = task_key
            .args
            .iter()
            .copied()
            .filter_map(ty::GenericArg::as_type)
            .map(|arg| {
                let decomp = vir::with_vcx(|vcx| {
                    RustTyDecomposition::from_ty(arg, vcx.tcx(), task_key.context)
                });
                params.ty_expr(deps, decomp, &mut builder)
            })
            .collect::<Vec<_>>();
        let const_args = task_key
            .args
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(i, a)| ty::GenericArg::as_const(a).map(|a| (i, a)))
            .map(|(i, const_)| {
                // If the constant is a value, we already know its type.
                // Otherwise, we will look it up in the param environment.
                // TODO: what about the other ConstKind variants?
                let ty = match const_.kind() {
                    ty::ConstKind::Value(v) => v.ty,
                    _ => task_key.context.expect_const(i).1,
                };
                let task = ConstEncTask::Ty {
                    const_,
                    ty,
                    context: task_key.context,
                };
                deps.require_dep::<ConstEnc>(task)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let args = vir::with_vcx(|vcx| GArgsTy {
            ty_args: vcx.alloc_slice(&ty_args),
            const_args: vcx.alloc_slice(&const_args),
        });
        if builder.functions.len() > 0 {
            vir::with_vcx(|vcx| {
                Ok((
                    Some(vcx.mk_domain(
                        ViperIdent::new(builder.domain_name),
                        &[],
                        vcx.alloc_slice(&builder.axioms),
                        vcx.alloc_slice(&builder.functions),
                        None,
                    )),
                    args,
                ))
            })
        } else {
            Ok((None, args))
        }
    }
}
