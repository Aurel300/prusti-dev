use crate::encoders::rust_ty_generic_cast::RustTyGenericCastEnc;
use prusti_rustc_interface::middle::ty;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::VirCtxt;

use super::{generic_cast::GenericCastOutputRef, lifted::LiftedTy};

#[derive(Copy, Hash, PartialEq, Eq, Clone, Debug)]
pub struct CastArgs<'tcx> {
    pub expected: ty::Ty<'tcx>,
    pub actual: ty::Ty<'tcx>,
}

#[derive(Copy, Clone)]
pub struct PureCast<'vir> {
    cast_function: vir::FunctionIdent<'vir, vir::UnknownArity<'vir>>,
    ty_args: &'vir [LiftedTy<'vir>],
}

impl<'vir> PureCast<'vir> {
    pub fn new(
        cast_function: vir::FunctionIdent<'vir, vir::UnknownArity<'vir>>,
        ty_args: &'vir [LiftedTy<'vir>],
    ) -> PureCast<'vir> {
        PureCast {
            cast_function,
            ty_args,
        }
    }
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.cast_function.apply(
            vcx,
            &std::iter::once(expr)
                .chain(self.ty_args.iter().map(|t| t.expr(vcx)))
                .collect::<Vec<_>>(),
        )
    }
 }

#[derive(Clone)]
pub enum PureGenericCastOutputRef<'vir> {
    NoCast,
    Cast(PureCast<'vir>),
}

impl<'vir> PureGenericCastOutputRef<'vir> {
    pub fn apply_cast_if_necessary<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'_>,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            PureGenericCastOutputRef::NoCast => expr,
            PureGenericCastOutputRef::Cast(PureCast {
                cast_function,
                ty_args,
            }) => cast_function.apply(
                vcx,
                &std::iter::once(expr)
                    .chain(ty_args.iter().map(|t| t.expr(vcx)))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    pub fn cast_function(&self) -> Option<PureCast<'vir>> {
        match self {
            PureGenericCastOutputRef::NoCast => None,
            PureGenericCastOutputRef::Cast(f) => Some(*f),
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for PureGenericCastOutputRef<'vir> {}

/// Returns necessary data to support casting the generic Viper representation
/// of a Rust expression to its concrete type, or vice versa, for function
/// applications. It takes as input a `CastArgs` struct, which contains the
/// parameter type a function expects, and the type of the argument. If the
/// function expects the concrete version of the type and the argument is
/// generic, it returns a function to casts the generic expression to its
/// concrete version. Likewise, if the function expects the generic version of
/// the type and the argument is concrete, it returns a function to cast the
/// concrete expression to its generic version. Otherwise, no cast is necessary
/// and it returns `PureGenericCastOutputRef::NoCast`.
pub struct PureGenericCastEnc;

impl TaskEncoder for PureGenericCastEnc {
    task_encoder::encoder_cache!(PureGenericCastEnc);
    type TaskDescription<'tcx> = CastArgs<'tcx>;
    type OutputRef<'vir> = PureGenericCastOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();
    type EncodingError = ();

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
        let expected_is_param = matches!(task_key.expected.kind(), ty::Param(_));
        let actual_is_param = matches!(task_key.actual.kind(), ty::Param(_));
        let output_ref = if expected_is_param == actual_is_param {
            PureGenericCastOutputRef::NoCast
        } else {
            if actual_is_param {
                // expected is concrete type, `actual` should be concretized
                let generic_cast = deps
                    .require_local::<RustTyGenericCastEnc>(task_key.expected)
                    .unwrap();
                if let GenericCastOutputRef::CastFunctions { make_concrete, .. } = generic_cast.cast
                {
                    PureGenericCastOutputRef::Cast(PureCast::new(
                        make_concrete,
                        generic_cast.ty_args,
                    ))
                } else {
                    unreachable!()
                }
            } else {
                // expected is generic type, `actual` should be be made generic
                let generic_cast = deps
                    .require_local::<RustTyGenericCastEnc>(task_key.actual)
                    .unwrap();
                if let GenericCastOutputRef::CastFunctions { make_generic, .. } = generic_cast.cast
                {
                    PureGenericCastOutputRef::Cast(PureCast::new(
                        make_generic,
                        generic_cast.ty_args,
                    ))
                } else {
                    unreachable!()
                }
            }
        };
        deps.emit_output_ref::<Self>(*task_key, output_ref);
        Ok(((), ()))
    }
}
