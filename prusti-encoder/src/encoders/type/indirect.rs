use pcg::borrow_pcg::region_projection::LifetimeProjection;
use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::lifted::{casters::CastTypePure, rust_ty_cast::RustTyCastersEnc};

use super::{ty_impure::TyImpureEnc, ty_pure::TyPureEnc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IndirectKey {
    Early(ty::EarlyParamRegion),
    Late(ty::BoundRegionKind),
    Var(ty::RegionVid),
    Param(ty::ParamTy),
}

impl IndirectKey {
    pub fn from_generic_arg(ga: ty::GenericArg) -> Option<Self> {
        match ga.kind() {
            ty::GenericArgKind::Lifetime(region) => Self::from_region(region),
            ty::GenericArgKind::Type(ty) => match *ty.kind() {
                ty::TyKind::Param(p) => Some(IndirectKey::Param(p)),
                _ => None,
            },
            ty::GenericArgKind::Const(_) => None,
        }
    }

    pub fn from_region(region: ty::Region) -> Option<Self> {
        use ty::RegionKind;
        match region.kind() {
            RegionKind::ReEarlyParam(e) => Some(IndirectKey::Early(e)),
            RegionKind::ReBound(_, g) => Some(IndirectKey::Late(g.kind)),
            RegionKind::ReLateParam(_r) => None, // TODO: Some(IndirectKey::Late(r.bound_region)),
            RegionKind::ReVar(r) => Some(IndirectKey::Var(r)),
            RegionKind::RePlaceholder(..) | RegionKind::ReError(..) | RegionKind::ReErased => {
                unreachable!("{region:?}")
            }
            RegionKind::ReStatic => None,
        }
    }
}

pub struct IndirectPredicatesEnc;

type ExprInput<'vir> = vir::ExprSnap<'vir>;
type ExprOutput<'vir> = vir::ExprGenBool<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone)]
pub struct IndirectPredicatesEncOutputRef<'vir> {
    pub predicate_applications: Vec<ExprOutput<'vir>>,
}

impl<'vir> IndirectPredicatesEncOutputRef<'vir> {
    pub fn new(predicate_applications: Vec<ExprOutput<'vir>>) -> Self {
        Self {
            predicate_applications,
        }
    }
}

impl<'vir> task_encoder::OutputRefAny for IndirectPredicatesEncOutputRef<'vir> {}

impl TaskEncoder for IndirectPredicatesEnc {
    task_encoder::encoder_cache!(IndirectPredicatesEnc);

    type TaskDescription<'vir> = LifetimeProjection<'vir, ty::Ty<'vir>>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputRef<'vir> = IndirectPredicatesEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let ty = task_key.base();
            let self_ty_enc = deps.require_local::<TyPureEnc>(ty)?;
            let mut covariant = Vec::<ExprOutput<'vir>>::new();
            let mut contravariant = Vec::<ExprOutput<'vir>>::new();
            let predicate_applications = match ty.kind() {
                ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) => {
                    let inner_ty_enc = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                    vec![vcx.mk_lazy_expr(
                        "ref_indirect",
                        vir::TYPE_BOOL,
                        Box::new(move |vcx, self_expr| {
                            inner_ty_enc
                                .ref_to_pred(
                                    vcx,
                                    ref_domain.deref_access(self_expr.downcast_ty()),
                                    None,
                                )
                                .kind
                        }),
                    )];
                }
                // TODO: recurse into other types
                _ => vec![],
            };
            deps.emit_output_ref(
                *task_key,
                IndirectPredicatesEncOutputRef::new(predicate_applications),
            )?;
            Ok(((), ()))
        })
    }
}
