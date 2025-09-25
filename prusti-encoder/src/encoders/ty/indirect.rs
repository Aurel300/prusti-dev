use pcg::borrow_pcg::region_projection::LifetimeProjection;
use prusti_rustc_interface::middle::ty::{self};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Reify};

use crate::encoders::ty::{RustTyDecomposition, pure::TyPureEnc};

use super::{data::TySpecifics, use_impure::TyUseImpureEnc, use_pure::TyUsePureEnc};

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

    type TaskDescription<'vir> = LifetimeProjection<'vir, RustTyDecomposition<'vir>>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    type OutputFullDependency<'vir> = IndirectPredicatesEncOutputRef<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let ty = task_key.base();
            let self_ty_enc = deps.require_dep::<TyUsePureEnc>(ty)?;
            let combined = ty.ty.zip(self_ty_enc);
            let mut predicate_applications = vec![];
            match combined.specifics {
                TySpecifics::MutRef((data, ref_domain)) => {
                    let inner_ty = data.decompose_normalize(ty.args);
                    let inner_ty_enc = deps.require_dep::<TyUseImpureEnc>(inner_ty)?;
                    predicate_applications.push(vcx.mk_lazy_expr(
                        "ref_indirect",
                        vir::TYPE_BOOL,
                        Box::new(move |vcx, self_expr: vir::ExprSnap<'vir>| {
                            inner_ty_enc
                                .ref_to_pred(
                                    vcx,
                                    ref_domain.deref_access(self_expr.downcast_ty()),
                                    None,
                                )
                                .kind
                        }),
                    ));
                    if let Some(new_projection) =
                        LifetimeProjection::new(inner_ty, task_key.region(()), None, ())
                    {
                        let inner_indirect =
                            deps.require_dep::<IndirectPredicatesEnc>(new_projection)?;
                        predicate_applications.extend(
                            inner_indirect
                                .predicate_applications
                                .into_iter()
                                .map(|inner_expr| {
                                    vcx.mk_lazy_expr(
                                        "ref_inner_indirect",
                                        vir::TYPE_BOOL,
                                        Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                            inner_expr
                                                .reify(
                                                    vcx,
                                                    ref_domain
                                                        .value_access(self_expr.downcast_ty()),
                                                )
                                                .kind
                                        }),
                                    )
                                }),
                        );
                    }
                }
                TySpecifics::StructLike(data) => {
                    for (field_ty, accessor) in data.fields {
                        let project = |inner_expr: ExprOutput<'vir>| {
                            vcx.mk_lazy_expr(
                                "ref_inner_indirect",
                                vir::TYPE_BOOL,
                                Box::new(move |vcx, self_expr: vir::ExprGenSnap<_, _>| {
                                    inner_expr
                                        .reify(vcx, accessor.read(self_expr.downcast_ty()))
                                        .kind
                                }),
                            )
                        };

                        // TODO: invalid recursion here if the defined struct is
                        // recursive!
                        let field_ty = field_ty.decompose(ty.ty.params);
                        let new_projection =
                            LifetimeProjection::new(field_ty, task_key.region(()), None, ())
                                .unwrap();
                        let field_indirect =
                            deps.require_dep::<IndirectPredicatesEnc>(new_projection)?;
                        predicate_applications.extend(
                            field_indirect
                                .predicate_applications
                                .into_iter()
                                .map(project),
                        );
                    }
                }
                // TODO: recurse into other types
                _ => {}
            };
            Ok((
                (),
                IndirectPredicatesEncOutputRef::new(predicate_applications),
            ))
        })
    }
}
