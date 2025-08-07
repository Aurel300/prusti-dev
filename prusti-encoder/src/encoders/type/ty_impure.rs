use prusti_rustc_interface::{
    middle::ty,
    abi,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{lifted::{casters::{CastTypeImpure, CastTypePure}, rust_ty_cast::{GenericCasterImpure, GenericCasterPure, RustTyCastersEnc}}, predicate::{PredicateEnc, PredicateEncDataEnum, PredicateEncDataImmRef, PredicateEncDataMutRef, PredicateEncDataStruct}, PredicateEncOutput, PredicateEncOutputRef};

use super::{
    lifted::{
        generic::LiftedGeneric,
        ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
    },
    most_generic_ty::extract_type_params,
};

pub struct TyImpureEnc;

#[derive(Clone)]
pub struct TyImpureEncOutputRef<'vir> {
    /// The predicate output for the "most generic version" of the input type
    generic_predicate: PredicateEncOutputRef<'vir>,

    pub indirect_predicate: Option<(
        vir::ExprGenBool<'vir, vir::ExprRef<'vir>, vir::ExprKind<'vir>>,
        vir::ExprGenBool<'vir, vir::ExprRef<'vir>, vir::ExprKind<'vir>>,
    )>,

    /// The lifted representation of the input type, as a Viper value
    pub ty: LiftedTy<'vir, LiftedGeneric<'vir>>,

    pub f_ty: GenericCasterPure<'vir>,
    pub params: Vec<GenericCasterImpure<'vir>>,
}

pub struct TyImpureDataStruct<'vir> {
    inner: PredicateEncDataStruct<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

pub struct TyImpureDataEnum<'vir> {
    inner: PredicateEncDataEnum<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

pub struct TyImpureDataImmRef<'vir> {
    inner: PredicateEncDataImmRef<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

pub struct TyImpureDataMutRef<'vir> {
    inner: PredicateEncDataMutRef<'vir>,
    ty_args: Vec<vir::ExprTyVal<'vir>>,
}

impl<'vir> TyImpureEncOutputRef<'vir> {
    /// Generates a call to `method_assign`, which asserts that the snapshot of
    /// `self_ref` is `self_new_snap`. Appropriate type arguments are used.
    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        self_new_snap: vir::ExprSnap<'vir>,
    ) -> vir::Stmt<'vir> {
        //assert_eq!(self_ref.ty(), &TypeData::Ref);
        assert_eq!(
            self.snapshot(),
            self_new_snap.ty(),
            "rhs of assignment does not have expected type"
        );
        vcx.alloc(vir::StmtData::new(vcx.alloc(
            (self.generic_predicate.method_assign)(
                self_ref,
                &self.ty.arg_exprs(vcx),
                self_new_snap,
            ),
        )))
    }

    pub fn snapshot(&self) -> vir::TypeSnap<'vir> {
        self.generic_predicate.snapshot
    }

    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::ExprBool<'vir> {
        vcx.mk_predicate_app_expr(self.ref_to_pred_app(vcx, self_ref, perm))
    }

    pub fn ref_to_pred_app<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.generic_predicate.ref_to_pred)(self_ref, &self.ref_to_ty_args(vcx))(perm)
    }

    pub fn ref_to_snap<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
    ) -> vir::ExprSnap<'vir> {
        let expr = (self.generic_predicate.ref_to_snap)(self_ref, &self.ref_to_ty_args(vcx));
        assert!(expr.ty() == self.snapshot());
        expr
    }

    pub fn ref_to_indirect_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        _perm: Option<vir::ExprPerm<'vir>>,
        // TODO: make this a function of a lifetime being projected?
        // lifetime: ty::Region<'tcx>,
    ) -> Option<(vir::ExprBool<'vir>, vir::ExprBool<'vir>)> {
        use vir::Reify;
        self.indirect_predicate
            .map(|(pre, post)| (pre.reify(vcx, self_ref), post.reify(vcx, self_ref)))
        //.map(|pred| vcx.mk_predicate_app_expr(pred.apply(vcx, self.ref_to_ty_args(vcx, self_ref), perm)))
    }

    fn ref_to_pred_app_variant_opt(
        &self,
        vid: Option<abi::VariantIdx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        let ty_params = vir::with_vcx(|vcx| self.ref_to_ty_args(vcx));
        self.generic_predicate.expect_pred_variant_opt(vid)(self_ref, &ty_params)(perm)
    }

    fn get_variant_opt(&self, vid: Option<abi::VariantIdx>) -> Option<TyImpureDataStruct<'vir>> {
        let inner = *self.generic_predicate.get_variant_opt(vid)?;
        let ty_args = self.ref_to_ty_args(vir::with_vcx(|vcx| vcx));
        Some(TyImpureDataStruct { inner, ty_args })
    }

    pub fn expect_variant_opt(&self, vid: Option<abi::VariantIdx>) -> TyImpureDataStruct<'vir> {
        self.get_variant_opt(vid).unwrap()
    }

    pub fn get_enumlike(&self) -> Option<Option<TyImpureDataEnum<'vir>>> {
        self.generic_predicate
            .get_enumlike()
            .map(|&inner| inner.map(|inner| TyImpureDataEnum {
                inner,
                ty_args: self.ref_to_ty_args(vir::with_vcx(|vcx| vcx)),
            }))
    }

    pub fn expect_immref(&self) -> TyImpureDataImmRef<'vir> {
        let inner = self.generic_predicate.expect_immref();
        let ty_args = self.ref_to_ty_args(vir::with_vcx(|vcx| vcx));
        TyImpureDataImmRef { inner, ty_args }
    }

    pub fn expect_mutref(&self) -> TyImpureDataMutRef<'vir> {
        let inner = self.generic_predicate.expect_mutref();
        let ty_args = self.ref_to_ty_args(vir::with_vcx(|vcx| vcx));
        TyImpureDataMutRef { inner, ty_args }
    }

    pub fn fold(&self, self_ref: vir::ExprRef<'vir>, perm: Option<vir::ExprPerm<'vir>>, vid: Option<abi::VariantIdx>) -> Vec<vir::Stmt<'vir>> {
        self.get_variant_opt(vid).into_iter().flat_map(|data| data.inner.snap_data.field_access.iter().filter_map(|field| {
            field.generic_idx.map(|generic_idx| self.params[generic_idx as usize])
        }));
        let fold = vir::with_vcx(|vcx| vcx.mk_fold_stmt(self.ref_to_pred_app(vcx, self_ref, perm)));
        todo!()
    }

    /// Arguments to `ref_to_pred` and `ref_to_snap`.
    fn ref_to_ty_args<'tcx>(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::ExprTyVal<'vir>> {
        self.generic_predicate.ref_to_ty_args(vcx, self.ty)
    }
}

impl<'vir> TyImpureDataStruct<'vir> {
    pub fn field<Curr, Next>(&self, field: abi::FieldIdx, self_ref: vir::ExprGenRef<'vir, Curr, Next>) -> vir::ExprGenRef<'vir, Curr, Next> {
        let ty_args = (&*self.ty_args) as *const [vir::ExprTyVal<'vir>] as *const [vir::ExprGenTyVal<'vir, Curr, Next>];
        // TODO: remove unsafe
        let ty_args = unsafe { &*ty_args };
        self.inner.ref_to_field_refs[field.index()].call()(self_ref, ty_args)
    }
}

impl<'vir> TyImpureDataEnum<'vir> {
    pub fn discr(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.inner.discr)(self_ref)
    }
}

impl<'vir> TyImpureDataImmRef<'vir> {
    pub fn deref(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.inner.deref_func)(self_ref, &self.ty_args)
    }
}

impl<'vir> TyImpureDataMutRef<'vir> {
    pub fn deref(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.inner.deref_func)(self_ref)
    }
}

impl<'vir> task_encoder::OutputRefAny for TyImpureEncOutputRef<'vir> {}

impl TaskEncoder for TyImpureEnc {
    task_encoder::encoder_cache!(TyImpureEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = TyImpureEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ();

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let generic_predicate = deps.require_ref::<PredicateEnc>(generic_ty)?;
            /*
            let indirect_predicate = if let ty::TyKind::Ref(_, inner_ty, _) = task_key.kind() {
                let inner_ty_enc = deps.require_ref::<TyImpureEnc>(*inner_ty).unwrap();
                let deref_access = generic_predicate.expect_ref().deref_func;
                let inner_ty_enc_c = inner_ty_enc.clone();
                Some((
                    vcx.mk_lazy_expr("ref_indirect", Box::new(move |vcx, self_expr| inner_ty_enc.ref_to_pred(
                        vcx,
                        deref_access.apply(vcx, [self_expr]),
                        None,
                    ).kind)),
                    vcx.mk_lazy_expr("ref_indirect_post", Box::new(move |vcx, self_expr| inner_ty_enc_c.ref_to_pred(
                        vcx,
                        vcx.mk_old_expr(deref_access.apply(vcx, [self_expr])),
                        None,
                    ).kind)),
                ))
            } else {
                None
            };
            */
            let ty = deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*task_key)?;
            let f_ty = deps.require_local::<RustTyCastersEnc<CastTypePure>>(*task_key)?;
            let mut params = Vec::new();
            for arg in args {
                params.push(deps.require_local::<RustTyCastersEnc<CastTypeImpure>>(arg)?);
            }
            deps.emit_output_ref(
                *task_key,
                TyImpureEncOutputRef {
                    generic_predicate,
                    indirect_predicate: None,
                    ty,
                    f_ty,
                    params,
                },
            )?;
            Ok(((), ()))
        })
    }

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }
}
