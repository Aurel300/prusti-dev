use prusti_rustc_interface::abi;
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, PredicateIdn};

use crate::encoders::{
    Impure, TyUsePureEnc,
    ty::{
        LazyRustTy, RustTyDatas,
        generics::{GArgs, GArgsCastEnc, GArgsTyEnc, GParams},
        use_pure::{TyUsePureRaw, UsePureTyDatas},
    },
};

use super::{
    TyUseEnc, UseTyDatas,
    data::*,
    generics::{GArgCaster, GArgsTy},
    impure::{ImpureTyDatas, TyImpureEnc},
};

pub(super) type UseImpureTyDatas = UseTyDatas<Impure>;

type FieldCaster<'vir> = GArgCaster<'vir, Impure>;

impl<'vir> TyDatas<'vir> for UseImpureTyDatas {
    type TyData = TyUseImpureData<'vir>;
    type PrimitiveData = ();
    type ArrayData = TyUseImpureArrayData<'vir>;
    type ImmRefData = TyUseImpureImmRef<'vir>;
    type MutRefData = TyUseImpureMutRef<'vir>;
    type RawData = TyUseImpureRaw<'vir>;
    type FieldData = TyUseImpureField<'vir>;
    type StructData = TyUseImpureStructData<'vir>;
    type VariantData = ();
    type EnumData = TyUseImpureEnumData<'vir>;
}

pub type TyUseImpure<'vir> = Ty<'vir, UseImpureTyDatas>;

pub type TyUseImpureArray<'vir> = ArrayData<'vir, UseImpureTyDatas>;
pub type TyUseImpureStruct<'vir> = StructData<'vir, UseImpureTyDatas>;
pub type TyUseImpureEnum<'vir> = EnumData<'vir, UseImpureTyDatas>;

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureData<'vir> {
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::TyData,
    maybe_inhabited: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureImmRef<'vir> {
    #[allow(dead_code)]
    referent_caster: FieldCaster<'vir>,
    #[allow(dead_code)]
    metadata_caster: GArgCaster<'vir, crate::encoders::Pure>,
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    #[allow(dead_code)]
    impure: <ImpureTyDatas as TyDatas<'vir>>::ImmRefData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureMutRef<'vir> {
    #[allow(dead_code)]
    referent_caster: FieldCaster<'vir>,
    #[allow(dead_code)]
    metadata_caster: GArgCaster<'vir, crate::encoders::Pure>,
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::MutRefData,
    ref_to_snap: vir::FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureRaw<'vir> {
    #[allow(dead_code)]
    metadata_caster: GArgCaster<'vir, crate::encoders::Pure>,
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    #[allow(dead_code)]
    impure: <ImpureTyDatas as TyDatas<'vir>>::RawData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureArrayData<'vir> {
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    #[allow(dead_code)]
    impure: <ImpureTyDatas as TyDatas<'vir>>::ArrayData,
    element_caster: FieldCaster<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyUseImpureStructType<'vir> {
    Box {
        unique_impure: &'vir TyUseImpureStruct<'vir>,
    },
    Unique {
        nonnull_impure: &'vir TyData<'vir, UseImpureTyDatas>,
        nonnull_pure: &'vir TyData<'vir, UsePureTyDatas>,
        rawptr_pure: &'vir TyUsePureRaw<'vir>,
        inner_caster: GArgCaster<'vir, Impure>,
    },
    Generic,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureStructData<'vir> {
    args: GArgsTy<'vir>,
    ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    #[allow(dead_code)]
    impure: <ImpureTyDatas as TyDatas<'vir>>::StructData,
    struct_type: TyUseImpureStructType<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureField<'vir> {
    caster: FieldCaster<'vir>,
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::FieldData,
}

#[derive(Debug, Clone, Copy)]
pub struct TyUseImpureEnumData<'vir> {
    #[allow(dead_code)]
    args: GArgsTy<'vir>,
    impure: <ImpureTyDatas as TyDatas<'vir>>::EnumData,
}

/// Encodes a type into the predicate representation. Takes an arbitrary Rust
/// `Ty` and provides a wrapper around the results of the `TyImpureEnc` encoder.
/// This wrapper handles all the generic casts required (e.g. when fold/unfolding).
pub type TyUseImpureEnc = TyUseEnc<Impure>;

type EncResult<'vir, T> = Result<T, EncodeFullError<'vir, TyUseImpureEnc>>;

impl TaskEncoder for TyUseImpureEnc {
    task_encoder::encoder_cache!(TyUseImpureEnc);
    const ENCODER_NAME: &'static str = "impure type use encoder";

    type TaskDescription<'vir> = super::RustTyDecomposition<'vir>;

    type OutputFullDependency<'vir> = TyUseImpure<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        let ty_impure = deps.require_dep::<TyImpureEnc>(task_key.ty)?;
        let mut walker = TyUseImpureWalker::new(deps, task_key.args)?;
        // Impure encoding needs to know whether the type may be inhabited (to emit
        // the right predicate). It is `None` only from `RustTyDecomposition::identity`.
        let maybe_inhabited = task_key.maybe_inhabited.expect(
            "impure type encoding requires a decomposition with known inhabitedness \
             (from `from_ty`), not one built by `RustTyDecomposition::identity`",
        );
        let ty_use_impure = walker.encode_ty(task_key.ty.zip(ty_impure), maybe_inhabited)?;
        Ok(((), ty_use_impure.alloc()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyImpureEnc::emit_outputs(program)
    }
}

struct TyUseImpureWalker<'a, 'vir> {
    deps: &'a mut TaskEncoderDependencies<'vir, TyUseImpureEnc>,
    args_t: GArgsTy<'vir>,
    args: GArgs<'vir>,
}

impl<'a, 'vir> TyUseImpureWalker<'a, 'vir> {
    fn new(
        deps: &'a mut TaskEncoderDependencies<'vir, TyUseImpureEnc>,
        args: GArgs<'vir>,
    ) -> EncResult<'vir, Self> {
        let args_t = deps.require_dep::<GArgsTyEnc>(args)?;
        Ok(Self { deps, args_t, args })
    }

    fn encode_ty(
        &mut self,
        ty: TyData<'vir, (RustTyDatas, ImpureTyDatas)>,
        maybe_inhabited: bool,
    ) -> EncResult<'vir, TyData<'vir, UseImpureTyDatas>> {
        let specifics = match &ty.specifics {
            TySpecifics::Param(..) => TySpecifics::mk_param(()),
            TySpecifics::Opaque(..) => TySpecifics::mk_opaque(()),
            TySpecifics::Primitive(..) => TySpecifics::mk_primitive(()),
            TySpecifics::ImmRef(data) => {
                let referent_caster = self.encode_normalized(data.0.referent, ty.0.params)?;
                let metadata_caster = self.encode_normalized_pure(data.0.metadata, ty.0.params)?;
                TySpecifics::mk_immref(TyUseImpureImmRef {
                    referent_caster,
                    metadata_caster,
                    args: self.args_t,
                    impure: *data.1,
                })
            }
            TySpecifics::MutRef(data) => {
                let referent_caster = self.encode_normalized(data.0.referent, ty.0.params)?;
                let metadata_caster = self.encode_normalized_pure(data.0.metadata, ty.0.params)?;
                TySpecifics::mk_mutref(TyUseImpureMutRef {
                    referent_caster,
                    metadata_caster,
                    args: self.args_t,
                    impure: *data.1,
                    ref_to_snap: ty.1.ref_to_snap,
                })
            }
            TySpecifics::Raw(data) => {
                let metadata_caster = self.encode_normalized_pure(data.0.metadata, ty.0.params)?;
                TySpecifics::mk_raw(TyUseImpureRaw {
                    metadata_caster,
                    args: self.args_t,
                    impure: *data.1,
                })
            }
            TySpecifics::ArrayLike(data) => {
                TySpecifics::ArrayLike(self.encode_array(data, ty.1.ref_to_pred, ty.0.params)?)
            }
            TySpecifics::StructLike(data) => TySpecifics::StructLike(self.encode_structlike(
                data,
                ty.1.ref_to_pred,
                ty.0.params,
            )?),
            TySpecifics::EnumLike(data) => {
                TySpecifics::EnumLike(self.encode_enumlike(data, ty.0.params)?)
            }
            TySpecifics::Builtin(..) => TySpecifics::mk_builtin(()),
        };
        let data = TyUseImpureData {
            args: self.args_t,
            impure: *ty.1,
            maybe_inhabited,
        };
        Ok(TyData::new(data, specifics))
    }

    fn encode_normalized(
        &mut self,
        inner: LazyRustTy<'vir>,
        params: GParams<'vir>,
    ) -> EncResult<'vir, FieldCaster<'vir>> {
        let normalized = inner.decompose_compare_normalize(params, self.args);
        self.deps.require_dep::<GArgsCastEnc<Impure>>(normalized)
    }

    fn encode_normalized_pure(
        &mut self,
        inner: LazyRustTy<'vir>,
        params: GParams<'vir>,
    ) -> EncResult<'vir, GArgCaster<'vir, crate::encoders::Pure>> {
        let normalized = inner.decompose_compare_normalize(params, self.args);
        self.deps
            .require_dep::<GArgsCastEnc<crate::encoders::Pure>>(normalized)
    }

    fn encode_array(
        &mut self,
        data: &ArrayData<'vir, (RustTyDatas, ImpureTyDatas)>,
        _ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
        params: GParams<'vir>,
    ) -> EncResult<'vir, ArrayData<'vir, UseImpureTyDatas>> {
        let caster = self.encode_normalized(*data.0, params)?;
        let slice = data.slice;
        let data = TyUseImpureArrayData {
            args: self.args_t,
            impure: *data.data.1,
            element_caster: caster,
        };
        Ok(ArrayData::new(data, slice))
    }

    fn encode_structlike(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, ImpureTyDatas)>,
        ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
        params: GParams<'vir>,
    ) -> EncResult<'vir, StructData<'vir, UseImpureTyDatas>> {
        let fields = data
            .fields
            .iter()
            .map(|field| {
                let caster = self.encode_normalized(field.0.ty(), params)?;
                Ok(TyUseImpureField {
                    caster,
                    args: self.args_t,
                    impure: *field.1,
                })
            })
            .collect::<EncResult<'vir, Vec<_>>>()?;
        let struct_type = data.struct_type;
        let impure_struct_type = match struct_type {
            super::StructType::Box => {
                let inner = self.deps.require_dep::<TyUseImpureEnc>(
                    data.fields[0].0.ty().decompose_normalize(self.args),
                )?;
                TyUseImpureStructType::Box {
                    unique_impure: inner.expect_structlike(),
                }
            }
            super::StructType::Unique => {
                let nonnull = data.fields[0].0.ty().decompose_normalize(self.args);
                let nonnull_impure = self.deps.require_dep::<TyUseImpureEnc>(nonnull)?;
                let nonnull_pure = self.deps.require_dep::<TyUsePureEnc>(nonnull)?;
                let raw = nonnull.ty.expect_structlike().fields[0].decompose_normalize(self.args);
                let raw_pure = self.deps.require_dep::<TyUsePureEnc>(raw)?;
                let caster = self.encode_normalized(data.fields[2].0.ty(), params)?;
                TyUseImpureStructType::Unique {
                    nonnull_impure,
                    nonnull_pure,
                    rawptr_pure: raw_pure.expect_raw(),
                    inner_caster: caster,
                }
            }
            _ => TyUseImpureStructType::Generic,
        };
        let data = TyUseImpureStructData {
            args: self.args_t,
            ref_to_pred,
            impure: *data.1,
            struct_type: impure_struct_type,
        };
        Ok(StructData::new(data, fields, struct_type))
    }

    fn encode_enumlike(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, ImpureTyDatas)>,
        params: GParams<'vir>,
    ) -> EncResult<'vir, EnumData<'vir, UseImpureTyDatas>> {
        let variants = data
            .variants
            .iter()
            .map(|variant| {
                let structlike =
                    self.encode_structlike(&variant.inner, variant.1.predicate, params)?;
                Ok(VariantData::new((), structlike))
            })
            .collect::<EncResult<'vir, Vec<_>>>()?;
        let data = TyUseImpureEnumData {
            args: self.args_t,
            impure: *data.1,
        };
        Ok(EnumData::new(data, variants))
    }
}

impl<'vir> TyUseImpureData<'vir> {
    /// Generates a call to `method_assign`, which asserts that the snapshot of
    /// `self_ref` is `self_new_snap`. Appropriate type arguments are used.
    pub fn apply_method_assign<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        self_new_snap: vir::ExprSnap<'vir>,
    ) -> vir::Stmt<'vir> {
        vcx.alloc(vir::StmtData::new(vcx.alloc((self.impure.method_assign)(
            self_ref,
            self.args.get_ty(),
            self.args.get_const(),
            self_new_snap,
        ))))
    }

    /// Constructs the Viper predicate application expression.
    pub fn ref_to_pred<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::ExprBool<'vir> {
        if self.maybe_inhabited {
            vcx.mk_predicate_app_expr(self.ref_to_pred_app(self_ref, perm))
        } else {
            vcx.mk_bool::<false>()
        }
    }

    /// Constructs the Viper predicate application.
    pub fn ref_to_pred_app(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.impure.ref_to_pred)(self_ref, self.args.get_ty(), self.args.get_const())(perm)
    }

    /// Calls the predicate (heap) dependent snapshot construction function.
    pub fn ref_to_snap<Curr, Next>(
        &self,
        self_ref: vir::ExprGenRef<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.impure.ref_to_snap.call()(self_ref, self.args.get_ty(), self.args.get_const())
    }

    pub fn snapshot(&self) -> vir::TypeSnap<'vir> {
        self.impure.ref_to_snap.result()
    }
}

impl<'vir> TyData<'vir, UseImpureTyDatas> {
    /// Fold the predicate (including generic casts).
    pub fn fold(
        &self,
        variant: Option<abi::VariantIdx>,
        self_ref: vir::ExprRef<'vir>,
        index: Option<vir::ExprInt<'vir>>,
        perm: Option<vir::ExprPerm<'vir>>,
        label: Option<vir::OldLabel<'vir>>,
    ) -> Vec<vir::Stmt<'vir>> {
        if let Some(variant) = variant {
            return self
                .expect_variant(variant)
                .inner
                .fold(self_ref, perm)
                .collect();
        };
        match &self.specifics {
            TySpecifics::Param(_) | TySpecifics::Primitive(_) | TySpecifics::Builtin(_) => {
                unreachable!()
            }
            TySpecifics::Opaque(_) => panic!("cannot fold opaque type"),
            TySpecifics::ArrayLike(array) => {
                let index = index.expect("cannot fold array type without index");
                array
                    .element_caster
                    .cast_to_callee_ctx(array.ref_to_index_ref(self_ref, index))
                    .into_iter()
                    .chain([vir::with_vcx(|vcx| {
                        vcx.alloc(vir::StmtData::new(vcx.alloc(
                            (array.data.impure.method_fold)(
                                index,
                                self_ref,
                                self.args.get_ty(),
                                self.args.get_const(),
                            ),
                        )))
                    })])
                    .collect()
            }
            TySpecifics::ImmRef(..) | TySpecifics::Raw(..) => Vec::new(),
            TySpecifics::MutRef(data) => data.fold(self_ref, label).into_iter().collect(),
            TySpecifics::StructLike(data) => data.fold(self_ref, perm).collect(),
            TySpecifics::EnumLike(..) => {
                let pred_app = self.ref_to_pred_app(self_ref, perm);
                vec![vir::with_vcx(|vcx| vcx.mk_fold_stmt(pred_app))]
            }
        }
    }

    /// Unfold the predicate (including generic casts).
    pub fn unfold(
        &self,
        variant: Option<abi::VariantIdx>,
        self_ref: vir::ExprRef<'vir>,
        index: Option<vir::ExprInt<'vir>>,
        perm: Option<vir::ExprPerm<'vir>>,
        old: Option<vir::OldLabel<'vir>>,
    ) -> Vec<vir::Stmt<'vir>> {
        if let Some(variant) = variant {
            return self
                .expect_variant(variant)
                .inner
                .unfold(self_ref, perm)
                .collect();
        };
        match &self.specifics {
            TySpecifics::Param(_) | TySpecifics::Primitive(_) | TySpecifics::Builtin(_) => {
                unreachable!()
            }
            TySpecifics::Opaque(_) => panic!("cannot unfold opaque type"),
            TySpecifics::ArrayLike(array) => {
                let index = index.expect("cannot unfold array type without index");
                [vir::with_vcx(|vcx| {
                    vcx.alloc(vir::StmtData::new(vcx.alloc(
                        (array.data.impure.method_unfold)(
                            index,
                            self_ref,
                            self.args.get_ty(),
                            self.args.get_const(),
                        ),
                    )))
                })]
                .into_iter()
                .chain(
                    array
                        .element_caster
                        .cast_to_caller_ctx(array.ref_to_index_ref(self_ref, index)),
                )
                .collect()
            }
            TySpecifics::ImmRef(..) | TySpecifics::Raw(..) => Vec::new(),
            TySpecifics::MutRef(data) => data.unfold(self_ref, old).into_iter().collect(),
            TySpecifics::StructLike(data) => data.unfold(self_ref, perm).collect(),
            TySpecifics::EnumLike(..) => {
                let pred_app = self.ref_to_pred_app(self_ref, perm);
                vec![vir::with_vcx(|vcx| vcx.mk_unfold_stmt(pred_app))]
            }
        }
    }
}

impl<'vir> TyUseImpureArray<'vir> {
    /// Get the (Ref) address of an index. Identical to the function one would
    /// call in `use_pure`.
    pub fn ref_to_index_ref<Curr, Next>(
        &self,
        self_ref: vir::ExprGenRef<'vir, Curr, Next>,
        index: vir::ExprGenInt<'vir, Curr, Next>,
    ) -> vir::ExprGenRef<'vir, Curr, Next> {
        self.data.impure.ref_to_index_ref.call()(self_ref, index, self.args.get_ty())
    }
}

impl<'vir> TyUseImpureStruct<'vir> {
    fn ref_to_pred_app(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> vir::PredicateApp<'vir> {
        (self.ref_to_pred)(self_ref, self.args.get_ty(), self.args.get_const())(perm)
    }

    /// If this is a struct containing a unique pointer, get the address of the pointee.
    pub fn get_wrapped_addr_from_addr<Curr, Next>(
        &self,
        addr: vir::ExprGenRef<'vir, Curr, Next>,
    ) -> vir::ExprGenRef<'vir, Curr, Next> {
        match self.data.struct_type {
            TyUseImpureStructType::Box { unique_impure } => {
                unique_impure.get_wrapped_addr_from_addr(self.fields[0].field_ref(addr))
            }
            TyUseImpureStructType::Unique {
                nonnull_impure,
                nonnull_pure,
                rawptr_pure,
                ..
            } => rawptr_pure.address_access(
                nonnull_pure.expect_structlike().fields[0]
                    .read(
                        nonnull_impure
                            .ref_to_snap(self.fields[0].field_ref(addr))
                            .downcast_ty(),
                    )
                    .downcast_ty(),
            ),
            TyUseImpureStructType::Generic => {
                unreachable!("Cannot get the wrapped address of a generic struct")
            }
        }
    }

    /// If this is a struct containing a unique pointer, get the metdata of the rawptr.
    pub fn get_wrapped_metadata_from_addr<Curr, Next>(
        &self,
        addr: vir::ExprGenRef<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        match self.data.struct_type {
            TyUseImpureStructType::Box { unique_impure } => {
                unique_impure.get_wrapped_metadata_from_addr(self.fields[0].field_ref(addr))
            }
            TyUseImpureStructType::Unique {
                nonnull_impure,
                nonnull_pure,
                rawptr_pure,
                ..
            } => rawptr_pure.metadata_access(
                nonnull_pure.expect_structlike().fields[0]
                    .read(
                        nonnull_impure
                            .ref_to_snap(self.fields[0].field_ref(addr))
                            .downcast_ty(),
                    )
                    .downcast_ty(),
            ),
            TyUseImpureStructType::Generic => {
                unreachable!("Cannot get the wrapped address of a generic struct")
            }
        }
    }

    /// Fold the predicate (including generic casts).
    fn fold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> + '_ {
        let pred_app = self.ref_to_pred_app(self_ref, perm);
        let fold = vir::with_vcx(|vcx| vcx.mk_fold_stmt(pred_app));
        let mut stmts = vec![];
        if let TyUseImpureStructType::Box { unique_impure } = self.data.struct_type {
            // if the struct is a Box we also need to fold the unique pointer.
            let unique_ptr_ref = self.fields[0].field_ref(self_ref);
            stmts.extend(unique_impure.fold(unique_ptr_ref, perm));
        }
        if let TyUseImpureStructType::Unique {
            nonnull_impure,
            nonnull_pure,
            rawptr_pure,
            inner_caster,
        } = self.data.struct_type
        {
            // folding the unique pointer means accessing its snapshot to retrieve the pointee to perform a cast
            let nonnull_ptr_ref = self.fields[0].field_ref(self_ref);
            let nonnull_snap = nonnull_impure.data.ref_to_snap(nonnull_ptr_ref);
            let rawptr_snap =
                nonnull_pure.expect_structlike().fields[0].read(nonnull_snap.downcast_ty());
            let rawptr_deref = rawptr_pure.address_access(rawptr_snap.downcast_ty());
            let inner_cast = inner_caster.cast_to_callee_ctx(rawptr_deref);
            stmts.push(inner_cast.unwrap());
        } else {
            // we manually create the right type of cast
            stmts.extend(self.cast_to_callee_ctx(self_ref));
        }
        stmts.push(fold);
        stmts.into_iter()
    }

    /// Unfold the predicate (including generic casts).
    fn unfold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        perm: Option<vir::ExprPerm<'vir>>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> + '_ {
        let pred_app = self.ref_to_pred_app(self_ref, perm);
        let unfold = vir::with_vcx(|vcx| vcx.mk_unfold_stmt(pred_app));
        let mut stmts = vec![unfold];
        if let TyUseImpureStructType::Unique {
            nonnull_impure,
            nonnull_pure,
            rawptr_pure,
            inner_caster,
        } = self.data.struct_type
        {
            // unfolding the unique pointer means accessing its snapshot to retrieve the pointee to perform a cast
            let nonnull_ptr_ref = self.fields[0].field_ref(self_ref);
            let nonnull_snap = nonnull_impure.data.ref_to_snap(nonnull_ptr_ref);
            let rawptr_snap =
                nonnull_pure.expect_structlike().fields[0].read(nonnull_snap.downcast_ty());
            let rawptr_deref = rawptr_pure.address_access(rawptr_snap.downcast_ty());
            let inner_cast = inner_caster.cast_to_caller_ctx(rawptr_deref);
            stmts.push(inner_cast.unwrap());
        } else {
            // we manually create the right type of cast
            stmts.extend(self.cast_to_caller_ctx(self_ref));
        }
        if let TyUseImpureStructType::Box { unique_impure } = self.data.struct_type {
            // if the struct is a Box we also need to unfold the unique pointer.
            let unique_ptr_ref = self.fields[0].field_ref(self_ref);
            stmts.extend(unique_impure.unfold(unique_ptr_ref, perm));
        }
        stmts.into_iter()
    }

    fn cast_to_caller_ctx(
        &self,
        self_ref: vir::ExprRef<'vir>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> {
        self.fields
            .iter()
            .filter_map(|f| f.cast_to_caller_ctx(self_ref))
    }

    fn cast_to_callee_ctx(
        &self,
        self_ref: vir::ExprRef<'vir>,
    ) -> impl Iterator<Item = vir::Stmt<'vir>> {
        self.fields
            .iter()
            .filter_map(|f| f.cast_to_callee_ctx(self_ref))
    }
}

impl<'vir> TyUseImpureField<'vir> {
    /// Get the (Ref) address of a field. Identical to the function one would
    /// call in `use_pure`.
    pub fn field_ref<Curr, Next>(
        &self,
        self_ref: vir::ExprGenRef<'vir, Curr, Next>,
    ) -> vir::ExprGenRef<'vir, Curr, Next> {
        self.impure.ref_to_field_ref.call()(self_ref, self.args.get_ty(), self.args.get_const())
    }

    fn cast_to_caller_ctx(&self, self_ref: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        self.caster.cast_to_caller_ctx(self.field_ref(self_ref))
    }

    fn cast_to_callee_ctx(&self, self_ref: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        self.caster.cast_to_callee_ctx(self.field_ref(self_ref))
    }
}

impl<'vir> TyUseImpureEnum<'vir> {
    pub fn discr(&self, self_ref: vir::ExprRef<'vir>) -> vir::ExprRef<'vir> {
        (self.impure.discr)(self_ref)
    }

    pub fn discr_ty(&self) -> TyUseImpure<'vir> {
        self.impure.discr_ty
    }
}

impl<'vir> TyUseImpureImmRef<'vir> {}

impl<'vir> TyUseImpureMutRef<'vir> {
    pub fn deref(
        &self,
        self_ref: vir::ExprRef<'vir>,
        label: Option<vir::OldLabel<'vir>>,
    ) -> vir::ExprRef<'vir> {
        let snap = self.ref_to_snap.call()(self_ref, self.args.get_ty(), self.args.get_const())
            .downcast_ty();
        let deref = self.impure.pure.deref_access.call()(snap);
        vir::with_vcx(|vcx| vcx.maybe_apply_label(deref, label))
    }

    pub fn prim_to_snap_assign(
        &self,
        self_ref: vir::ExprRef<'vir>,
        metadata: vir::ExprSnap<'vir>,
    ) -> vir::ExprCSnap<'vir> {
        let metadata = self.metadata_caster.cast_to_callee_ctx(metadata);
        (self.impure.arbitrary_value)(self_ref, metadata.downcast_ty())
    }

    fn fold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        label: Option<vir::OldLabel<'vir>>,
    ) -> Option<vir::Stmt<'vir>> {
        self.referent_caster
            .cast_to_callee_ctx(self.deref(self_ref, label))
    }

    fn unfold(
        &self,
        self_ref: vir::ExprRef<'vir>,
        label: Option<vir::OldLabel<'vir>>,
    ) -> Option<vir::Stmt<'vir>> {
        self.referent_caster
            .cast_to_caller_ctx(self.deref(self_ref, label))
    }
}
