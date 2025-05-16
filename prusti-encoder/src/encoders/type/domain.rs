// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]

use prusti_rustc_interface::middle::ty::{self, ParamTy, TyKind};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, DomainAxiomData, DomainFunctionData, DomainIdent, DomainParamData,
    FunctionIdent, NullaryArityAny, ToKnownArity, UnaryArity, UnknownArity,
};
use super::{
    lifted::{
        ty::{EncodeGenericsAsParamTy, LiftedTy, LiftedTyEnc},
        ty_constructor::TyConstructorEnc,
    }, most_generic_ty::{extract_type_params, get_vir_base_name_kind, MostGenericTy}, rust_ty_snapshots::RustTySnapshotsEnc
};

pub use super::kinds::adt::DomainDataEnum;
pub use super::kinds::immref::DomainDataImmRef;
pub use super::kinds::mutref::DomainDataMutRef;
pub use super::kinds::primitive::DomainDataPrim;
pub use super::kinds::structlike::DomainDataStruct;

/// You probably never want to use this, use `SnapshotEnc` instead.
/// Note: there should never be a dependency on `PredicateEnc` inside this
/// encoder!
pub struct DomainEnc;

#[derive(Clone, Copy, Debug)]
pub struct FieldFunctions<'vir> {
    /// Snapshot of self as argument. Returns domain of field.
    pub read: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Snapshot of self as first argument and of field as second. Returns
    /// updated domain of self.
    pub write: FunctionIdent<'vir, BinaryArity<'vir>>,
}

#[derive(Clone, Copy, Debug)]
pub enum DiscrBounds<'vir> {
    Range {
        lower: vir::Expr<'vir>,
        upper: vir::Expr<'vir>,
    },
    Explicit(&'vir [vir::Expr<'vir>]),
}

#[derive(Clone, Copy, Debug)]
pub enum DomainEncSpecifics<'vir> {
    Opaque,
    Param,
    Never,
    Primitive(DomainDataPrim<'vir>),
    ImmRef(DomainDataImmRef<'vir>),
    MutRef(DomainDataMutRef<'vir>),
    // structs, tuples
    StructLike(DomainDataStruct<'vir>),
    EnumLike(Option<DomainDataEnum<'vir>>),
}

#[derive(Clone, Debug)]
pub struct DomainEncOutputRef<'vir> {
    pub base_name: String,
    pub domain: vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>,
    pub(super) ty_param_accessors: &'vir [FunctionIdent<'vir, UnaryArity<'vir>>],
    /// Returns the Viper representation of the type of a snapshot-encoded value
    pub typeof_function: FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> DomainEncOutputRef<'vir> {
    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th type parameter of it's type.
    pub fn ty_param_from_snap(
        &self,
        vcx: &'vir vir::VirCtxt,
        idx: usize,
        snap: vir::Expr<'vir>,
    ) -> vir::Expr<'vir> {
        self.ty_param_accessors[idx].apply(vcx, [self.typeof_function.apply(vcx, [snap])])
    }
}

impl<'vir> task_encoder::OutputRefAny for DomainEncOutputRef<'vir> {}

pub fn all_outputs<'vir>() -> Vec<vir::Domain<'vir>> {
    DomainEnc::all_outputs().into_iter().flatten().collect()
}

impl TaskEncoder for DomainEnc {
    task_encoder::encoder_cache!(DomainEnc);

    type TaskDescription<'vir> = MostGenericTy<'vir>;

    type OutputRef<'vir> = DomainEncOutputRef<'vir>;
    type OutputFullDependency<'vir> = DomainEncSpecifics<'vir>;

    /// A domain is not encoded here for Param types, the relevant domains are
    /// encoded in [`GenericEnc`]. The reason we do not encode the domain for
    /// `Param` types here is because we don't want [`GenericEnc`] to depend on
    /// this encoder: doing so would create a cyclic dependency.
    type OutputFullLocal<'vir> = Option<vir::Domain<'vir>>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut builder = DomainBuilder::new(vcx);

            if matches!(task_key.kind(), TyKind::Param(_)) {
                let specifics = super::kinds::param::domain(*task_key, deps, &mut builder)?;
                return Ok((builder.build(), specifics));
            }

            let base_name = get_vir_base_name_kind(task_key.kind(), builder.vcx);
            builder.set_name(&base_name);
            let typeof_ident =
                builder.function("typeof", &[builder.self_type()], builder.type_type());
            let ty_param_accessors = deps
                .require_ref::<TyConstructorEnc>(*task_key)?
                .ty_param_accessors;
            let output_ref =
                builder.output_ref(base_name, typeof_ident.to_known(), ty_param_accessors);
            deps.emit_output_ref(*task_key, output_ref.clone())?;

            let specifics = match task_key.kind() {
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_) => {
                    super::kinds::primitive::domain(*task_key, deps, &mut builder)?
                }
                TyKind::Array(..) => {
                    super::kinds::array::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Closure(..) => {
                    super::kinds::closure::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Adt(..) => {
                    super::kinds::adt::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Tuple(..) => {
                    super::kinds::tuple::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Never => super::kinds::never::domain(*task_key, deps, &mut builder)?,
                TyKind::Ref(_, _, ty::Mutability::Not) => {
                    super::kinds::immref::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Ref(_, _, ty::Mutability::Mut) => {
                    super::kinds::mutref::domain(*task_key, deps, &mut builder)?
                }
                TyKind::Param(_) => super::kinds::param::domain(*task_key, deps, &mut builder)?,
                TyKind::Str => super::kinds::str::domain(*task_key, deps, &mut builder)?,
                _kind => super::kinds::opaque::domain(*task_key, deps, &mut builder)?,
            };
            Ok((builder.build(), specifics))
        })
    }
}

pub(crate) struct DomainBuilder<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: Option<&'vir str>,
    domain_ident: Option<vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>>,
    self_type: Option<vir::Type<'vir>>,
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
}

impl<'vir> DomainBuilder<'vir> {
    pub(crate) fn new(vcx: &'vir vir::VirCtxt<'vir>) -> Self {
        DomainBuilder {
            vcx,
            name: None,
            domain_ident: None,
            self_type: None,
            axioms: Vec::new(),
            functions: Vec::new(),
        }
    }

    pub(crate) fn set_name(&mut self, name: &str) {
        let name = vir::vir_format!(self.vcx, "s_{name}");
        self.name = Some(name);
        self.domain_ident = Some(DomainIdent::nullary(vir::ViperIdent::new(name)));
        self.self_type = Some(self.vcx.alloc(vir::TypeData::Domain(
            self.name.expect("name should be set"),
            &[],
        )));
    }

    pub(crate) fn function(
        &mut self,
        name: &str,
        args: &[&'vir vir::TypeData],
        ret: &'vir vir::TypeData,
    ) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        let name = vir::vir_format!(
            self.vcx,
            "{}_{name}",
            self.name.expect("name should be set")
        );
        let args = self.vcx.alloc_slice(args);
        let ident = FunctionIdent::new(vir::ViperIdent::new(name), UnknownArity::new(args), ret);
        self.functions.push(self.vcx.alloc(DomainFunctionData {
            unique: false,
            name: ident.name(),
            args,
            ret,
        }));
        ident
    }

    pub(crate) fn axiom(&mut self, name: &str, expr: vir::Expr<'vir>) {
        let name = vir::vir_format!(
            self.vcx,
            "{}_ax_{name}",
            self.name.expect("name should be set")
        );
        self.axioms
            .push(self.vcx.alloc(DomainAxiomData { name, expr }));
    }

    pub(crate) fn self_type(&self) -> vir::Type<'vir> {
        self.self_type.expect("name should be set")
    }

    pub(crate) fn type_type(&self) -> vir::Type<'vir> {
        &vir::TypeData::Domain("Type", &[]) // TODO: refer to something else
    }

    pub(crate) fn output_ref(
        &self,
        base_name: String,
        typeof_function: FunctionIdent<'vir, UnaryArity<'vir>>,
        ty_param_accessors: &[FunctionIdent<'vir, UnaryArity<'vir>>],
    ) -> DomainEncOutputRef<'vir> {
        DomainEncOutputRef {
            base_name,
            domain: self.domain_ident.expect("name should be set"),
            typeof_function,
            ty_param_accessors: self.vcx.alloc_slice(ty_param_accessors),
        }
    }

    pub(crate) fn build(self) -> Option<vir::Domain<'vir>> {
        Some(self.vcx.mk_domain(
            self.domain_ident?.name(),
            &[],
            self.vcx.alloc_slice(&self.axioms),
            self.vcx.alloc_slice(&self.functions),
        ))
    }
}

/// Data for encoding field access functions and axioms
#[derive(Clone)]
pub(super) struct FieldTy<'vir> {
    pub(super) rust_ty: ty::Ty<'vir>,

    /// The type of encoded field
    pub(super) ty: vir::Type<'vir>,
}

impl<'vir> FieldTy<'vir> {
    pub(super) fn mk_field_tys<T: TaskEncoder>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        variant: &ty::VariantDef,
        params: ty::GenericArgsRef<'vir>,
    ) -> Result<Vec<Self>, EncodeFullError<'vir, T>> {
        variant
            .fields
            .iter()
            .map(|f| f.ty(vcx.tcx(), params))
            .map(|ty| Self::from_ty(vcx, deps, ty))
            .collect::<Result<Vec<_>, _>>()
    }

    pub(super) fn from_ty<T: TaskEncoder>(
        _vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        ty: ty::Ty<'vir>,
    ) -> Result<FieldTy<'vir>, EncodeFullError<'vir, T>> {
        let vir_ty = deps
            .require_ref::<RustTySnapshotsEnc>(ty)?
            .generic_snapshot
            .snapshot;
        Ok(FieldTy {
            rust_ty: ty,
            ty: vir_ty,
        })
    }
}
