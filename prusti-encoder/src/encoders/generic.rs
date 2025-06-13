use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, DomainIdent, DomainParamData, FunctionIdent, KnownArityAny,
    NullaryArity, PredicateIdent, TypeData, UnaryArity, ViperIdent,
};

use super::rust_ty_predicates::RustTyPredicatesEnc;

pub fn generic_enc_ref<'vir, E: TaskEncoder>(
    deps: &mut TaskEncoderDependencies<'vir, E>,
) -> Result<GenericEncOutputRef<'vir>, EncodeFullError<'vir, E>> {
    vir::with_vcx(|vcx| {
        let ty_param = vcx.tcx().mk_ty_from_kind(TyKind::Param(ty::ParamTy {
            index: 0u32,
            name: symbol::Symbol::intern("T"),
        }));
        deps.require_ref::<RustTyPredicatesEnc>(ty_param)
    })?;
    deps.require_ref::<GenericEnc>(())
}

pub struct GenericEnc;

#[derive(Clone, Debug)]
pub enum GenericEncError {
    // UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncOutputRef<'vir> {
    pub type_snapshot: vir::Type<'vir>,
    pub param_snapshot: vir::Type<'vir>,
    pub param_type_function: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    pub ref_to_pred: PredicateIdent<'vir, BinaryArity<'vir>>,
    pub ref_to_snap: FunctionIdent<'vir, BinaryArity<'vir>>,
    pub unreachable_to_snap: FunctionIdent<'vir, NullaryArity<'vir>>,
    // pub domain_type_name: DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>>,
    pub domain_param_name: DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>>,
    pub const_type_function: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    pub const_value_function: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for GenericEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct GenericEncOutput<'vir> {
    pub type_snapshot: vir::Domain<'vir>,
    pub ref_to_pred: vir::Predicate<'vir>,
    pub param_snapshot: vir::Domain<'vir>,
    pub ref_to_snap: vir::Function<'vir>,
    pub unreachable_to_snap: vir::Function<'vir>,
}

const TYP_DOMAIN: TypeData<'static> = TypeData::Domain("Type", &[]);
const SNAPSHOT_PARAM_DOMAIN: TypeData<'static> = TypeData::Domain("s_Param", &[]);

impl TaskEncoder for GenericEnc {
    task_encoder::encoder_cache!(GenericEnc);

    type TaskDescription<'vir> = (); // ?

    type OutputRef<'vir> = GenericEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericEncOutput<'vir>;

    type EncodingError = GenericEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[allow(non_snake_case)]
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let ref_to_pred = PredicateIdent::new(
            ViperIdent::new("p_Param"),
            BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]),
        );
        // let type_domain_ident = DomainIdent::nullary(ViperIdent::new("Type"));
        let param_domain_ident = DomainIdent::nullary(ViperIdent::new("s_Param"));
        let ref_to_snap = FunctionIdent::new(
            ViperIdent::new("p_Param_snap"),
            BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]),
            &SNAPSHOT_PARAM_DOMAIN,
        );
        let unreachable_to_snap = FunctionIdent::new(
            ViperIdent::new("p_Param_unreachable"),
            NullaryArity::new(&[]),
            &SNAPSHOT_PARAM_DOMAIN,
        );

        let param_type_function = FunctionIdent::new(
            ViperIdent::new("typ"),
            UnaryArity::new(&[&SNAPSHOT_PARAM_DOMAIN]),
            &TYP_DOMAIN,
        );

        let const_type_function = FunctionIdent::new(
            ViperIdent::new("const_typ"),
            UnaryArity::new(&[&SNAPSHOT_PARAM_DOMAIN]),
            &TYP_DOMAIN,
        );
        let const_value_function = FunctionIdent::new(
            ViperIdent::new("const_val"),
            UnaryArity::new(&[&TYP_DOMAIN]),
            &SNAPSHOT_PARAM_DOMAIN,
        );

        let output_ref = GenericEncOutputRef {
            type_snapshot: &TYP_DOMAIN,
            param_snapshot: &SNAPSHOT_PARAM_DOMAIN,
            ref_to_pred,
            // domain_type_name: type_domain_ident,
            domain_param_name: param_domain_ident,
            ref_to_snap,
            unreachable_to_snap,
            param_type_function,
            const_type_function,
            const_value_function,
        };

        #[allow(clippy::unit_arg)]
        deps.emit_output_ref(*task_key, output_ref)?;

        vir::with_vcx(|vcx| {
            let t = vcx.mk_local_ex("t", &TYP_DOMAIN);
            let ref_to_snap = vcx.mk_function(
                "p_Param_snap",
                vir::vir_arg_list! { vcx; self: Ref, t: Type },
                vir::vir_type! { vcx; s_Param },
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr(ref_to_pred.apply(
                    vcx,
                    [vcx.mk_local_ex("self", &TypeData::Ref), t],
                    Some(vcx.mk_wildcard()),
                ))]),
                vcx.alloc_slice(&[vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    param_type_function.apply(vcx, [vcx.mk_result(&SNAPSHOT_PARAM_DOMAIN)]),
                    t,
                )]),
                None,
            );

            // unreachable_to_snap
            let name = unreachable_to_snap.name_str();
            let false_ = vcx.alloc_slice(&[vcx.mk_bool::<false>()]);
            let unreachable_to_snap =
                vcx.mk_function(name, &[], &SNAPSHOT_PARAM_DOMAIN, false_, false_, None);
            Ok((
                GenericEncOutput {
                    param_snapshot: vir::vir_domain! { vcx; domain s_Param {
                            function param_type_function(s_Param): Type;
                            function const_type_function(s_Param): Type;
                            function const_value_function(Type): s_Param;
                            axiom_inverse(const_value_function, const_type_function, s_Param);
                        }
                    },
                    ref_to_pred: vir::vir_predicate! { vcx; predicate p_Param(self_p: Ref, t: Type) },
                    type_snapshot: vir::vir_domain! { vcx; domain Type { } },
                    ref_to_snap,
                    unreachable_to_snap,
                },
                (),
            ))
        })
    }
}
