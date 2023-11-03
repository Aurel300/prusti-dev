use prusti_rustc_interface::middle::ty;
use rustc_middle::ty::VariantDef;
use rustc_type_ir::sty::TyKind;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionGenData, TypeData};

pub struct TypeEncoder;

#[derive(Clone, Debug)]
pub enum TypeEncoderError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRefSubStruct<'vir> {
    pub field_read: &'vir [&'vir str],
    pub field_write: &'vir [&'vir str],
    pub field_projection_p: &'vir [&'vir str],
}

#[derive(Clone, Debug)]
pub enum TypeEncoderOutputRefSub<'vir> {
    Primitive,
    // structs, tuples
    StructLike(TypeEncoderOutputRefSubStruct<'vir>),
    Enum,
}

// TODO: should output refs actually be references to structs...?
#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRef<'vir> {
    pub snapshot_name: &'vir str,
    pub predicate_name: &'vir str,
    pub from_primitive: Option<&'vir str>,
    pub to_primitive: Option<&'vir str>,
    pub snapshot: vir::Type<'vir>,
    pub function_unreachable: &'vir str,
    pub function_snap: &'vir str,
    //pub method_refold: &'vir str,
    pub specifics: TypeEncoderOutputRefSub<'vir>,
    pub method_assign: &'vir str,
}
impl<'vir> task_encoder::OutputRefAny<'vir> for TypeEncoderOutputRef<'vir> {}

impl<'vir> TypeEncoderOutputRef<'vir> {
    #[track_caller]
    pub fn expect_structlike(&self) -> &TypeEncoderOutputRefSubStruct<'vir> {
        match self.specifics {
            TypeEncoderOutputRefSub::StructLike(ref data) => data,
            _ => panic!("expected structlike type"),
        }
    }

    pub fn expr_from_u128(&self, val: u128) -> vir::Expr<'vir> {
        // TODO: not great: store the TyKind as well?
        //   or should this be a different task for TypeEncoder?
        match self.snapshot_name {
            "s_Bool" => vir::with_vcx(|vcx| {
                vcx.mk_func_app(
                    self.from_primitive.unwrap(),
                    &[vcx.alloc(vir::ExprData::Const(
                        vcx.alloc(vir::ConstData::Bool(val != 0)),
                    ))],
                )
            }),
            name if name.starts_with("s_Int_") || name.starts_with("s_Uint_") => {
                vir::with_vcx(|vcx| {
                    vcx.mk_func_app(
                        self.from_primitive.unwrap(),
                        &[vcx.alloc(vir::ExprData::Const(vcx.alloc(vir::ConstData::Int(val))))],
                    )
                })
            }
            k => todo!("unsupported type in expr_from_u128 {k:?}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutput<'vir> {
    pub fields: &'vir [vir::Field<'vir>],
    pub snapshot: vir::Domain<'vir>,
    pub predicate: vir::Predicate<'vir>,
    // TODO: these should be generated on demand, put into tiny encoders ?
    pub function_unreachable: vir::Function<'vir>,
    pub function_snap: vir::Function<'vir>,
    pub field_projection_p: &'vir [vir::Function<'vir>],
    //pub method_refold: vir::Method<'vir>,
    pub method_assign: vir::Method<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<TypeEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for TypeEncoder {
    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = TypeEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = TypeEncoderOutput<'vir>;
    //type OutputFullDependency<'vir> = TypeEncoderOutputDep<'vir>;

    type EncodingError = TypeEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'vir, TypeEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        // Here we need to normalise the task description.
        // In particular, any concrete type parameter instantiation is replaced
        // with the identity substitutions for the item.
        // For example:
        //     Assuming `struct Foo<T, U> { .. }`,
        //     `Foo<i32, bool>` is normalised to `Foo<T, U>`
        match task.kind() {
            /*TyKind::Param(_) => vir::with_vcx(|vcx| vcx.tcx.mk_ty_param(
                0,
                vcx.tcx.mk_symbol("T"),
            )),*/
            TyKind::Adt(adt_def, _) if adt_def.is_struct() => vir::with_vcx(|vcx| {
                let substs = ty::List::identity_for_item(vcx.tcx, adt_def.did());
                vcx.tcx.mk_ty_from_kind(ty::TyKind::Adt(*adt_def, substs))
            }),
            _ => *task,
        }
    }

    /*
    fn task_to_output_ref<'vir>(task: &Self::TaskDescription<'vir>) -> Self::OutputRef<'vir> {
        let (snapshot, predicate) = match task.kind() {
            TyKind::Bool => ("s_Bool", "p_Bool"),
            _ => panic!(),
        };
        vir::with_vcx(|vcx| TypeEncoderOutputDep {
            snapshot: vcx.alloc_str(snapshot),
            predicate: vcx.alloc_str(predicate),
        })
    }
    */

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
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
        // TODO: remove. This is here to get rust-analyzer to know the type.
        let task_key: &ty::Ty = task_key;

        vir::with_vcx(|vcx| match task_key.kind() {
            TyKind::Bool => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Bool"));
                deps.emit_output_ref::<Self>(
                    *task_key,
                    TypeEncoderOutputRef {
                        snapshot_name: "s_Bool",
                        predicate_name: "p_Bool",
                        to_primitive: Some("s_Bool_val"),
                        from_primitive: Some("s_Bool_cons"),
                        snapshot: ty_s,
                        function_unreachable: "s_Bool_unreachable",
                        function_snap: "p_Bool_snap",
                        //method_refold: "refold_p_Bool",
                        specifics: TypeEncoderOutputRefSub::Primitive,
                        method_assign: "assign_p_Bool",
                    },
                );
                Ok((
                    TypeEncoderOutput {
                        fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                            name: "f_Bool",
                            ty: ty_s,
                        })]),
                        snapshot: vir::vir_domain! { vcx; domain s_Bool {
                            function s_Bool_cons(Bool): s_Bool;
                            function s_Bool_val(s_Bool): Bool;
                            axiom_inverse(s_Bool_val, s_Bool_cons, Bool);
                            axiom_inverse(s_Bool_cons, s_Bool_val, s_Bool);
                        } },
                        predicate: mk_simple_predicate(vcx, "p_Bool", "f_Bool"),
                        function_unreachable: mk_unreachable(vcx, "s_Bool", ty_s),
                        function_snap: mk_snap(vcx, "p_Bool", "s_Bool", Some("f_Bool"), ty_s),
                        //method_refold: mk_refold(vcx, "p_Bool", ty_s),
                        field_projection_p: &[],
                        method_assign: mk_assign(vcx, "p_Bool", ty_s),
                    },
                    (),
                ))
            }
            TyKind::Int(_) | TyKind::Uint(_) => {
                let (sign, name_str) = match task_key.kind() {
                    TyKind::Int(kind) => ("Int", kind.name_str()),
                    TyKind::Uint(kind) => ("Uint", kind.name_str()),
                    _ => unreachable!(),
                };
                let name_s = vir::vir_format!(vcx, "s_{sign}_{name_str}");
                let name_p = vir::vir_format!(vcx, "p_{sign}_{name_str}");
                let name_cons = vir::vir_format!(vcx, "{name_s}_cons");
                let name_val = vir::vir_format!(vcx, "{name_s}_val");
                let name_field = vir::vir_format!(vcx, "f_{name_s}");
                let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));
                deps.emit_output_ref::<Self>(
                    *task_key,
                    TypeEncoderOutputRef {
                        snapshot_name: name_s,
                        predicate_name: name_p,
                        to_primitive: Some(name_val),
                        from_primitive: Some(name_cons),
                        snapshot: ty_s,
                        function_unreachable: vir::vir_format!(vcx, "{name_s}_unreachable"),
                        function_snap: vir::vir_format!(vcx, "{name_p}_snap"),
                        //method_refold: vir::vir_format!(vcx, "refold_{name_p}"),
                        specifics: TypeEncoderOutputRefSub::Primitive,
                        method_assign: vir::vir_format!(vcx, "assign_{name_p}"),
                    },
                );
                Ok((
                    TypeEncoderOutput {
                        fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                            name: name_field,
                            ty: ty_s,
                        })]),
                        snapshot: vir::vir_domain! { vcx; domain [name_s] {
                            function [name_cons](Int): [ty_s];
                            function [name_val]([ty_s]): Int;
                            axiom_inverse([name_val], [name_cons], Int);
                            axiom_inverse([name_cons], [name_val], [ty_s]);
                        } },
                        predicate: mk_simple_predicate(vcx, name_p, name_field),
                        function_unreachable: mk_unreachable(vcx, name_s, ty_s),
                        function_snap: mk_snap(vcx, name_p, name_s, Some(name_field), ty_s),
                        //method_refold: mk_refold(vcx, name_p, ty_s),
                        field_projection_p: &[],
                        method_assign: mk_assign(vcx, name_p, ty_s),
                    },
                    (),
                ))
            }

            TyKind::Tuple(tys) if tys.len() == 0 => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Tuple0"));
                deps.emit_output_ref::<Self>(
                    *task_key,
                    TypeEncoderOutputRef {
                        snapshot_name: "s_Tuple0",
                        predicate_name: "p_Tuple0",
                        to_primitive: None,
                        from_primitive: None,
                        snapshot: ty_s,
                        function_unreachable: "s_Tuple0_unreachable",
                        function_snap: "p_Tuple0_snap",
                        //method_refold: "refold_p_Tuple0",
                        specifics: TypeEncoderOutputRefSub::Primitive,
                        method_assign: vir::vir_format!(vcx, "assign_p_Tuple0"),
                    },
                );
                Ok((
                    TypeEncoderOutput {
                        fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                            name: vir::vir_format!(vcx, "f_Tuple0"),
                            ty: ty_s,
                        })]),
                        snapshot: vir::vir_domain! { vcx; domain s_Tuple0 {
                            function s_Tuple0_cons(): [ty_s];
                        } },
                        predicate: vir::vir_predicate! { vcx; predicate p_Tuple0(self_p: Ref) },
                        function_unreachable: mk_unreachable(vcx, "s_Tuple0", ty_s),
                        function_snap: mk_snap(vcx, "p_Tuple0", "s_Tuple0", None, ty_s),
                        //method_refold: mk_refold(vcx, "p_Tuple0", ty_s),
                        field_projection_p: &[],
                        method_assign: mk_assign(vcx, "p_Tuple0", ty_s),
                    },
                    (),
                ))
            }

            TyKind::Tuple(tys) => {
                let field_ty_out = tys
                    .iter()
                    .map(|ty| {
                        deps.require_ref::<crate::encoders::TypeEncoder>(ty)
                            .unwrap()
                    })
                    .collect::<Vec<_>>();

                // TODO: Properly name the tuple according to its types, or make generic?

                // Temporary fix to make it possisble to have multiple tuples of the same size with different element types
                let tmp_ty_name = field_ty_out
                    .iter()
                    .map(|e| e.snapshot_name)
                    .collect::<Vec<&str>>()
                    .join("_");

                Ok((
                    mk_structlike(
                        vcx,
                        deps,
                        task_key,
                        vir::vir_format!(vcx, "s_Tuple{}_{}", tys.len(), tmp_ty_name),
                        vir::vir_format!(vcx, "p_Tuple{}_{}", tys.len(), tmp_ty_name),
                        field_ty_out,
                    )?,
                    (),
                ))
            }

            TyKind::Param(_param) => {
                let param_out = deps
                    .require_ref::<crate::encoders::GenericEncoder>(())
                    .unwrap();
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Param"));
                deps.emit_output_ref::<Self>(
                    *task_key,
                    TypeEncoderOutputRef {
                        snapshot_name: param_out.snapshot_param_name,
                        predicate_name: param_out.predicate_param_name,
                        to_primitive: None,
                        from_primitive: None,
                        snapshot: ty_s,
                        function_unreachable: "s_Param_unreachable",
                        function_snap: "p_Param_snap",
                        //method_refold: "refold_p_Param",
                        specifics: TypeEncoderOutputRefSub::Primitive,
                        method_assign: vir::vir_format!(vcx, "assign_p_Bool"),
                    },
                );
                Ok((
                    TypeEncoderOutput {
                        fields: &[],
                        snapshot: vir::vir_domain! { vcx; domain s_ParamTodo { // TODO: should not be emitted -- make outputs vectors
                        } },
                        predicate: vir::vir_predicate! { vcx; predicate p_ParamTodo(self_p: Ref) },
                        function_unreachable: mk_unreachable(vcx, "p_Param", ty_s),
                        function_snap: mk_snap(vcx, "p_Param", "s_Param", None, ty_s),
                        //method_refold: mk_refold(vcx, "p_Param", ty_s),
                        field_projection_p: &[],
                        method_assign: mk_assign(vcx, "p_Param", ty_s),
                    },
                    (),
                ))
            }
            TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                tracing::debug!("encoding ADT {adt_def:?} with substs {substs:?}");
                let substs = ty::List::identity_for_item(vcx.tcx, adt_def.did());
                let field_ty_out = adt_def
                    .all_fields()
                    .map(|field| {
                        deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs))
                            .unwrap()
                    })
                    .collect::<Vec<_>>();
                let did_name = vcx.tcx.item_name(adt_def.did()).to_ident_string();

                Ok((
                    mk_structlike(
                        vcx,
                        deps,
                        task_key,
                        vir::vir_format!(vcx, "s_Adt_{did_name}"),
                        vir::vir_format!(vcx, "p_Adt_{did_name}"),
                        field_ty_out,
                    )?,
                    (),
                ))
            }

            TyKind::Never => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Never"));
                deps.emit_output_ref::<Self>(
                    *task_key,
                    TypeEncoderOutputRef {
                        snapshot_name: "s_Never",
                        predicate_name: "p_Never",
                        to_primitive: None,
                        from_primitive: None,
                        snapshot: ty_s,
                        function_unreachable: "s_Never_unreachable",
                        function_snap: "p_Never_snap",
                        //method_refold: "refold_p_Never",
                        specifics: TypeEncoderOutputRefSub::Primitive,
                        method_assign: vir::vir_format!(vcx, "assign_p_Never"),
                    },
                );
                Ok((
                    TypeEncoderOutput {
                        fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                            name: vir::vir_format!(vcx, "f_Never"),
                            ty: ty_s,
                        })]),
                        snapshot: vir::vir_domain! { vcx; domain s_Never {} },
                        predicate: vir::vir_predicate! { vcx; predicate p_Never(self_p: Ref) },
                        function_unreachable: mk_unreachable(vcx, "s_Never", ty_s),
                        function_snap: mk_snap(vcx, "p_Never", "s_Never", None, ty_s),
                        //method_refold: mk_refold(vcx, "p_Never", ty_s),
                        field_projection_p: &[],
                        method_assign: mk_assign(vcx, "p_Never", ty_s),
                    },
                    (),
                ))
            }

            TyKind::Adt(adt_def, substs) if adt_def.is_enum() => {
                tracing::error!("encoding enum {adt_def:#?} with substs {substs:?}");
                tracing::warn!("{:?}", adt_def.all_fields().collect::<Vec<_>>());
                tracing::warn!("{:#?}", adt_def.variants());

                Ok((mk_enum(vcx, deps, adt_def, task_key)?, ()))
            }

            //_ => Err((TypeEncoderError::UnsupportedType, None)),
            unsupported_type => todo!("type not supported: {unsupported_type:?}"),
        })
    }
}

fn mk_enum<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir>,
    adt: &ty::AdtDef,
    task_key: &<TypeEncoder as TaskEncoder>::TaskKey<'vir>,
) -> Result<
    <TypeEncoder as TaskEncoder>::OutputFullLocal<'vir>,
    (
        <TypeEncoder as TaskEncoder>::EncodingError,
        Option<<TypeEncoder as TaskEncoder>::OutputFullDependency<'vir>>,
    ),
> {
    let did_name = vcx.tcx.item_name(adt.did()).to_ident_string();

    let name_s = vir::vir_format!(vcx, "s_Adt_{did_name}");
    let name_p = vir::vir_format!(vcx, "p_Adt_{did_name}");

    deps.emit_output_ref::<TypeEncoder>(
        *task_key,
        TypeEncoderOutputRef {
            snapshot_name: name_s,
            predicate_name: name_p,
            from_primitive: None,
            to_primitive: None,
            snapshot: vcx.alloc(vir::TypeData::Domain(name_s)),
            function_unreachable: vir::vir_format!(vcx, "{name_s}_unreachable"),
            function_snap: vir::vir_format!(vcx, "{name_p}_snap"),
            //method_refold: vir::vir_format!(vcx, "refold_{name_p}"),
            specifics: TypeEncoderOutputRefSub::Enum,
            method_assign: vir::vir_format!(vcx, "assign_{name_p}"),
        },
    );
    let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));

    // TODO: discriminant function

    // TODO: discriminant bounds axioms

    let mut funcs: Vec<vir::DomainFunction<'vir>> = vec![];
    let mut axioms: Vec<vir::DomainAxiom<'vir>> = vec![];
    let mut field_projection_p = Vec::new();

    for variant in adt.variants() {
        mk_emum_variant(
            vcx,
            deps,
            variant,
            ty_s,
            name_s,
            name_p,
            &mut funcs,
            &mut field_projection_p,
            &mut axioms,
        )
    }

    let field_projection_p = vcx.alloc_slice(&field_projection_p);


    let predicate =  vcx.alloc(vir::PredicateData {
        name: name_p,
        args: vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]),
        expr: None,
    }); //TODO


    let pred_app = vcx.alloc(vir::PredicateAppData {
        target: name_p,
        args: vcx.alloc_slice(&[vcx.mk_local_ex("self_p")]),
    });

    let function_snap =vcx.alloc(vir::FunctionData {
        name: vir::vir_format!(vcx, "{name_p}_snap"),
        args: vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]),
        ret: ty_s,
        pres: vcx.alloc_slice(&[vcx.alloc(vir::ExprData::PredicateApp(pred_app))]),
        posts: &[],
        expr: None, //TODO
    });

    Ok(TypeEncoderOutput {
        fields: &[],
        snapshot: vir::vir_domain! { vcx; domain [name_s] {
            with_funcs [funcs];
            with_axioms [axioms];
        } },
        predicate,
        function_unreachable: mk_unreachable(vcx, name_s, ty_s),
        function_snap,
        //method_refold: mk_refold(vcx, name_p, ty_s),
        field_projection_p,
        method_assign: mk_assign(vcx, name_p, ty_s),
    })
}

fn mk_emum_variant<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir>,
    variant: &VariantDef,
    ty_s: &'vir TypeData<'vir>,
    parent_name_s: &'vir str,
    parent_name_p: &'vir str,
    funcs: &mut Vec<&'vir vir::DomainFunctionData<'vir>>,
    field_projection_p: &mut Vec<&'vir FunctionGenData<'vir, !, !>>,
    axioms: &mut Vec<vir::DomainAxiom<'vir>>,
) {
    let substs = ty::List::identity_for_item(vcx.tcx, variant.def_id);
    let fields = variant
        .fields
        .iter()
        .map(|field| {
            deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs))
                .unwrap()
        })
        .collect::<Vec<_>>();

    let did_name = vcx.tcx.item_name(variant.def_id).to_ident_string();
    let name_s = vir::vir_format!(vcx, "{parent_name_s}_variant_{did_name}");
    let name_p = vir::vir_format!(vcx, "{parent_name_p}_variant_{did_name}");


    mk_field_projection_p(
        &fields,
        vcx,
        ty_s,
        name_s,
        name_p,
        funcs,
        field_projection_p,
    );

    read_write_axioms(vcx, ty_s, name_s, &fields, axioms);
}

fn mk_unreachable<'vir>(
    vcx: &'vir vir::VirCtxt,
    snapshot_name: &'vir str,
    snapshot_ty: vir::Type<'vir>,
) -> vir::Function<'vir> {
    vcx.alloc(vir::FunctionData {
        name: vir::vir_format!(vcx, "{snapshot_name}_unreachable"), // TODO: pass from outside?
        args: &[],
        ret: snapshot_ty,
        pres: vcx.alloc_slice(&[vcx.alloc(vir::ExprData::Todo("false"))]),
        posts: &[],
        expr: None,
    })
}
fn mk_simple_predicate<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    predicate_name: &'vir str,
    field_name: &'vir str,
) -> vir::Predicate<'vir> {
    let predicate_body = vcx.alloc(vir::ExprData::AccField(vcx.alloc(vir::AccFieldData {
        recv: vcx.mk_local_ex("self_p"),
        field: field_name,
    })));
    vir::vir_predicate! { vcx; predicate [predicate_name](self_p: Ref) { [predicate_body] } }
}
/*
fn mk_refold<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    predicate_name: &'vir str,
    snapshot_ty: vir::Type<'vir>,
) -> vir::Method<'vir> {
    vcx.alloc(vir::MethodData {
        name: vir::vir_format!(vcx, "refold_{predicate_name}"),
        args: vcx.alloc_slice(&[
            vcx.alloc(vir::LocalDeclData {
                name: "_p",
                ty: vcx.alloc(vir::TypeData::Ref),
            }),
            vcx.alloc(vir::LocalDeclData {
                name: "_s_old",
                ty: snapshot_ty,
            }),
            vcx.alloc(vir::LocalDeclData {
                name: "_s_new",
                ty: snapshot_ty,
            }),
        ]),
        rets: &[],
        pres: vcx.alloc_slice(&[
            vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                target: predicate_name,
                args: vcx.alloc_slice(&[
                    vcx.mk_local_ex("_p"),
                    vcx.mk_local_ex("_s_old"),
                ]),
            }))),
        ]),
        posts: vcx.alloc_slice(&[
            vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                target: predicate_name,
                args: vcx.alloc_slice(&[
                    vcx.mk_local_ex("_p"),
                    vcx.mk_local_ex("_s_new"),
                ]),
            }))),
        ]),
        blocks: None,
    })
}
*/
// TODO: there is a lot of duplication here, both in these assign/
//   reassign methods, and in the match cases below
//   also: is mk_assign really worth it? (used in constant method
//   arguments only)
fn mk_assign<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    predicate_name: &'vir str,
    snapshot_ty: vir::Type<'vir>,
) -> vir::Method<'vir> {
    vcx.alloc(vir::MethodData {
        name: vir::vir_format!(vcx, "assign_{predicate_name}"),
        args: vcx.alloc_slice(&[
            vcx.alloc(vir::LocalDeclData {
                name: "_p",
                ty: vcx.alloc(vir::TypeData::Ref),
            }),
            vcx.alloc(vir::LocalDeclData {
                name: "_s_new",
                ty: snapshot_ty,
            }),
        ]),
        rets: &[],
        pres: &[],
        posts: vcx.alloc_slice(&[
            vcx.mk_pred_app(predicate_name, &[vcx.mk_local_ex("_p")]),
            vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::CmpEq,
                lhs: vcx.mk_func_app(
                    vir::vir_format!(vcx, "{predicate_name}_snap"),
                    &[vcx.mk_local_ex("_p")],
                ),
                rhs: vcx.mk_local_ex("_s_new"),
            }))),
        ]),
        blocks: None,
    })
}

fn mk_snap<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    predicate_name: &'vir str,
    snapshot_name: &'vir str,
    field_name: Option<&'vir str>,
    snapshot_ty: vir::Type<'vir>,
) -> vir::Function<'vir> {
    let pred_app = vcx.alloc(vir::PredicateAppData {
        target: predicate_name,
        args: vcx.alloc_slice(&[vcx.mk_local_ex("self")]),
    });
    vcx.alloc(vir::FunctionData {
        name: vir::vir_format!(vcx, "{predicate_name}_snap"),
        args: vcx.alloc_slice(&[vcx.mk_local_decl("self", &vir::TypeData::Ref)]),
        ret: snapshot_ty,
        pres: vcx.alloc_slice(&[vcx.alloc(vir::ExprData::PredicateApp(pred_app))]),
        posts: &[],
        expr: field_name.map(|field_name| {
            vcx.alloc(vir::ExprData::Unfolding(vcx.alloc(vir::UnfoldingData {
                target: pred_app,
                expr: vcx.alloc(vir::ExprData::Field(vcx.mk_local_ex("self"), field_name)),
            })))
        }),
    })
}

fn mk_struct_snap<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    name_p: &'vir str,
    fields: &[TypeEncoderOutputRef<'vir>],
    ty_s: &'vir TypeData<'vir>,
    cons_name: &'vir str,
) -> vir::Function<'vir> {
    let pred_app = vcx.alloc(vir::PredicateAppData {
        target: name_p,
        args: vcx.alloc_slice(&[vcx.mk_local_ex("self_p")]),
    });

    let cons_args = vcx.alloc_slice(
        &fields
            .iter()
            .enumerate()
            .map(|(idx, field_ty_out)| {
                vcx.mk_func_app(
                    field_ty_out.function_snap,
                    &[vcx.mk_func_app(
                        vir::vir_format!(vcx, "{name_p}_field_{idx}"),
                        &[vcx.mk_local_ex("self_p")],
                    )],
                )
            })
            .collect::<Vec<_>>(),
    );

    vcx.alloc(vir::FunctionData {
        name: vir::vir_format!(vcx, "{name_p}_snap"),
        args: vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]),
        ret: ty_s,
        pres: vcx.alloc_slice(&[vcx.alloc(vir::ExprData::PredicateApp(pred_app))]),
        posts: &[],
        expr: Some(
            vcx.alloc(vir::ExprData::Unfolding(vcx.alloc(vir::UnfoldingData {
                target: pred_app,
                expr: vcx.mk_func_app(cons_name, cons_args),
            }))),
        ),
    })
}

/// for the given fields on the given type create the read_write axioms and push them into the `axioms` Vector
fn read_write_axioms<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    ty_s: &'vir TypeData<'vir>,
    name_s: &'vir str,
    fields: &[TypeEncoderOutputRef<'vir>],
    axioms: &mut Vec<vir::DomainAxiom<'vir>>,
) {
    for (write_idx, write_ty_out) in fields.iter().enumerate() {
        for (read_idx, _read_ty_out) in fields.iter().enumerate() {
            axioms.push(vcx.alloc(vir::DomainAxiomData {
                name: vir::vir_format!(vcx, "ax_{name_s}_write_{write_idx}_read_{read_idx}"),
                expr: if read_idx == write_idx {
                    vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                        qvars: vcx.alloc_slice(&[
                            vcx.mk_local_decl("self", ty_s),
                            vcx.mk_local_decl("val", write_ty_out.snapshot),
                        ]),
                        triggers: vcx.alloc_slice(&[vcx.alloc_slice(&[vcx.mk_func_app(
                            vir::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                            &[vcx.mk_func_app(
                                vir::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                &[vcx.mk_local_ex("self"), vcx.mk_local_ex("val")],
                            )],
                        )])]),
                        body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                            kind: vir::BinOpKind::CmpEq,
                            lhs: vcx.mk_func_app(
                                vir::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                &[vcx.mk_func_app(
                                    vir::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                    &[vcx.mk_local_ex("self"), vcx.mk_local_ex("val")],
                                )],
                            ),
                            rhs: vcx.mk_local_ex("val"),
                        }))),
                    })))
                } else {
                    vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                        qvars: vcx.alloc_slice(&[
                            vcx.mk_local_decl("self", ty_s),
                            vcx.mk_local_decl("val", write_ty_out.snapshot),
                        ]),
                        triggers: vcx.alloc_slice(&[vcx.alloc_slice(&[vcx.mk_func_app(
                            vir::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                            &[vcx.mk_func_app(
                                vir::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                &[vcx.mk_local_ex("self"), vcx.mk_local_ex("val")],
                            )],
                        )])]),
                        body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                            kind: vir::BinOpKind::CmpEq,
                            lhs: vcx.mk_func_app(
                                vir::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                &[vcx.mk_func_app(
                                    vir::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                    &[vcx.mk_local_ex("self"), vcx.mk_local_ex("val")],
                                )],
                            ),
                            rhs: vcx.mk_func_app(
                                vir::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                &[vcx.mk_local_ex("self")],
                            ),
                        }))),
                    })))
                },
            }));
        }
    }
}

/// Create the `_cons_read_` axioms and push them into the `axioms` vector
fn constructor_axioms<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    ty_s: &'vir TypeData<'vir>,
    name_s: &'vir str,
    fields: &[TypeEncoderOutputRef<'vir>],
    cons_name: &'vir str,
    axioms: &mut Vec<vir::DomainAxiom<'vir>>,
) {
    let cons_qvars = vcx.alloc_slice(
        &fields
            .iter()
            .enumerate()
            .map(|(idx, field_ty_out)| {
                vcx.mk_local_decl(vir::vir_format!(vcx, "f{idx}"), field_ty_out.snapshot)
            })
            .collect::<Vec<_>>(),
    );
    let cons_args = fields
        .iter()
        .enumerate()
        .map(|(idx, _field_ty_out)| vcx.mk_local_ex(vir::vir_format!(vcx, "f{idx}")))
        .collect::<Vec<_>>();
    let cons_call = vcx.mk_func_app(cons_name, &cons_args);

    for (read_idx, _) in fields.iter().enumerate() {
        axioms.push(vcx.alloc(vir::DomainAxiomData {
            name: vir::vir_format!(vcx, "ax_{name_s}_cons_read_{read_idx}"),
            expr: vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                qvars: cons_qvars.clone(),
                triggers: vcx.alloc_slice(&[vcx.alloc_slice(&[cons_call])]),
                body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                    kind: vir::BinOpKind::CmpEq,
                    lhs: vcx.mk_func_app(
                        vir::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                        &[cons_call],
                    ),
                    rhs: cons_args[read_idx],
                }))),
            }))),
        }));
    }

    let cons_call_with_reads = vcx.mk_func_app(
        cons_name,
        &fields
            .iter()
            .enumerate()
            .map(|(idx, _field_ty_out)| {
                vcx.mk_func_app(
                    vir::vir_format!(vcx, "{name_s}_read_{idx}"),
                    &[vcx.mk_local_ex("self")],
                )
            })
            .collect::<Vec<_>>(),
    );
    axioms.push(vcx.alloc(vir::DomainAxiomData {
        name: vir::vir_format!(vcx, "ax_{name_s}_cons"),
        expr: vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
            qvars: vcx.alloc_slice(&[vcx.mk_local_decl("self", ty_s)]),
            triggers: vcx.alloc_slice(&[vcx.alloc_slice(&[cons_call_with_reads])]),
            body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                kind: vir::BinOpKind::CmpEq,
                lhs: cons_call_with_reads,
                rhs: vcx.mk_local_ex("self"),
            }))),
        }))),
    }));
}

fn mk_structlike<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir>,
    task_key: &<TypeEncoder as TaskEncoder>::TaskKey<'vir>,
    name_s: &'vir str,
    name_p: &'vir str,
    field_ty_out: Vec<TypeEncoderOutputRef<'vir>>,
) -> Result<
    <TypeEncoder as TaskEncoder>::OutputFullLocal<'vir>,
    (
        <TypeEncoder as TaskEncoder>::EncodingError,
        Option<<TypeEncoder as TaskEncoder>::OutputFullDependency<'vir>>,
    ),
> {
    let mut field_read_names = Vec::new();
    let mut field_write_names = Vec::new();
    let mut field_projection_p_names = Vec::new();
    for idx in 0..field_ty_out.len() {
        field_read_names.push(vir::vir_format!(vcx, "{name_s}_read_{idx}"));
        field_write_names.push(vir::vir_format!(vcx, "{name_s}_write_{idx}"));
        field_projection_p_names.push(vir::vir_format!(vcx, "{name_p}_field_{idx}"));
    }
    let field_read_names = vcx.alloc_slice(&field_read_names);
    let field_write_names = vcx.alloc_slice(&field_write_names);
    let field_projection_p_names = vcx.alloc_slice(&field_projection_p_names);

    deps.emit_output_ref::<TypeEncoder>(
        *task_key,
        TypeEncoderOutputRef {
            snapshot_name: name_s,
            predicate_name: name_p,
            from_primitive: None,
            to_primitive: None,
            snapshot: vcx.alloc(vir::TypeData::Domain(name_s)),
            function_unreachable: vir::vir_format!(vcx, "{name_s}_unreachable"),
            function_snap: vir::vir_format!(vcx, "{name_p}_snap"),
            //method_refold: vir::vir_format!(vcx, "refold_{name_p}"),
            specifics: TypeEncoderOutputRefSub::StructLike(TypeEncoderOutputRefSubStruct {
                field_read: field_read_names,
                field_write: field_write_names,
                field_projection_p: field_projection_p_names,
            }),
            method_assign: vir::vir_format!(vcx, "assign_{name_p}"),
        },
    );
    let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));

    let mut funcs: Vec<vir::DomainFunction<'vir>> = vec![];
    let mut axioms: Vec<vir::DomainAxiom<'vir>> = vec![];

    let cons_name = vir::vir_format!(vcx, "{name_s}_cons");
    funcs.push(
        vcx.alloc(vir::DomainFunctionData {
            unique: false,
            name: cons_name,
            args: vcx.alloc_slice(
                &field_ty_out
                    .iter()
                    .map(|field_ty_out| field_ty_out.snapshot)
                    .collect::<Vec<_>>(),
            ),
            ret: ty_s,
        }),
    );

    let mut field_projection_p = Vec::new();
    mk_field_projection_p(
        &field_ty_out,
        vcx,
        ty_s,
        name_s,
        name_p,
        &mut funcs,
        &mut field_projection_p,
    );

    let field_projection_p = vcx.alloc_slice(&field_projection_p);

    read_write_axioms(vcx, ty_s, name_s, &field_ty_out, &mut axioms);

    constructor_axioms(vcx, ty_s, name_s, &field_ty_out, cons_name, &mut axioms);

    // predicate
    let predicate = {
        let expr = field_ty_out
            .iter()
            .enumerate()
            .map(|(idx, field_ty_out)| {
                vcx.mk_pred_app(
                    field_ty_out.predicate_name,
                    &[vcx.mk_func_app(
                        vir::vir_format!(vcx, "{name_p}_field_{idx}"),
                        &[vcx.mk_local_ex("self_p")],
                    )],
                )
            })
            .reduce(|base, field_expr| vcx.mk_and(base, field_expr))
            .unwrap_or_else(|| vcx.mk_true());

        vcx.alloc(vir::PredicateData {
            name: name_p,
            args: vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]),
            expr: Some(expr),
        })
    };

    Ok(TypeEncoderOutput {
        fields: &[],
        snapshot: vir::vir_domain! { vcx; domain [name_s] {
            with_funcs [funcs];
            with_axioms [axioms];
        } },
        predicate,
        function_unreachable: mk_unreachable(vcx, name_s, ty_s),
        function_snap: mk_struct_snap(vcx, name_p, &field_ty_out, ty_s, cons_name),
        //method_refold: mk_refold(vcx, name_p, ty_s),
        field_projection_p,
        method_assign: mk_assign(vcx, name_p, ty_s),
    })
}

/// add the field projectsions and add the snapshot version to the funcs vector
fn mk_field_projection_p<'vir>(
    fields: &[TypeEncoderOutputRef<'vir>],
    vcx: &'vir vir::VirCtxt<'vir>,
    ty_s: &'vir TypeData<'vir>,
    name_s: &'vir str,
    name_p: &'vir str,
    funcs: &mut Vec<&vir::DomainFunctionData<'vir>>,
    field_projection_p: &mut Vec<&FunctionGenData<'vir, !, !>>,
) {
    let mut field_projection_p = Vec::new();
    for (idx, ty_out) in fields.iter().enumerate() {
        let name_r = vir::vir_format!(vcx, "{name_s}_read_{idx}");
        funcs.push(vir::vir_domain_func! { vcx; function [name_r]([ty_s]): [ty_out.snapshot] });

        let name_w = vir::vir_format!(vcx, "{name_s}_write_{idx}");
        funcs.push(
            vir::vir_domain_func! { vcx; function [name_w]([ty_s], [ty_out.snapshot]): [ty_s] },
        );

        field_projection_p.push(vcx.alloc(vir::FunctionData {
            name: vir::vir_format!(vcx, "{name_p}_field_{idx}"),
            args: vcx.alloc_slice(&[vcx.mk_local_decl("self", &vir::TypeData::Ref)]),
            ret: &vir::TypeData::Ref,
            pres: &[],
            posts: &[],
            expr: None,
        }));
    }
}
