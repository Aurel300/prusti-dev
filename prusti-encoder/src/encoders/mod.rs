mod mir_builtin;
mod mir_pure;
<<<<<<< HEAD
=======
mod mir_poly_impure;
>>>>>>> ide/rewrite-2023-assistant-features
mod mir_impure;
mod spec;
mod pure;
mod local_def;
pub(super) mod ty;
mod r#const;
// TODO: move `mir_impure` to this dir:
pub mod impure;
/// Encoders for Rust functions (pure and impure)
pub mod mir_fn;

<<<<<<< HEAD
=======
cfg_if::cfg_if! {
    if #[cfg(feature = "mono_function_encoding")] {
        pub use mono::mir_pure_function::MirMonoFunctionEnc as PureFunctionEnc;
    } else {
        pub use mir_pure_function::MirFunctionEnc as PureFunctionEnc;
    }
}


pub use mono::task_description::*;
pub use pure::*;
pub use pure::spec::MirSpecEnc;
pub use local_def::*;
pub use r#type::*;
pub use generic::GenericEnc;
pub use mir_builtin::{
    MirBuiltinEnc,
    MirBuiltinEncTask,
};
pub use mir_poly_impure::MirPolyImpureEnc;
pub use mono::mir_impure::MirMonoImpureEnc;
pub use mir_impure::{ImpureEncVisitor, MirImpureEnc};
pub use mir_pure::{
    PureKind,
    MirPureEnc,
    MirPureEncTask,
};
pub use spec::{
    SpecEnc,
    SpecEncOutput,
    SpecEncTask,
};
pub(super) use spec::{init_def_spec, with_proc_spec};
pub use snapshot::SnapshotEnc;
pub use predicate::{
    PredicateEnc,
    PredicateEncOutputRef,
    PredicateEncOutput,
};
pub use domain::all_outputs as DomainEnc_all_outputs;
pub use viper_tuple::{
    ViperTupleEnc,
    ViperTupleEncOutput,
};
>>>>>>> ide/rewrite-2023-assistant-features
pub use r#const::ConstEnc;
pub use impure::fn_wand::{WandEnc, WandEncOutput, WandEncTask};
pub use local_def::*;
pub use mir_builtin::{MirBuiltinEnc, MirBuiltinEncTask};
pub use mir_fn::{FunctionCallEnc, MethodCallEnc, encode_all_in_crate};
pub use mir_impure::ImpureEncVisitor;
pub use mir_pure::{MirPureEnc, MirPureEncTask, PureKind};
pub use pure::spec::MirSpecEnc;
pub(super) use spec::with_proc_spec;
pub use spec::{SpecEnc, SpecEncTask, is_function_trusted, is_type_trusted};
pub use ty::{
    use_impure::TyUseImpureEnc,
    use_pure::TyUsePureEnc,
    viper_tuple::{ViperTupleEnc, ViperTupleEncOutput},
};

/// Some encoders work for both pure and impure encodings, though might output
/// something slightly different for the two. This allows them to be generic in
/// that regard and reuse code.
pub(crate) trait Purity:
    'static + std::fmt::Debug + Clone + Copy + PartialEq + Eq + std::hash::Hash
{
}

/// Some encoders work for both pure and impure encodings, though might output
/// something slightly different for the two. This allows them to be generic in
/// that regard and reuse code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pure;

impl Purity for Pure {}

/// Some encoders work for both pure and impure encodings, though might output
/// something slightly different for the two. This allows them to be generic in
/// that regard and reuse code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Impure;

impl Purity for Impure {}
