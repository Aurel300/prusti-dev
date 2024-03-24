#![feature(rustc_private)]
#![feature(never_type)]
#![feature(iter_intersperse)]

mod context;
mod data;
mod debug;
mod debug_info;
mod gendata;
mod genrefs; // TODO: explain gen...
mod macros;
mod make;
mod refs;
mod reify;
mod serde;
mod callable_idents;
mod viper_ident;

// `fmt_domain_with_extras` can be removed once we're encoding the Viper AST via
// JNI
pub use debug::fmt_domain_with_extras;
pub use context::*;
pub use data::*;
pub use gendata::*;
pub use genrefs::*;
pub use refs::*;
pub use reify::*;
pub use callable_idents::*;
pub use viper_ident::*;

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
