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
mod refs;
mod reify;
mod callable_idents;
mod folder;
mod opt;

pub use callable_idents::*;
pub use context::*;
pub use data::*;
pub use folder::*;
pub use gendata::*;
pub use genrefs::*;
pub use opt::*;
pub use refs::*;
pub use reify::*;

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
