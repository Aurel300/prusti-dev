#![feature(rustc_private)]
#![feature(local_key_cell_methods)]
#![feature(never_type)]
#![feature(iter_intersperse)]

mod context;
mod data;
mod debug;
mod gendata;
mod genrefs; // TODO: explain gen...
mod macros;
mod refs;
mod reify;
mod functionidentifier;

pub use context::*;
pub use data::*;
pub use gendata::*;
pub use genrefs::*;
pub use refs::*;
pub use reify::*;
pub use functionidentifier::*;

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
