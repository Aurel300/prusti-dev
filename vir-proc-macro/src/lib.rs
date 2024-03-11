#![feature(box_patterns)]

use proc_macro::TokenStream;

mod reify;
pub(crate) mod reify_kind;
mod vir_serde;

// #[proc_macro_derive(VirSerde, attributes(reify_copy, reify_copy_ref))]
#[proc_macro_derive(VirSerde, attributes(vir))]
pub fn derive_vir_serde(input: TokenStream) -> TokenStream {
    vir_serde::derive_vir_serde(input)
}

// #[proc_macro_derive(Reify, attributes(reify_copy, reify_copy_ref))]
#[proc_macro_derive(Reify, attributes(vir))]
pub fn derive_reify(input: TokenStream) -> TokenStream {
    reify::derive_reify(input)
}
