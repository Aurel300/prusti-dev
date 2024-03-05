/// Determines how data should be treated during reification, as well as
/// de/serialisation.
pub(crate) enum ReifyKind {
    /// String reference, `&'vir str`.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise as `String`.
    //  Deser: allocate into arena.
    String,

    /// Slice of a reifiable type, e.g. `&'vir [Expr<'vir>]`.
    ///
    /// Reify: reify every element.
    ///   Ser: serialise every element as owned data.
    /// Deser: allocate every element into arena.
    SliceReify,

    /// Slice of a non-refiable type, e.g. `&'vir [LocalDecl<'vir>]`.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise every element as owned data.
    /// Deser: allocate every element into arena.
    SliceCopy,

    /// Option of a reifiable type, e.g. `Option<Expr<'vir>>`.
    ///
    /// Reify: reify value, if present.
    ///   Ser: serialise value as owned data, if present.
    /// Deser: allocate value into arena.
    OptionReify,

    // TODO: `OptionCopy`?

    /// Reference to a non-reifiable type.
    ///
    /// Reify: passthrough.
    ///   Ser: default serde implementation.
    /// Deser: default serde implementation.
    Copy,

    /// Reference to a reifiable type.
    ///
    /// Reify: passthrough.
    ///   Ser: serialise as owned data.
    /// Deser: allocate value into arena.
    CopyRef,

    /// Other types.
    ///
    /// Reify: reify value.
    ///   Ser: default serde implementation.
    /// Deser: default serde implementation.
    Other,
}

impl ReifyKind {
    pub(crate) fn of_field(field: &syn::Field) -> ReifyKind {
        let is_reify_copy = field.attrs.iter()
            .filter_map(|attr| match &attr.meta {
                syn::Meta::Path(p) => Some(&p.segments),
                _ => None,
            })
            .any(|segs| segs.len() == 1 && segs[0].ident == "reify_copy");
        let is_reify_copy_ref = field.attrs.iter()
            .filter_map(|attr| match &attr.meta {
                syn::Meta::Path(p) => Some(&p.segments),
                _ => None,
            })
            .any(|segs| segs.len() == 1 && segs[0].ident == "reify_copy_ref");
        assert!(!is_reify_copy || !is_reify_copy_ref);

        if matches!(&field.ty, syn::Type::Reference(syn::TypeReference {
            mutability: None,
            elem: box syn::Type::Path(syn::TypePath {
                qself: None,
                path: syn::Path {
                    leading_colon: None,
                    segments,
                },
            }),
            ..
        }) if segments.len() == 1 && matches!(&segments[0], syn::PathSegment {
            ident,
            arguments: syn::PathArguments::None,
        } if ident == "str")) {
            assert!(!is_reify_copy && !is_reify_copy_ref);
            return ReifyKind::String;
        }

        if matches!(&field.ty, syn::Type::Reference(syn::TypeReference {
            mutability: None,
            elem: box syn::Type::Slice(_),
            ..
        })) {
            assert!(!is_reify_copy_ref);
            if is_reify_copy {
                return ReifyKind::SliceCopy;
            } else {
                return ReifyKind::SliceReify;
            }
        }

        if matches!(&field.ty, syn::Type::Path(syn::TypePath {
            qself: None,
            path: syn::Path {
                leading_colon: None,
                segments,
            },
        }) if segments.len() == 1 && matches!(&segments[0], syn::PathSegment {
            ident,
            arguments: syn::PathArguments::AngleBracketed(..),
        } if ident == "Option")) {
            assert!(!is_reify_copy && !is_reify_copy_ref);
            return ReifyKind::OptionReify;
        }

        if is_reify_copy {
            ReifyKind::Copy
        } else if is_reify_copy_ref {
            ReifyKind::CopyRef
        } else {
            ReifyKind::Other
        }
    }

    pub(crate) fn should_reify(&self) -> bool {
        matches!(self, Self::SliceReify | Self::OptionReify | Self::Other)
    }
}
