use syn::parse::{Parse, ParseStream};

pub(crate) struct ClosureWithSpec {
    pub pres: Vec<syn::Expr>,
    pub posts: Vec<syn::Expr>,
    pub invariants: Vec<syn::Expr>,
    pub views: Vec<ClosureView>,
    pub cl: syn::ExprClosure,
}

pub(crate) struct ClosureView {
    pub ident: syn::Ident,
    pub ty: syn::Type,
    pub expr: syn::Expr,
}

impl Parse for ClosureWithSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut cl: syn::ExprClosure = input.parse()?;

        let mut pres: Vec<syn::Result<syn::Expr>> = vec![];
        let mut posts: Vec<syn::Result<syn::Expr>> = vec![];
        let mut invariants: Vec<syn::Result<syn::Expr>> = vec![];
        let mut views: Vec<syn::Result<ClosureView>> = vec![];

        // collect and remove any specification attributes
        // leave other attributes intact
        cl.attrs.drain_filter(|attr| {
            if let Some(id) = attr.path.get_ident() {
                match id.to_string().as_ref() {
                    "requires" => pres.push(syn::parse2(attr.tokens.clone())),
                    "ensures" => posts.push(syn::parse2(attr.tokens.clone())),
                    "invariant" => invariants.push(syn::parse2(attr.tokens.clone())),
                    "view" => views.push(syn::parse2(attr.tokens.clone())),
                    _ => return false
                }
                true
            } else {
                false
            }
        });

        Ok(Self {
            pres: pres.into_iter().collect::<syn::Result<Vec<_>>>()?,
            posts: posts.into_iter().collect::<syn::Result<Vec<_>>>()?,
            invariants: invariants.into_iter().collect::<syn::Result<Vec<_>>>()?,
            views: views.into_iter().collect::<syn::Result<Vec<_>>>()?,
            cl
        })
    }
}

impl Parse for ClosureView {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident: syn::Ident = input.parse()?;
        input.parse::<syn::Token![:]>()?;
        let ty: syn::Type = input.parse()?;
        input.parse::<syn::Token![=]>()?;
        let expr: syn::Expr = input.parse()?;

        Ok(Self {
            ident,
            ty,
            expr,
        })
    }
}
