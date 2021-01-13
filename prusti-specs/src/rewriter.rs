use crate::specifications::common::{ExpressionIdGenerator, SpecificationIdGenerator, SpecType};
use crate::specifications::untyped::{self, EncodeTypeCheck};
use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, format_ident};
use syn::spanned::Spanned;
use syn::{Type, punctuated::Punctuated, Pat, Token};

pub(crate) struct AstRewriter {
    expr_id_generator: ExpressionIdGenerator,
    spec_id_generator: SpecificationIdGenerator,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecItemType {
    Precondition,
    Postcondition,
    Predicate,
}

impl std::fmt::Display for SpecItemType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecItemType::Precondition => write!(f, "pre"),
            SpecItemType::Postcondition => write!(f, "post"),
            SpecItemType::Predicate => write!(f, "pred"),
        }
    }
}

impl AstRewriter {
    pub(crate) fn new() -> Self {
        Self {
            expr_id_generator: ExpressionIdGenerator::new(),
            spec_id_generator: SpecificationIdGenerator::new(),
        }
    }

    pub fn generate_expr_id(&mut self) -> untyped::ExpressionId {
        self.expr_id_generator.generate()
    }

    pub fn generate_spec_id(&mut self) -> untyped::SpecificationId {
        self.spec_id_generator.generate()
    }

    /// Parse an expression.
    pub fn parse_expression(
        &mut self,
        spec_id: untyped::SpecificationId,
        tokens: TokenStream,
    ) -> syn::Result<untyped::Expression> {
        untyped::Expression::parse(tokens, spec_id, &mut self.expr_id_generator)
    }

    /// Parse an assertion.
    pub fn parse_assertion(
        &mut self,
        spec_id: untyped::SpecificationId,
        tokens: TokenStream,
    ) -> syn::Result<untyped::Assertion> {
        untyped::Assertion::parse(tokens, spec_id, &mut self.expr_id_generator)
    }

    /// Parse a pledge.
    pub fn parse_pledge(
        &mut self,
        spec_id_lhs: Option<untyped::SpecificationId>,
        spec_id_rhs: untyped::SpecificationId,
        tokens: TokenStream
    ) -> syn::Result<untyped::Pledge> {
        untyped::Pledge::parse(tokens, spec_id_lhs, spec_id_rhs, &mut self.expr_id_generator)
    }

    /// Check whether function `item` contains a parameter called `keyword`. If
    /// yes, return its span.
    fn check_contains_keyword_in_params(&self, item: &untyped::AnyFnItem, keyword: &str) -> Option<Span> {
        for param in &item.sig().inputs {
            match param {
                syn::FnArg::Typed(syn::PatType {
                    pat: box syn::Pat::Ident(syn::PatIdent { ident, .. }),
                    ..
                }) => {
                    if ident == keyword {
                        return Some(param.span());
                    }
                }
                _ => {}
            }
        }
        None
    }
    fn generate_result_arg(&self, item: &untyped::AnyFnItem) -> syn::FnArg {
        let item_span = item.span();
        let output_ty = match &item.sig().output {
            syn::ReturnType::Default => parse_quote_spanned!(item_span=> ()),
            syn::ReturnType::Type(_, ty) => ty.clone(),
        };
        let fn_arg = syn::FnArg::Typed(
            syn::PatType {
                attrs: Vec::new(),
                pat: box parse_quote_spanned!(item_span=> result),
                colon_token: syn::Token![:](item.sig().output.span()),
                ty: output_ty,
            }
        );
        fn_arg
    }

    /// Generate a dummy function for checking the given precondition, postcondition or predicate.
    ///
    /// `spec_type` should be either `"pre"`, `"post"` or `"pred"`.
    pub fn generate_spec_item_fn(
        &mut self,
        spec_type: SpecItemType,
        spec_id: untyped::SpecificationId,
        assertion: untyped::Assertion,
        item: &untyped::AnyFnItem,
    ) -> syn::Result<syn::Item> {
        if let Some(span) = self.check_contains_keyword_in_params(item, "result") {
            return Err(syn::Error::new(
                span,
                "it is not allowed to use the keyword `result` as a function argument".to_string(),
            ));
        }
        let item_span = item.span();
        let item_name = syn::Ident::new(
            &format!("prusti_{}_item_{}_{}", spec_type, item.sig().ident, spec_id),
            item_span,
        );
        let mut statements = TokenStream::new();
        assertion.encode_type_check(&mut statements);
        let spec_id_str = spec_id.to_string();
        let assertion_json = crate::specifications::json::to_json_string(&assertion);

        let mut spec_item: syn::ItemFn = parse_quote_spanned! {item_span=>
            #[allow(unused_must_use, unused_variables, dead_code)]
            #[prusti::spec_only]
            #[prusti::spec_id = #spec_id_str]
            #[prusti::assertion = #assertion_json]
            fn #item_name() {
                #statements
            }
        };
        spec_item.sig.generics = item.sig().generics.clone();
        spec_item.sig.inputs = item.sig().inputs.clone();
        if spec_type == SpecItemType::Postcondition {
            let fn_arg = self.generate_result_arg(item);
            spec_item.sig.inputs.push(fn_arg);
        }
        Ok(syn::Item::Fn(spec_item))
    }

    /// Generate statements for checking the given loop invariant.
    pub fn generate_spec_loop(
        &mut self,
        spec_id: untyped::SpecificationId,
        assertion: untyped::Assertion,
    ) -> TokenStream {
        let mut statements = TokenStream::new();
        assertion.encode_type_check(&mut statements);
        let spec_id_str = spec_id.to_string();
        let assertion_json = crate::specifications::json::to_json_string(&assertion);
        let callsite_span = Span::call_site();
        quote_spanned! {callsite_span=>
            #[allow(unused_must_use, unused_variables)]
            {
                #[prusti::spec_only]
                #[prusti::loop_body_invariant_spec]
                #[prusti::spec_id = #spec_id_str]
                #[prusti::assertion = #assertion_json]
                || {
                    #statements
                };
            }
        }
    }

    /// Generate statements for checking a closure specification.
    /// TODO: arguments, result (types are typically not known yet after parsing...)
    /// TODO: refactor so that generate_cl_spec does more (too much preprocessing
    /// currently in lib::closure.
    pub fn generate_cl_spec(
        &mut self,
        inputs: Punctuated<Pat, Token![,]>,
        output: Type,
        preconds: Vec<(untyped::SpecificationId, untyped::Assertion)>,
        postconds: Vec<(untyped::SpecificationId, untyped::Assertion)>,
        invariants: Vec<(untyped::SpecificationId, untyped::Assertion)>,
        views: Vec<(untyped::ExpressionId, untyped::Expression)>,
    ) -> (TokenStream, TokenStream, TokenStream, TokenStream) {
        let callsite_span = Span::call_site();
        let process_cond = |spec_type: SpecType, id: &untyped::SpecificationId,
                            assertion: &untyped::Assertion| -> TokenStream
        {
            let spec_id_str = id.to_string();
            let mut encoded = TokenStream::new();
            assertion.encode_type_check(&mut encoded);
            let assertion_json = crate::specifications::json::to_json_string(&assertion);
            let name = format_ident!("prusti_{}_closure_{}", match spec_type {
                SpecType::Precondition => "pre",
                SpecType::Postcondition => "post",
                SpecType::HistoryInvariant => "invariant",
                _ => unimplemented!(),
            }, spec_id_str);
            let result = if spec_type == SpecType::Postcondition && !inputs.empty_or_trailing() {
                quote_spanned! { callsite_span => , result: #output }
            } else if spec_type == SpecType::Postcondition {
                quote_spanned! { callsite_span => result: #output }
            } else {
                TokenStream::new()
            };
            quote_spanned! { callsite_span =>
                #[prusti::spec_only]
                #[prusti::spec_id = #spec_id_str]
                #[prusti::assertion = #assertion_json]
                fn #name(#inputs #result) {
                    #encoded
                }
            }
        };

        let mut pre_ts = TokenStream::new();
        for (id, precond) in preconds {
            pre_ts.extend(process_cond(SpecType::Precondition, &id, &precond));
        }

        let mut post_ts = TokenStream::new();
        for (id, postcond) in postconds {
            post_ts.extend(process_cond(SpecType::Postcondition, &id, &postcond));
        }

        let mut invariants_ts = TokenStream::new();
        for (id, invariant) in invariants {
            invariants_ts.extend(process_cond(SpecType::HistoryInvariant, &id, &invariant));
        }

        let mut views_ts = TokenStream::new();
        for (id, expr) in views {
            let expr_id_str = id.to_string();
            let mut encoded = TokenStream::new();
            expr.encode_type_check_any(&mut encoded);
            // TODO: type check specifically for view type
            // let ty = view.ty;
            views_ts.extend(quote_spanned! { callsite_span =>
                #[prusti::spec_only]
                #[prusti::expr_id = #expr_id_str]
                || {
                    #encoded
                };
            })
        }

        (pre_ts, post_ts, invariants_ts, views_ts)
    }
}
