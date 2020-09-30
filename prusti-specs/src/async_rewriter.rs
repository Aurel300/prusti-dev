use syn::visit_mut::{self, VisitMut};
use syn::{parse_quote, ItemFn, Expr};
use quote::quote;

/// Rewrite async functions into fake-synchronous versions that Prusti can
/// verify. Regular functions are left untouched.
///
/// Async functions are rewritten from:
///
/// ```rust
/// async fn func_name(inputs...) -> ReturnType {
///     statements...
/// }
/// ```
///
/// Into:
///
/// ```rust
/// fn func_name(inputs...) -> Box<dyn Future<Output = ReturnType>> {
///     if false {
///         prusti_contracts::fake_async({ transformed_statements... })
///     } else {
///         Box::new(async { statements... })
///     }
/// }
/// ```
///
/// Where `transformed_statements` are obtained by replacing `.await`
/// expressions with calls to `prusti_contracts::fake_await`.
pub fn rewrite_item(item: &mut ItemFn) {
    if !item.sig.asyncness.is_some() {
        return;
    }
    println!("before: {}", quote!(#item));
    AsyncRewriter.visit_item_fn_mut(item);
    println!("after:  {}", quote!(#item));
    panic!("TODO");
}

struct AsyncRewriter;

impl VisitMut for AsyncRewriter {
    fn visit_item_fn_mut(&mut self, node: &mut ItemFn) {
        if node.sig.asyncness.is_some() {
            node.sig.asyncness = None;
            let ItemFn {
                attrs,
                vis,
                ref mut sig,
                ref mut block
            } = node;
            /*
            if let syn::ReturnType::Type(_, ref ty) = sig.output {
                sig.output = parse_quote!( -> Box<dyn Future<Output = #ty>> );
            } else {
                sig.output = parse_quote!( -> Box<dyn Future<Output = ()>> );
            }
            */
            if let syn::ReturnType::Type(_, ref ty) = sig.output {
                sig.output = parse_quote!( -> impl std::future::Future<Output = #ty> );
            } else {
                sig.output = parse_quote!( -> impl std::future::Future<Output = ()> );
            }
            // let original_block = block.clone();
            visit_mut::visit_block_mut(self, block);
            *node = parse_quote!(
                #(#attrs)* #vis #sig {
                    prusti_contracts::fake_async(
                        //#[prusti_fake_sync]
                        || #block
                    )
                    /*
                    if false {
                        Box::new(prusti_contracts::fake_async(#block))
                    } else {
                        Box::new(async #original_block)
                    }
                    */
                }
            );
        }
    }

    fn visit_expr_mut(&mut self, node: &mut Expr) {
        match &node {
            Expr::Await(syn::ExprAwait {attrs, base: box expr, ..}) => {
                *node = parse_quote!(#(#attrs)* prusti_contracts::fake_await(#expr));
            }
            Expr::Macro(syn::ExprMacro {attrs, mac: syn::Macro {
                path,
                tokens,
                ..
            }}) => {
                match path.segments.last().unwrap().ident.to_string().as_str() {
                    "join" => {
                        let args: syn::punctuated::Punctuated<Expr, syn::Token!(,)> = parse_quote!(#tokens);
                        let wrapped_args = args.iter()
                            .map(|arg| {
                                let wrapped: syn::Expr = parse_quote!(prusti_contracts::fake_await(#arg));
                                wrapped
                            })
                            .collect::<Vec<syn::Expr>>();
                        *node = parse_quote!( #(#attrs)* ( #(#wrapped_args),* ) );
                    },
                    "select" => {
                        unimplemented!("select!");
                    },
                    _ => {
                        visit_mut::visit_expr_mut(self, node);
                    }
                }
            }
            _ => {
                visit_mut::visit_expr_mut(self, node);
            }
        }
    }
}
