/// The preparser processes Prusti syntax into Rust syntax.

use proc_macro2::{Span, TokenStream, TokenTree, Delimiter};
use std::collections::VecDeque;
use quote::{ToTokens, quote_spanned};
use proc_macro2::Punct;
use proc_macro2::Spacing::*;

/// The representation of an argument to a quantifier (for example `a: i32`)
#[derive(Debug, Clone)]
pub struct Arg {
    pub name: syn::Ident,
    pub typ: syn::Type
}

pub fn parse_prusti(tokens: TokenStream) -> syn::Result<TokenStream> {
    let parsed = PrustiTokenStream::new(tokens).parse()?;
    //println!("parsed? {}", parsed);
    // to make sure we catch errors in the Rust syntax early (and with the
    // correct spans), we try to parse the resulting stream using syn here
    syn::parse2::<syn::Expr>(parsed.clone())?;
    Ok(parsed)
}
pub fn parse_prusti_pledge_rhs_only(tokens: TokenStream) -> syn::Result<TokenStream> {
    todo!() // Parser::new(tokens).extract_pledge_rhs_only_expr()
}
pub fn parse_prusti_pledge(tokens: TokenStream) -> syn::Result<TokenStream> {
    todo!() // Parser::new(tokens).extract_pledge_expr()
}

/*
Preparsing consists of two stages:

1. In [PrustiTokenStream::new], we map a [TokenStream] to a [PrustiTokenStream]
   by identifying unary and binary operators. We also take care of Rust binary
   operators that have lower precedence than the Prusti ones. Note that at this
   token-based stage, a "binary operator" includes e.g. the semicolon for
   statement sequencing.

2. In [PrustiTokenStream::parse], we perform the actual parsing as well as the
   translation back to Rust syntax. The parser is a Pratt parser with binding
   powers defined in [PrustiBinaryOp::binding_power]. Performing translation to
   Rust syntax in this step allows us to not have to define data types for the
   Prusti AST, as we reuse the Rust AST (i.e. [TokenTree] and [TokenStream]).
*/

/// The preparser reuses [syn::Result] to integrate with the rest of the specs
/// library, even though syn is not used here.
fn error<T>(span: Span, msg: &str) -> syn::Result<T> {
    syn::Result::Err(syn::parse::Error::new(span, msg))
}

#[derive(Debug, Clone)]
struct PrustiTokenStream {
    tokens: VecDeque<PrustiToken>,
}

impl PrustiTokenStream {
    /// Constructs a stream of Prusti tokens from a stream of Rust tokens.
    fn new(source: TokenStream) -> Self {
        let source = source.into_iter().collect::<Vec<_>>();

        let mut pos = 0;
        let mut tokens = VecDeque::new();

        // TODO: figure out syntax for spec entailments (|= is taken in Rust)

        while pos < source.len() {
            // no matter what tokens we see, we will consume at least one
            pos += 1;
            tokens.push_back(match (&source[pos - 1], source.get(pos), source.get(pos + 1)) {
                (
                    token @ TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2)),
                    Some(TokenTree::Punct(p3)),
                ) if let Some(op) = PrustiToken::parse_op3(p1, p2, p3) => {
                    // this was a three-character operator, consume two
                    // additional tokens
                    pos += 2;
                    op
                }
                (
                    token @ TokenTree::Punct(p1),
                    Some(TokenTree::Punct(p2)),
                    _,
                ) if let Some(op) = PrustiToken::parse_op2(p1, p2) => {
                    // this was a three-character operator, consume one
                    // additional token
                    pos += 1;
                    op
                }
                (TokenTree::Ident(ident), _, _) if ident == "outer" =>
                    PrustiToken::Outer(ident.span()),
                (TokenTree::Ident(ident), _, _) if ident == "forall" =>
                    PrustiToken::Quantifier(ident.span(), Quantifier::Forall),
                (TokenTree::Ident(ident), _, _) if ident == "exists" =>
                    PrustiToken::Quantifier(ident.span(), Quantifier::Exists),
                (TokenTree::Punct(punct), _, _)
                    if punct.as_char() == ',' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Comma)),
                (TokenTree::Punct(punct), _, _)
                    if punct.as_char() == ';' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Semicolon)),
                (TokenTree::Punct(punct), _, _)
                    if punct.as_char() == '=' && punct.spacing() == Alone =>
                    PrustiToken::BinOp(punct.span(), PrustiBinaryOp::Rust(RustOp::Assign)),
                (token @ TokenTree::Punct(punct), _, _) if punct.spacing() == Joint => {
                    // make sure to fully consume any Rust operator
                    // to avoid later mis-identifying its suffix
                    tokens.push_back(PrustiToken::Token(token.clone()));
                    while let Some(token @ TokenTree::Punct(p)) = source.get(pos) {
                        pos += 1;
                        tokens.push_back(PrustiToken::Token(token.clone()));
                        if p.spacing() != Joint {
                            break;
                        }
                    }
                    continue;
                }
                (TokenTree::Group(group), _, _) => PrustiToken::Group(
                    group.span(),
                    group.delimiter(),
                    box Self::new(group.stream()),
                ),
                (token, _, _) => PrustiToken::Token(token.clone()),
            });
        }
        Self { tokens }
    }

    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Processes a Prusti token stream back into Rust syntax.
    fn parse(mut self) -> syn::Result<TokenStream> {
        self.expr_bp(0)
    }

    /// The core of the Pratt parser algorithm. [self.tokens] is the source of
    /// "lexemes". [min_bp] is the minimum binding power we need to see when
    /// identifying a binary operator.
    /// See https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
    fn expr_bp(&mut self, min_bp: u8) -> syn::Result<TokenStream> {
        let mut lhs = match self.tokens.pop_front() {
            Some(PrustiToken::Group(span, delimiter, box stream)) => {
                let mut group = proc_macro2::Group::new(
                    delimiter,
                    stream.parse()?,
                );
                group.set_span(span);
                TokenTree::Group(group).to_token_stream()
            }
            Some(PrustiToken::Outer(span)) => {
                let mut stream = self.pop_group(Delimiter::Parenthesis)
                    .ok_or(syn::parse::Error::new(span, "expected parenthesized expression after outer"))?;
                todo!()
            }
            Some(PrustiToken::Quantifier(span, kind)) => {
                let mut stream = self.pop_group(Delimiter::Parenthesis)
                    .ok_or(syn::parse::Error::new(span, "expected parenthesized expression after quantifier"))?;
                let args = stream.pop_closure_args()
                    .ok_or(syn::parse::Error::new(span, "expected quantifier body"))?;
                let triggers = stream.extract_triggers()?;
                if args.is_empty() {
                    return error(span, "a quantifier must have at least one argument");
                }
                let args = args.parse()?;
                let body = stream.parse()?;
                kind.translate(span, triggers, args, body)
            }

            Some(PrustiToken::SpecEnt(span, _))
            | Some(PrustiToken::CallDesc(span, _)) =>
                return error(span, "unexpected operator"),
            
            Some(PrustiToken::BinOp(span, _)) =>
                return error(span, "unexpected binary operator"),
            Some(PrustiToken::Token(token)) => token.to_token_stream(),
            None => return Ok(TokenStream::new()),
        };
        loop {
            let (span, op) = match self.tokens.front() {
                // If we see a group or token, we simply add them to the
                // current LHS. This way fragments of Rust code with higher-
                // precedence operators (e.g. plus) are connected into atoms
                // as far as our parser is concerned.
                Some(PrustiToken::Group(span, delimiter, box stream)) => {
                    let mut group = proc_macro2::Group::new(
                        *delimiter,
                        stream.clone().parse()?,
                    );
                    group.set_span(*span);
                    lhs.extend(TokenTree::Group(group).to_token_stream());
                    self.tokens.pop_front();
                    continue;
                }
                Some(PrustiToken::Token(token)) => {
                    lhs.extend(token.to_token_stream());
                    self.tokens.pop_front();
                    continue;
                }

                Some(PrustiToken::SpecEnt(span, once)) => {
                    let span = *span;
                    let once = *once;
                    self.tokens.pop_front();
                    let args = self.pop_closure_args()
                        .ok_or(syn::parse::Error::new(span, "expected closure arguments"))?;
                    let contract = self.pop_group(Delimiter::Bracket)
                        .ok_or(syn::parse::Error::new(span, "expected closure specification in brackets"))?;
                    lhs = translate_spec_ent(
                        span,
                        once,
                        lhs,
                        args
                            .split(PrustiBinaryOp::Rust(RustOp::Comma))
                            .into_iter()
                            .map(|stream| stream.parse())
                            .collect::<Result<Vec<_>, _>>()?,
                        contract
                            .split(PrustiBinaryOp::Rust(RustOp::Comma))
                            .into_iter()
                            .map(|stream| stream.pop_closure_spec().unwrap())
                            // TODO: assert empty afterwards ...
                            .map(|stream| stream.parse())
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    continue;
                }

                Some(PrustiToken::CallDesc(span, _)) => todo!("call desc"),

                Some(PrustiToken::BinOp(span, op)) => (*span, op.clone()),
                Some(PrustiToken::Outer(span)) =>
                    return error(*span, "unexpected outer"),
                Some(PrustiToken::Quantifier(span, op)) =>
                    return error(*span, "unexpected quantifier"),

                None => break,
            };
            let (l_bp, r_bp) = op.binding_power();
            if l_bp < min_bp {
                break;
            }
            self.tokens.pop_front();
            let rhs = self.expr_bp(r_bp)?;
            // TODO: explain
            if !matches!(op, PrustiBinaryOp::Rust(_)) && rhs.is_empty() {
                return error(span, "expected expression");
            }
            lhs = op.translate(span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn pop_group(&mut self, delimiter: Delimiter) -> Option<Self> {
        match self.tokens.pop_front() {
            Some(PrustiToken::Group(_, del, box stream)) if del == delimiter
                => Some(stream),
            _ => None,
        }
    }

    fn pop_closure_args(&mut self) -> Option<Self> {
        let mut tokens = VecDeque::new();

        // special case: empty closure might be parsed as a logical or
        if matches!(self.tokens.front(), Some(PrustiToken::BinOp(_, PrustiBinaryOp::Or))) {
            return Some(Self { tokens });
        }

        if !self.tokens.pop_front()?.is_closure_brace() {
            return None;
        }
        loop {
            let token = self.tokens.pop_front()?;
            if token.is_closure_brace() {
                break;
            }
            tokens.push_back(token);
        }
        Some(Self { tokens })
    }

    fn pop_closure_spec(mut self) -> Option<ClosureSpec<PrustiTokenStream>> {
        // TODO: clean up the interface somehow ...
        if self.tokens.len() == 0 {
            return None;
        }
        if self.tokens.len() != 2 {
            panic!();
        }
        match [
            &self.tokens[0],
            &self.tokens[1],
        ] {
            [
                PrustiToken::Token(TokenTree::Ident(ident)),
                PrustiToken::Group(span, Delimiter::Parenthesis, box group),
            ] => {
                if ident == "requires" {
                    Some(ClosureSpec::Requires(group.clone()))
                } else if ident == "ensures" {
                    Some(ClosureSpec::Ensures(group.clone()))
                } else {
                    None
                }
            }
            _ => None
        }
    }

    fn split(self, split_on: PrustiBinaryOp) -> Vec<Self> {
        self.tokens
            .into_iter()
            .collect::<Vec<_>>()
            .split(|token| matches!(token, PrustiToken::BinOp(_, t) if *t == split_on))
            .map(|group| Self { tokens: group.into_iter().cloned().collect() })
            .collect()
    }

    fn extract_triggers(&mut self) -> syn::Result<Vec<Vec<TokenStream>>> {
        let len = self.tokens.len();
        if len < 4 {
            return Ok(vec![]);
        }
        match [
            &self.tokens[len - 4],
            &self.tokens[len - 3],
            &self.tokens[len - 2],
            &self.tokens[len - 1]
        ] {
            [
                PrustiToken::BinOp(_, PrustiBinaryOp::Rust(RustOp::Comma)),
                PrustiToken::Token(TokenTree::Ident(ident)),
                PrustiToken::BinOp(_, PrustiBinaryOp::Rust(RustOp::Assign)),
                PrustiToken::Group(_, Delimiter::Bracket, box triggers),
            ] if ident == "triggers" => {
                let triggers = triggers.clone()
                    .split(PrustiBinaryOp::Rust(RustOp::Comma))
                    .into_iter()
                    .map(|stream| stream.clone()
                        .pop_group(Delimiter::Parenthesis)
                        .unwrap()
                        .split(PrustiBinaryOp::Rust(RustOp::Comma))
                        .into_iter()
                        .map(|stream| stream.parse())
                        .collect::<Result<Vec<_>, _>>())
                    .collect::<Result<Vec<_>, _>>();
                self.tokens.truncate(len - 4);
                triggers
            }
            _ => Ok(vec![]),
        }
    }
}

enum ClosureSpec<T> {
    Requires(T),
    Ensures(T),
}

impl ClosureSpec<PrustiTokenStream> {
    fn parse(self) -> syn::Result<ClosureSpec<TokenStream>> {
        Ok(match self {
            ClosureSpec::Requires(stream) => ClosureSpec::Requires(stream.parse()?),
            ClosureSpec::Ensures(stream) => ClosureSpec::Ensures(stream.parse()?),
        })
    }
}

#[derive(Debug, Clone)]
enum PrustiToken {
    Group(Span, Delimiter, Box<PrustiTokenStream>),
    Token(TokenTree),
    BinOp(Span, PrustiBinaryOp),
    // TODO: add note about unops not sharing a variant, descriptions ...
    Outer(Span),
    Quantifier(Span, Quantifier),
    SpecEnt(Span, bool),
    CallDesc(Span, bool),
}

fn fn_type_extractor(arg_count: usize) -> TokenStream {
    todo!()
}

fn translate_spec_ent(
    span: Span,
    once: bool,
    cl_expr: TokenStream,
    cl_args: Vec<TokenStream>,
    contract: Vec<ClosureSpec<TokenStream>>,
) -> TokenStream {
    let once = if once {
        quote_spanned! { span => true }
    } else {
        quote_spanned! { span => false }
    };

    let arg_count = cl_args.len();
    let generics_args = (0..arg_count)
        .map(|i| TokenTree::Ident(proc_macro2::Ident::new(&format!("GA{}", i), span)))
        .collect::<Vec<_>>();
    let generic_res = TokenTree::Ident(proc_macro2::Ident::new(&"GR", span));

    let extract_args = (0..arg_count)
        .map(|i| TokenTree::Ident(proc_macro2::Ident::new(&format!("__extract_arg{}", i), span)))
        .collect::<Vec<_>>();
    let extract_args_decl = extract_args.iter()
        .zip(generics_args.iter())
        .map(|(ident, arg_type)| quote_spanned! { span =>
            #[prusti::spec_only]
            fn #ident<
                #(#generics_args),* ,
                #generic_res,
                F: FnOnce( #(#generics_args),* ) -> #generic_res
            >(_f: &F) -> #arg_type { unreachable!() }
        })
        .collect::<Vec<_>>();

    let preconds = contract.iter()
        .filter_map(|spec| match spec {
            ClosureSpec::Requires(stream) => Some(stream.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let postconds = contract.into_iter()
        .filter_map(|spec| match spec {
            ClosureSpec::Ensures(stream) => Some(stream),
            _ => None,
        })
        .collect::<Vec<_>>();

    // TODO: figure out `outer`

    quote_spanned! { span => {
        let __cl_ref = & #cl_expr;
        #(#extract_args_decl)*
        #[prusti::spec_only]
        fn __extract_res<
            #(#generics_args),* ,
            #generic_res,
            F: FnOnce( #(#generics_args),* ) -> #generic_res
        >(_f: &F) -> #generic_res { unreachable!() }
        #( let #cl_args = #extract_args(__cl_ref); )*
        let result = __extract_res(__cl_ref);
        specification_entailment(
            #once,
            __cl_ref,
            ( #( #[prusti::spec_only] || -> bool { ((#preconds): bool) }, )* ),
            ( #( #[prusti::spec_only] || -> bool { ((#postconds): bool) }, )* ),
        )
    } }
}

#[derive(Debug, Clone)]
enum Quantifier {
    Forall,
    Exists,
}

impl Quantifier {
    fn translate(
        &self,
        span: Span,
        triggers: Vec<Vec<TokenStream>>,
        args: TokenStream,
        body: TokenStream,
    ) -> TokenStream {
        let trigger_sets = triggers.into_iter()
            .map(|set| quote_spanned! { span =>
                ( #( #[prusti::spec_only] | #args | ( #set ), )* ) })
            .collect::<Vec<_>>();
        match self {
            Self::Forall => quote_spanned! { span => forall(
                ( #( #trigger_sets, )* ),
                #[prusti::spec_only] | #args | -> bool { ((#body): bool) }
            ) },
            Self::Exists => quote_spanned! { span => exists(
                ( #( #trigger_sets, )* ),
                #[prusti::spec_only] | #args | -> bool { ((#body): bool) }
            ) },
        }
    }
}

// For Prusti-specific operators, in both [operator2] and [operator3]
// we only care about the spacing of the last [Punct], as this lets us
// know that the last character is not itself part of an actual Rust
// operator.
//
// "==>" will never have the "expected" spacing of [Joint, Joint, Alone]
// because "==" and ">" are Rust operators, but "==>" is not.
//
// If [all_spacing] is enabled, we care about the spacing of all three
// [Punct] characters, since we are parsing a Rust operator.
fn operator2(
    op: &str,
    p1: &Punct,
    p2: &Punct,
    all_spacing: bool,
) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    &[p1.as_char(), p2.as_char()] == &chars[0..2]
        && (!all_spacing || p1.spacing() == Joint)
        && p2.spacing() == Alone
}

fn operator3(
    op: &str,
    p1: &Punct,
    p2: &Punct,
    p3: &Punct,
    all_spacing: bool,
) -> bool {
    let chars = op.chars().collect::<Vec<_>>();
    [p1.as_char(), p2.as_char(), p3.as_char()] == &chars[0..3]
        && (!all_spacing || (p1.spacing() == Joint && p2.spacing() == Joint))
        && p3.spacing() == Alone
}

impl PrustiToken {
    fn is_closure_brace(&self) -> bool {
        matches!(self, Self::Token(TokenTree::Punct(p))
            if p.as_char() == '|' && p.spacing() == proc_macro2::Spacing::Alone)
    }

    fn parse_op2(
        p1: &Punct,
        p2: &Punct,
    ) -> Option<Self> {
        let span = p1.span().join(p2.span()).unwrap();
        Some(Self::BinOp(span, if operator2("&&", p1, p2, true) {
            PrustiBinaryOp::And
        } else if operator2("||", p1, p2, true) {
            PrustiBinaryOp::Or
        } else if operator2("..", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::Range)
        } else if operator2("+=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::AddAssign)
        } else if operator2("-=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::SubtractAssign)
        } else if operator2("*=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::MultiplyAssign)
        } else if operator2("/=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::DivideAssign)
        } else if operator2("%=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::ModuloAssign)
        } else if operator2("&=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::BitAndAssign)
        //} else if operator2("|=", p1, p2, true) {
        //    PrustiBinaryOp::Rust(RustOp::BitOrAssign)
        } else if operator2("^=", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::BitXorAssign)
        } else if operator2("=>", p1, p2, true) {
            PrustiBinaryOp::Rust(RustOp::Arrow)
        } else if operator2("|=", p1, p2, true) {
            return Some(Self::SpecEnt(span, false));
        } else if operator2("~>", p1, p2, false) {
            return Some(Self::CallDesc(span, false));
        } else {
            return None;
        }))
    }

    fn parse_op3(
        p1: &Punct,
        p2: &Punct,
        p3: &Punct,
    ) -> Option<Self> {
        let span = p1.span().join(p2.span()).unwrap().join(p3.span()).unwrap();
        Some(Self::BinOp(span, if operator3("==>", p1, p2, p3, false) {
            PrustiBinaryOp::Implies
        } else if operator3("===", p1, p2, p3, false) {
            PrustiBinaryOp::SnapEq
        } else if operator3("..=", p1, p2, p3, true) {
            PrustiBinaryOp::Rust(RustOp::RangeInclusive)
        } else if operator3("<<=", p1, p2, p3, true) {
            PrustiBinaryOp::Rust(RustOp::LeftShiftAssign)
        } else if operator3(">>=", p1, p2, p3, true) {
            PrustiBinaryOp::Rust(RustOp::RightShiftAssign)
        } else if operator3("|=!", p1, p2, p3, false) {
            return Some(Self::SpecEnt(span, true));
        } else if operator3("~>!", p1, p2, p3, false) {
            return Some(Self::CallDesc(span, true));
        } else {
            return None;
        }))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrustiBinaryOp {
    Rust(RustOp),
    Implies,
    Or,
    And,
    SnapEq,
}

impl PrustiBinaryOp {
    fn binding_power(&self) -> (u8, u8) {
        match self {
            // TODO: explain
            Self::Rust(_) => (0, 0),
            Self::Implies => (4, 3),
            Self::Or => (5, 6),
            Self::And => (7, 8),
            Self::SnapEq => (9, 10),
        }
    }

    fn translate(
        &self,
        span: Span,
        lhs: TokenStream,
        rhs: TokenStream,
    ) -> TokenStream {
        match self {
            Self::Rust(op) => op.translate(span, lhs, rhs),
            Self::Implies => quote_spanned! { span => implication(#lhs, #rhs) },
            Self::Or => quote_spanned! { span => #lhs || #rhs },
            Self::And => quote_spanned! { span => #lhs && #rhs },
            Self::SnapEq => quote_spanned! { span => snapshot_equality(#lhs, #rhs) },
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RustOp {
    RangeInclusive,
    LeftShiftAssign,
    RightShiftAssign,
    Range,
    AddAssign,
    SubtractAssign,
    MultiplyAssign,
    DivideAssign,
    ModuloAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    Arrow,
    Comma,
    Semicolon,
    Assign,
}

impl RustOp {
    fn translate(
        &self,
        span: Span,
        lhs: TokenStream,
        rhs: TokenStream,
    ) -> TokenStream {
        match self {
            Self::RangeInclusive => quote_spanned! { span => #lhs ..= #rhs },
            Self::LeftShiftAssign => quote_spanned! { span => #lhs <<= #rhs },
            Self::RightShiftAssign => quote_spanned! { span => #lhs >>= #rhs },
            Self::Range => quote_spanned! { span => #lhs .. #rhs },
            Self::AddAssign => quote_spanned! { span => #lhs += #rhs },
            Self::SubtractAssign => quote_spanned! { span => #lhs -= #rhs },
            Self::MultiplyAssign => quote_spanned! { span => #lhs *= #rhs },
            Self::DivideAssign => quote_spanned! { span => #lhs /= #rhs },
            Self::ModuloAssign => quote_spanned! { span => #lhs %= #rhs },
            Self::BitAndAssign => quote_spanned! { span => #lhs &= #rhs },
            Self::BitOrAssign => quote_spanned! { span => #lhs |= #rhs },
            Self::BitXorAssign => quote_spanned! { span => #lhs ^= #rhs },
            Self::Arrow => quote_spanned! { span => #lhs => #rhs },
            Self::Comma => quote_spanned! { span => #lhs , #rhs },
            Self::Semicolon => quote_spanned! { span => #lhs ; #rhs },
            Self::Assign => quote_spanned! { span => #lhs = #rhs },
        }
    }
}

#[test]
fn test_preparser() {
    use quote::quote;/*
    assert_eq!(
        parse_prusti(quote! { a ==> b }).unwrap().to_string(),
        "implication (a , b)",
    );
    assert_eq!(
        parse_prusti(quote! { a ==> b ==> c }).unwrap().to_string(),
        "implication (a , implication (b , c))",
    );
    assert_eq!(
        parse_prusti(quote! { (a ==> b && c) ==> d || e }).unwrap().to_string(),
        "implication ((implication (a , b && c)) , d || e)",
    );
    assert_eq!(
        parse_prusti(quote! { forall(|x: i32| a ==> b) }).unwrap().to_string(),
        "forall (() , | x : i32 | -> bool { ((implication (a , b)) : bool) })",
    );
    assert_eq!(
        parse_prusti(quote! { exists(|x: i32| a === b) }).unwrap().to_string(),
        "exists (() , | x : i32 | -> bool { ((snapshot_equality (a , b)) : bool) })",
    );
    assert_eq!(
        parse_prusti(quote! { forall(|x: i32| a ==> b, triggers = [(c,), (d, e)]) }).unwrap().to_string(),
        "forall ((| x : i32 | { (c ,) ; } , | x : i32 | { (d , e) ; }) , | x : i32 | -> bool { ((implication (a , b)) : bool) })",
    );
*/
    assert_eq!(
        parse_prusti(quote! { f |= |i: i32| [ requires(i >= 5), ensures(cl_result >= 6) ] }).unwrap().to_string(),
        "",
    );
}
