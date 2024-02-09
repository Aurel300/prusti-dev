use rustc_hash::FxHashMap;
use viper::{self, AstFactory};

/// Context for conversion of VIR nodes to Viper AST. We need to keep track of
/// domain information in particular, since domain function application nodes
/// must be created with information that we do not store in the VIR.
#[derive(Default)]
pub struct ToViperContext<'vir> {
    /// Map of all domains in the program, keyed by name.
    domains: FxHashMap<&'vir str, vir::Domain<'vir>>,

    /// Map of all domain functions in the program, keyed by name.
    domain_functions: FxHashMap<&'vir str, (vir::Domain<'vir>, vir::DomainFunction<'vir>)>,
}

/// Conversion of one VIR node into one Viper AST node.
pub trait ToViper<'vir, 'v> {
    /// Type of the created Viper AST node.
    type Output;

    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output;
}

/// Conversion of one VIR node into a vector of Viper AST nodes.
pub trait ToViperVec<'vir, 'v> {
    /// Type of a single created Viper AST node.
    type Output;

    /// Extend the given vector with the converted contents of `self`.
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>);

    /// Indicate how many elements there are in `self`. Does not need to be
    /// provided, nor does it need to be accurate; this is only used to set a
    /// capacity for vectors.
    fn size_hint(&self) -> Option<usize> {
        None
    }

    /// Helper method to allocate a vector and extend it with `self`.
    fn to_viper_vec(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Vec<Self::Output> {
        let mut result = match self.size_hint() {
            Some(hint) => Vec::with_capacity(hint),
            None => Vec::new(),
        };
        self.to_viper_extend(&mut result, ctx, ast);
        result
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::AccField<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.field_access_predicate(
            ast.field_access(
                self.recv.to_viper(ctx, ast),
                self.field.to_viper(ctx, ast),
                // TODO: position
            ),
            self.perm.map(|v| v.to_viper(ctx, ast)).unwrap_or_else(|| ast.full_perm()),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::BinOp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        let lhs = self.lhs.to_viper(ctx, ast);
        let rhs = self.rhs.to_viper(ctx, ast);
        // TODO: position
        match self.kind {
            vir::BinOpKind::CmpEq => ast.eq_cmp(lhs, rhs),
            vir::BinOpKind::CmpNe => ast.ne_cmp(lhs, rhs),
            vir::BinOpKind::CmpGt => ast.gt_cmp(lhs, rhs),
            vir::BinOpKind::CmpLt => ast.lt_cmp(lhs, rhs),
            vir::BinOpKind::CmpGe => ast.ge_cmp(lhs, rhs),
            vir::BinOpKind::CmpLe => ast.le_cmp(lhs, rhs),
            vir::BinOpKind::And => ast.and(lhs, rhs),
            vir::BinOpKind::Or => ast.or(lhs, rhs),
            vir::BinOpKind::Add => ast.add(lhs, rhs),
            vir::BinOpKind::Sub => ast.sub(lhs, rhs),
            vir::BinOpKind::Mod => ast.mul(lhs, rhs),
        }
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::CfgBlock<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        Some(1 + self.stmts.len() + self.terminator.size_hint().unwrap_or(1))
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) {
        vec.push(self.label.to_viper(ctx, ast));
        vec.extend(self.stmts.iter().map(|v| v.to_viper(ctx, ast)));
        self.terminator.to_viper_extend(vec, ctx, ast);
    }
}

fn label_name<'vir>(label: vir::CfgBlockLabel<'vir>) -> String {
    match label {
        vir::CfgBlockLabelData::Start => "start".to_string(),
        vir::CfgBlockLabelData::End => "end".to_string(),
        vir::CfgBlockLabelData::BasicBlock(idx) => format!("bb_{idx}"),
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::CfgBlockLabel<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, _ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.label(
            &label_name(self),
            &[], // TODO: invariants
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Const<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, _ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        // TODO: position
        match self {
            vir::ConstData::Bool(true) => ast.true_lit(),
            vir::ConstData::Bool(false) => ast.false_lit(),
            vir::ConstData::Int(v) if *v < (i64::MAX as u128) => ast.int_lit(*v as i64),
            vir::ConstData::Int(v) => ast.int_lit_from_ref(v),
            vir::ConstData::Wildcard => ast.wildcard_perm(),
            vir::ConstData::Null => ast.null_lit(),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Domain<'vir> {
    type Output = viper::Domain<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.domain(
            self.name,
            &self.functions.iter().map(|v| (self.name, *v).to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.axioms.iter().map(|v| (self.name, *v).to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.typarams.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for (&'vir str, vir::DomainAxiom<'vir>) {
    type Output = viper::NamedDomainAxiom<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.named_domain_axiom(
            self.1.name,
            self.1.expr.to_viper(ctx, ast),
            self.0,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for (&'vir str, vir::DomainFunction<'vir>) {
    type Output = viper::DomainFunc<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.domain_func(
            self.1.name,
            &self.1.args.iter().enumerate().map(|(idx, v)| ast.local_var_decl(
                &format!("arg{idx}"),
                v.to_viper(ctx, ast),
            )).collect::<Vec<_>>(),
            self.1.ret.to_viper(ctx, ast),
            self.1.unique,
            self.0,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainParam<'vir> {
    type Output = viper::Type<'v>;
    fn to_viper(&self, _ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.type_var(
            self.name,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Expr<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        match self.kind {
            vir::ExprKindData::AccField(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::BinOp(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Const(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Field(recv, field) => ast.field_access(
                recv.to_viper(ctx, ast),
                field.to_viper(ctx, ast),
                // TODO: position
            ),
            vir::ExprKindData::Forall(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::FuncApp(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Let(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Local(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Old(v) => ast.old(v.to_viper(ctx, ast)), // TODO: position
            vir::ExprKindData::PredicateApp(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Result(ty) => ast.result_with_pos(
                ty.to_viper(ctx, ast),
                ast.no_position(), // TODO: position
            ),
            vir::ExprKindData::Ternary(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::Unfolding(v) => v.to_viper(ctx, ast),
            vir::ExprKindData::UnOp(v) => v.to_viper(ctx, ast),

            //vir::ExprKindData::Lazy(&'vir str, Box<dyn for <'a> Fn(&'vir crate::VirCtxt<'a>, Curr) -> Next + 'vir>),
            //vir::ExprKindData::Todo(&'vir str) => unreachable!(),

            _ => unimplemented!(),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Field<'vir> {
    type Output = viper::Field<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.field(
            self.name,
            self.ty.to_viper(ctx, ast),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Forall<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.forall(
            &self.qvars.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.triggers.iter().map(|v| ast.trigger(
                &v.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
                // TODO: position
            )).collect::<Vec<_>>(),
            self.body.to_viper(ctx, ast),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::FuncApp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        if let Some((domain, domain_function)) = ctx.domain_functions.get(self.target) {
            // TODO: func apps should contain the ident
            let ident = vir::FunctionIdent::new(
                domain_function.name,
                vir::UnknownArityAny::new(domain_function.args),
                domain_function.ret,
            );
            use vir::{CallableIdent, CheckTypes};
            let tymap = ident.arity().check_types(domain_function.name, self.args);

            let mut domain_tymap: FxHashMap<_, _> = Default::default();
            for typaram in domain.typarams {
                domain_tymap.insert(typaram.name, ast.type_var(typaram.name));
            }
            for (typaram, ty) in tymap {
                domain_tymap.insert(typaram, ty.to_viper(ctx, ast));
            }
            let mut domain_tymap_vec = domain_tymap.into_iter().collect::<Vec<_>>();
            domain_tymap_vec.sort_by_key(|(k, _)| *k);
            let domain_tymap_vec = domain_tymap_vec.into_iter()
                .map(|(k, v)| (ast.type_var(k), v))
                .collect::<Vec<_>>();

            ast.domain_func_app2(
                self.target,
                &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
                &domain_tymap_vec,
                self.result_ty.to_viper(ctx, ast),
                domain.name,
                ast.no_position(), // TODO: position
            )
        } else {
            ast.func_app(
                self.target,
                &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
                self.result_ty.to_viper(ctx, ast),
                ast.no_position(), // TODO: position
            )
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Function<'vir> {
    type Output = viper::Function<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.function(
            self.name,
            &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            self.ret.to_viper(ctx, ast),
            &self.pres.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.posts.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            ast.no_position(), // TODO: position
            self.expr.map(|v| v.to_viper(ctx, ast)),
        )
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::GotoIf<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        if self.targets.is_empty() {
            Some(1 + self.otherwise_statements.len())
        } else {
            Some(1)
        }
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) {
        if self.targets.is_empty() {
            self.otherwise_statements.iter()
                .for_each(|v| vec.push(v.to_viper(ctx, ast)));
            vec.push(ast.goto(&label_name(self.otherwise)));
            return;
        }
        let value = self.value.to_viper(ctx, ast);
        vec.push(self.targets.iter()
            .rfold({
                let mut vec_otherwise = Vec::with_capacity(1 + self.otherwise_statements.len());
                self.otherwise_statements.iter()
                    .for_each(|v| vec_otherwise.push(v.to_viper(ctx, ast)));
                vec_otherwise.push(ast.goto(&label_name(self.otherwise)));
                ast.seqn(&vec_otherwise, &[])
            }, |else_, (discr, label, then_statements)| {
                let mut vec_then = Vec::with_capacity(1 + then_statements.len());
                then_statements.iter()
                    .for_each(|v| vec_then.push(v.to_viper(ctx, ast)));
                vec_then.push(ast.goto(&label_name(label)));
                ast.if_stmt(
                    ast.eq_cmp(
                        value,
                        discr.to_viper(ctx, ast),
                    ),
                    ast.seqn(&vec_then, &[]),
                    else_,
                )
            }))
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Let<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.let_expr(
            ast.local_var_decl(
                self.name,
                self.val.ty().to_viper(ctx, ast),
            ),
            self.val.to_viper(ctx, ast),
            self.expr.to_viper(ctx, ast),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::LocalData<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.local_var(
            self.name,
            self.ty.to_viper(ctx, ast),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::LocalDeclData<'vir> {
    type Output = viper::LocalVarDecl<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.local_var_decl(
            self.name,
            self.ty.to_viper(ctx, ast),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Method<'vir> {
    type Output = viper::Method<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.method(
            self.name,
            &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.rets.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.pres.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.posts.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            self.blocks.map(|blocks| {
                let size_hint = blocks.iter().flat_map(|b| b.size_hint()).sum();
                let mut result = if size_hint > 0 {
                    Vec::with_capacity(size_hint)
                } else {
                    Vec::new()
                };
                let mut declarations: Vec<viper::Declaration> = Vec::with_capacity(1 + blocks.len());
                blocks.iter()
                    .for_each(|b| {
                        declarations.push(ast.label(
                            &label_name(b.label),
                            &[],
                        ).into());
                        b.stmts.iter()
                            .for_each(|s| match s {
                                vir::StmtGenData::LocalDecl(decl, _) => declarations.push(decl.to_viper(ctx, ast).into()),
                                _ => (),
                            });
                        b.to_viper_extend(&mut result, ctx, ast);
                    });
                ast.seqn(
                    &result,
                    &declarations,
                )
            }),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::MethodCall<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.method_call_with_pos(
            self.method,
            &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            &self.targets.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            ast.no_position(), // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::PredicateApp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.predicate_access_predicate(
            ast.predicate_access(
                &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
                self.target
            ),
            self.perm.map(|v| v.to_viper(ctx, ast)).unwrap_or_else(|| ast.full_perm()),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Predicate<'vir> {
    type Output = viper::Predicate<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.predicate(
            self.name,
            &self.args.iter().map(|v| v.to_viper(ctx, ast)).collect::<Vec<_>>(),
            self.expr.map(|v| v.to_viper(ctx, ast)),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Program<'vir> {
    type Output = viper::Program<'v>;
    fn to_viper(&self, _ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        let mut domains: FxHashMap<_, _> = Default::default();
        let mut domain_functions: FxHashMap<_, _> = Default::default();
        for domain in self.domains {
            domains.insert(domain.name, *domain);
            for function in domain.functions {
                domain_functions.insert(function.name, (*domain, *function));
            }
        }
        let ctx = ToViperContext {
            domains,
            domain_functions,
        };
        ast.program(
            &self.domains.iter().map(|v| v.to_viper(&ctx, ast)).collect::<Vec<_>>(),
            &self.fields.iter().map(|v| v.to_viper(&ctx, ast)).collect::<Vec<_>>(),
            &self.functions.iter().map(|v| v.to_viper(&ctx, ast)).collect::<Vec<_>>(),
            &self.predicates.iter().map(|v| v.to_viper(&ctx, ast)).collect::<Vec<_>>(),
            &self.methods.iter().map(|v| v.to_viper(&ctx, ast)).collect::<Vec<_>>(),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::PureAssign<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.local_var_assign(
            // TODO: this won't work, maybe abstract assign?
            self.lhs.to_viper(ctx, ast),
            self.rhs.to_viper(ctx, ast),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Stmt<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        match self {
            vir::StmtGenData::Comment(v) => ast.comment(v),
            vir::StmtGenData::Exhale(v) => ast.exhale(
                v.to_viper(ctx, ast),
                ast.no_position(), // TODO: position
            ),
            vir::StmtGenData::Fold(pred) => ast.fold(
                pred.to_viper(ctx, ast),
                // TODO: position
            ),
            vir::StmtGenData::Inhale(v) => ast.inhale(
                v.to_viper(ctx, ast),
                ast.no_position(), // TODO: position
            ),
            vir::StmtGenData::LocalDecl(decl, Some(expr)) => ast.local_var_assign(
                ast.local_var(
                    decl.name,
                    decl.ty.to_viper(ctx, ast),
                    // TODO: position
                ),
                expr.to_viper(ctx, ast),
                // TODO: position
            ),
            vir::StmtGenData::LocalDecl(decl, None) => ast.comment(&format!("var {}", decl.name)),
            vir::StmtGenData::MethodCall(v) => v.to_viper(ctx, ast),
            vir::StmtGenData::PureAssign(v) => v.to_viper(ctx, ast),
            vir::StmtGenData::Unfold(pred) => ast.unfold(
                pred.to_viper(ctx, ast),
                // TODO: position
            ),
            //vir::StmtGenData::Dummy(#[reify_copy] &'vir str),
            _ => unimplemented!(),
        }
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::TerminatorStmt<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        if let vir::TerminatorStmtGenData::GotoIf(v) = self {
            v.size_hint()
        } else {
            Some(1)
        }
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) {
        match self {
            vir::TerminatorStmtGenData::AssumeFalse => vec.push(ast.inhale(
                ast.false_lit(), // TODO: position
                ast.no_position(), // TODO: position
            )),
            vir::TerminatorStmtGenData::Goto(label) => vec.push(ast.goto(&label_name(label))),
            vir::TerminatorStmtGenData::GotoIf(v) => v.to_viper_extend(vec, ctx, ast),
            vir::TerminatorStmtGenData::Exit => vec.push(ast.comment("return")),
            vir::TerminatorStmtGenData::Dummy(v) => vec.push(ast.seqn(
                &[
                    ast.comment(v),
                    ast.inhale(
                        ast.false_lit(), // TODO: position
                        ast.no_position(), // TODO: position
                    ),
                ],
                &[],
            )),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Ternary<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        ast.cond_exp(
            self.cond.to_viper(ctx, ast),
            self.then.to_viper(ctx, ast),
            self.else_.to_viper(ctx, ast),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Type<'vir> {
    type Output = viper::Type<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        match self {
            vir::TypeData::Int => ast.int_type(),
            vir::TypeData::Bool => ast.bool_type(),
            vir::TypeData::DomainTypeParam(param) => ast.type_var(param.name),
            vir::TypeData::Domain(name, params) => {
                let domain = ctx.domains.get(name).unwrap();
                ast.domain_type(
                    name,
                    &domain.typarams.iter()
                        .zip(params.iter())
                        .map(|(domain_param, actual)| (ast.type_var(domain_param.name), actual.to_viper(ctx, ast)))
                        .collect::<Vec<_>>(),
                    &domain.typarams.iter()
                        .map(|v| ast.type_var(v.name))
                        .collect::<Vec<_>>(),
                )
            }
            vir::TypeData::Ref => ast.ref_type(),
            vir::TypeData::Perm => ast.perm_type(),
            //vir::TypeData::Predicate, // The type of a predicate application
            //vir::TypeData::Unsupported(UnsupportedType<'vir>)
            _ => unimplemented!(),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::UnOp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        let expr = self.expr.to_viper(ctx, ast);
        // TODO: position
        match self.kind {
            vir::UnOpKind::Neg => ast.minus(expr),
            vir::UnOpKind::Not => ast.not(expr),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Unfolding<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir>, ast: &AstFactory<'v>) -> Self::Output {
        // TODO: position
        ast.unfolding(
            self.target.to_viper(ctx, ast),
            self.expr.to_viper(ctx, ast),
        )
    }
}

