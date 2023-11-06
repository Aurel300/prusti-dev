use crate::{ExprGen, PredicateAppGen, Type, PredicateAppGenData, StmtGenData, MethodCallGenData, VirCtxt};
use private::*;

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdent<'vir, A: Arity>(&'vir str, A);
impl<'vir, T: Arity> FunctionIdent<'vir, T> {
    pub const fn new(name: &'vir str, args: T) -> Self {
        Self(name, args)
    }
    pub fn name(&self) -> &'vir str {
        self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MethodIdent<'vir, A: Arity>(&'vir str, A);
impl<'vir, T: Arity> MethodIdent<'vir, T> {
    pub const fn new(name: &'vir str, args: T) -> Self {
        Self(name, args)
    }
    pub fn name(&self) -> &'vir str {
        self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PredicateIdent<'vir, A: Arity>(&'vir str, A);
impl<'vir, T: Arity> PredicateIdent<'vir, T> {
    pub const fn new(name: &'vir str, args: T) -> Self {
        Self(name, args)
    }
    pub fn name(&self) -> &'vir str {
        self.0
    }
}

/// Module to prevent anyone else from implementing Arity
mod private {
    use super::*;
    pub trait Arity {}
    impl<const N: usize> Arity for KnownArity<'_, N> {}
    impl Arity for UnknownArity<'_> {}
}

#[derive(Debug, Clone, Copy)]
pub struct KnownArity<'vir, const N: usize>([Type<'vir>; N]);
impl<'vir, const N: usize> KnownArity<'vir, N> {
    pub const fn new(types: [Type<'vir>; N]) -> Self {
        Self(types)
    }
}
pub type NullaryArity = KnownArity<'static, 0>;
pub type UnaryArity<'vir> = KnownArity<'vir, 1>;
pub type BinaryArity<'vir> = KnownArity<'vir, 2>;

#[derive(Debug, Clone, Copy)]
pub struct UnknownArity<'vir>(&'vir [Type<'vir>]);
impl<'vir> UnknownArity<'vir> {
    pub const fn new(types: &'vir [Type<'vir>]) -> Self {
        Self(types)
    }
}

// Func arity known at compile time

// TODO: deduplicate all the similar code across the `apply` methods
impl<'vir, const N: usize> FunctionIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> ExprGen<'vir, Curr, Next>{
        vcx.mk_func_app(self.name(), &args)
    }
}
impl<'vir, const N: usize> PredicateIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> PredicateAppGen<'vir, Curr, Next>{
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(&args),
        })
    }
}
impl<'vir, const N: usize> MethodIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> StmtGenData<'vir, Curr, Next>{
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(&args),
        }))
    }
}

// Func arity checked at runtime

impl<'vir> FunctionIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> ExprGen<'vir, Curr, Next>{
        debug_assert_eq!(self.1.0.len(), args.len(), "function {} called with {} args", self.name(), args.len());
        vcx.mk_func_app(self.name(), args)
    }
}
impl<'vir> PredicateIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> PredicateAppGen<'vir, Curr, Next>{
        debug_assert_eq!(self.1.0.len(), args.len(), "predicate {} called with {} args", self.name(), args.len());
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(args),
        })
    }
}
impl<'vir> MethodIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> StmtGenData<'vir, Curr, Next>{
        debug_assert_eq!(self.1.0.len(), args.len(), "method {} called with {} args", self.name(), args.len());
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(args),
        }))
    }
}
