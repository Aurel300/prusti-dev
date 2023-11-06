use prusti_interface::environment::EnvBody;
use prusti_rustc_interface::middle::ty;
use std::cell::RefCell;

use crate::{data::*, gendata::*, genrefs::*, refs::*};

/// The VIR context is a data structure used throughout the encoding process.
pub struct VirCtxt<'tcx> {
    /// The arena used for bump allocating all VIR AST data. Anything allocated
    /// in the arena (using [VirCtxt::alloc] or similar) is returned as a
    /// shared reference (with the `'tcx` lifetime). This means that different
    /// parts of the AST can refer to the same node, without the need for
    /// unnecessary cloning.
    pub arena: bumpalo::Bump,

    /// The stack of spans during the encoding process. (TODO)
    pub span_stack: Vec<i32>,
    // TODO: span stack
    // TODO: error positions?
    /// The compiler's typing context. This allows convenient access to most
    /// of the compiler's APIs.
    pub tcx: ty::TyCtxt<'tcx>,

    pub body: RefCell<EnvBody<'tcx>>,
}

impl<'tcx> VirCtxt<'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, body: EnvBody<'tcx>) -> Self {
        Self {
            arena: bumpalo::Bump::new(),
            span_stack: vec![],
            tcx,
            body: RefCell::new(body),
        }
    }

    /// Moves `val` into the arena and returns a shared reference to the data.
    pub fn alloc<T>(&self, val: T) -> &T {
        &*self.arena.alloc(val)
    }

    pub fn alloc_str(&self, val: &str) -> &str {
        &*self.arena.alloc_str(val)
    }

    /*    pub fn alloc_slice<'a, T: Copy>(&'tcx self, val: &'a [T]) -> &'tcx [T] {
    &*self.arena.alloc_slice_copy(val)
    }*/
    pub fn alloc_slice<T: Copy>(&self, val: &[T]) -> &[T] {
        &*self.arena.alloc_slice_copy(val)
    }

    pub fn mk_local<'vir>(&'vir self, name: &'vir str) -> Local<'vir> {
        self.alloc(LocalData { name })
    }
    pub fn mk_local_decl(&'tcx self, name: &'tcx str, ty: Type<'tcx>) -> LocalDecl<'tcx> {
        self.alloc(LocalDeclData { name, ty })
    }
    pub fn mk_local_ex_local<Curr, Next>(
        &'tcx self,
        local: Local<'tcx>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.arena.alloc(ExprGenData::Local(local))
    }
    pub fn mk_local_ex<Curr, Next>(&'tcx self, name: &'tcx str) -> ExprGen<'tcx, Curr, Next> {
        self.mk_local_ex_local(self.mk_local(name))
    }
    pub fn mk_func_app<Curr, Next>(
        &'tcx self,
        target: &'tcx str,
        src_args: &[ExprGen<'tcx, Curr, Next>],
    ) -> ExprGen<'tcx, Curr, Next> {
        self.alloc(ExprGenData::FuncApp(self.alloc(FuncAppGenData {
            target,
            args: self.alloc_slice(src_args),
        })))
    }
    pub fn mk_pred_app(&'tcx self, target: &'tcx str, src_args: &[Expr<'tcx>]) -> Expr<'tcx> {
        self.alloc(ExprData::PredicateApp(self.alloc(PredicateAppData {
            target,
            args: self.alloc_slice(src_args),
        })))
    }

    pub fn mk_true(&'tcx self) -> Expr<'tcx> {
        self.mk_const(true.into())
    }

    pub fn mk_false(&'tcx self) -> Expr<'tcx> {
        self.mk_const(false.into())
    }

    pub fn mk_tern<Curr, Next>(
        &'tcx self,
        cond: ExprGen<'tcx, Curr, Next>,
        then: ExprGen<'tcx, Curr, Next>,
        else_: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.alloc(ExprGenData::Ternary(self.alloc(TernaryGenData {
            cond,
            then,
            else_,
        })))
    }

    pub fn mk_bin_op<Curr, Next>(
        &'tcx self,
        kind: BinOpKind,
        lhs: ExprGen<'tcx, Curr, Next>,
        rhs: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.alloc(ExprGenData::BinOp(self.alloc(BinOpGenData {
            kind,
            lhs,
            rhs,
        })))
    }

    pub fn mk_not<Curr, Next>(
        &'tcx self,
        expr: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.alloc(ExprGenData::UnOp(self.alloc(UnOpGenData {
            kind: UnOpKind::Not,
            expr,
        })))
    }

    pub fn mk_impl<Curr, Next>(
        &'tcx self,
        cond: ExprGen<'tcx, Curr, Next>,
        rhs: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.mk_or(self.mk_not(cond), rhs)
    }

    pub fn mk_and<Curr, Next>(
        &'tcx self,
        lhs: ExprGen<'tcx, Curr, Next>,
        rhs: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.mk_bin_op(BinOpKind::And, lhs, rhs)
    }

    pub fn mk_or<Curr, Next>(
        &'tcx self,
        lhs: ExprGen<'tcx, Curr, Next>,
        rhs: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.mk_bin_op(BinOpKind::Or, lhs, rhs)
    }

    pub fn mk_eq<Curr, Next>(
        &'tcx self,
        lhs: ExprGen<'tcx, Curr, Next>,
        rhs: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.mk_bin_op(BinOpKind::CmpEq, lhs, rhs)
    }

    pub fn mk_forall<Curr, Next>(
        &'tcx self,
        qvars: &'tcx [&'tcx LocalDeclData<'tcx>],
        triggers: &'tcx [&'tcx [ExprGen<'tcx, Curr, Next>]],
        body: ExprGen<'tcx, Curr, Next>,
    ) -> ExprGen<'tcx, Curr, Next> {
        self.alloc(ExprGenData::Forall(self.alloc(ForallGenData {
            qvars,
            triggers,
            body,
        })))
    }

    pub fn mk_const<Curr, Next>(&'tcx self, cnst: ConstData) -> ExprGen<'tcx, Curr, Next> {
        self.alloc(ExprGenData::Const(self.alloc(cnst)))
    }

    pub fn mk_conj(&'tcx self, elems: &[Expr<'tcx>]) -> Expr<'tcx> {
        if elems.len() == 0 {
            return self.mk_true();
        }
        let mut e = elems[0];
        for i in 1..elems.len() {
            e = self.mk_and(e, elems[i])
        }
        e
    }
}

thread_local! {
    static VCTX: RefCell<Option<VirCtxt<'static>>> = RefCell::new(None);
}

/// Initialises the VIR context. Should only be called once, when the type
/// context is available.
pub fn init_vcx<'tcx>(vcx: VirCtxt<'tcx>) {
    VCTX.replace(Some(unsafe { std::mem::transmute(vcx) }));
}

/// Perform an action with the VIR context.
pub fn with_vcx<'vir, F, R>(f: F) -> R
where
    F: FnOnce(&'vir VirCtxt<'vir>) -> R,
{
    VCTX.with_borrow(|vcx: &Option<VirCtxt<'static>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let vcx = vcx.as_ref().unwrap();
        let vcx = unsafe { std::mem::transmute(vcx) };
        f(vcx)
    })
}
