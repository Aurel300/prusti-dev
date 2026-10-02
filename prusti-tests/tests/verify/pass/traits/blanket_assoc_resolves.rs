// A blanket impl's associated types and method specifications are assumed
// only where the impl's where-clauses hold (see
// `verify/fail/traits/blanket_*.rs`). These check that they still resolve
// where the bounds do hold: for concrete types, and for generic code whose
// own where-clauses provide them.

use prusti_contracts::*;
use std::convert::{Infallible, TryFrom};

// `impl<T, U: Into<T>> TryFrom<U> for T` with `Error = Infallible`.
pub fn try_from_same(x: u8) -> u8 {
    let r: Result<u8, Infallible> = u8::try_from(x);
    match r {
        Ok(v) => v,
        Err(e) => match e {},
    }
}

pub fn try_from_generic<T, U: Into<T>>(u: U) -> T {
    match T::try_from(u) {
        Ok(t) => t,
        Err(e) => match e {},
    }
}

pub trait MyBound {}
pub trait Tr<U> {
    type Out;
    #[pure]
    fn make(&self, u: U) -> Self::Out;
}

pub struct S;
#[derive(Clone, Copy)]
pub struct Z(pub u32);

impl MyBound for Z {}

#[refine_trait_spec]
impl<U: MyBound + Copy> Tr<U> for S {
    type Out = U;
    #[pure]
    fn make(&self, u: U) -> U {
        u
    }
}

#[pure]
pub fn via<T: Tr<V>, V>(t: &T, v: V) -> T::Out {
    t.make(v)
}

// `<S as Tr<Z>>::Out == Z` and the impl's `make` spec, at a concrete type.
pub fn concrete_user(z: Z) {
    let o: Z = via(&S, z);
    prusti_assert!(o.0 == z.0);
}

// The same, where `V: MyBound + Copy` is only known from the where-clause.
#[pure]
#[ensures(result === v)]
pub fn generic_user<V: MyBound + Copy>(v: V) -> V {
    via(&S, v)
}

// `impl<I: Iterator> IntoIterator for I`: `IntoIter == I`.
pub fn into_iter_is_identity<I: Iterator<Item = u32>>(i: I) -> I {
    i.into_iter()
}

// The behavioural-subtyping check of an impl assumes the impl's
// where-clauses: `via(&self.0) == 7` needs `T: Copy`.
mod subtyping_check_bounds {
    use prusti_contracts::*;

    pub trait Seven {
        #[pure]
        fn seven(&self) -> u32;
    }
    #[refine_trait_spec]
    impl<T: Copy> Seven for T {
        #[pure]
        #[ensures(result == 7)]
        fn seven(&self) -> u32 {
            7
        }
    }

    #[pure]
    pub fn via<T: Seven>(t: &T) -> u32 {
        t.seven()
    }

    pub trait Tr {
        #[ensures(result == 7)]
        fn f(&self) -> u32;
    }
    pub struct W<T>(pub T);
    #[refine_trait_spec]
    impl<T: Copy> Tr for W<T> {
        #[ensures(result == via(&self.0))]
        fn f(&self) -> u32 {
            via(&self.0)
        }
    }
}

// An impl parameter fixed only by a closure bound's output (`U`, as in
// itertools' `MapSpecialCaseFnOk`) that occurs in an item's signature, and so
// in the trigger of the item's axioms.
mod fn_output_param {
    use prusti_contracts::*;

    pub trait MapFn<T> {
        type Out;
        fn call(&mut self, t: T) -> Self::Out;
    }

    pub struct MapOk<F>(pub F);

    #[refine_trait_spec]
    impl<F, T, U, E> MapFn<Result<T, E>> for MapOk<F>
    where
        F: FnMut(T) -> U,
    {
        type Out = Result<U, E>;
        #[trusted]
        fn call(&mut self, t: Result<T, E>) -> Result<U, E> {
            t.map(&mut self.0)
        }
    }

    pub fn go<M: MapFn<Result<u8, ()>>>(m: &mut M, t: Result<u8, ()>) -> M::Out {
        m.call(t)
    }

    pub fn user<F: FnMut(u8) -> u16>(m: &mut MapOk<F>) -> Result<u16, ()> {
        go(m, Ok(1))
    }
}

// An impl forwarding to a projection of its own parameter (as rand_core's
// `TryRng` for `R: DerefMut`): its axioms apply `TryRng` to `R::Target`, and
// resolve where that projection occurs, without feeding themselves.
mod forward_to_projection {
    use prusti_contracts::*;
    use std::ops::DerefMut;

    pub trait TryRng {
        type Error;
        fn try_next(&mut self) -> Result<u32, Self::Error>;
    }

    #[refine_trait_spec]
    impl<R: DerefMut> TryRng for R
    where
        R::Target: TryRng,
    {
        type Error = <R::Target as TryRng>::Error;
        #[trusted]
        fn try_next(&mut self) -> Result<u32, Self::Error> {
            self.deref_mut().try_next()
        }
    }

    pub fn take<R: TryRng>(r: &mut R) -> Result<u32, R::Error> {
        r.try_next()
    }

    pub fn forward<R: DerefMut>(r: &mut R) -> Result<u32, <R::Target as TryRng>::Error>
    where
        R::Target: TryRng,
    {
        take(r)
    }
}

// A where-clause on a projection that cannot feed the impl's own trigger
// (`Clone` of `G::Output` under the trigger at `BlockRng<G>`, as
// `#[derive(Clone)]` generates it) keeps the trigger as it is, so the impl
// applies where the projection does not occur yet.
mod projection_bound {
    use prusti_contracts::*;

    pub trait Generator {
        type Output;
    }

    pub struct BlockRng<G: Generator> {
        pub core: G,
    }

    #[refine_trait_spec]
    impl<G: Generator + Clone> Clone for BlockRng<G>
    where
        G::Output: Clone,
    {
        #[trusted]
        fn clone(&self) -> Self {
            BlockRng { core: self.core.clone() }
        }
    }

    #[derive(Clone)]
    pub struct MyGen<T>(pub T);
    impl<T> Generator for MyGen<T> {
        type Output = T;
    }

    pub struct Wrap<T>(pub T);
    pub trait Tr {
        type A;
    }
    impl<T: Clone> Tr for Wrap<T> {
        type A = u8;
    }

    pub fn get<T: Tr>(_t: &T) -> Option<T::A> {
        None
    }

    pub fn user(w: &Wrap<BlockRng<MyGen<u32>>>) -> Option<u8> {
        get(w)
    }
}
