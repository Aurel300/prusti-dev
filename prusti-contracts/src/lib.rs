extern crate proc_macro;

#[cfg(not(feature = "prusti"))]
mod private {
    /// A macro for writing a precondition on a function.
    pub use prusti_contracts_impl::requires;

    /// A macro for writing a postcondition on a function.
    pub use prusti_contracts_impl::ensures;

    /// A macro for writing a pledge on a function.
    pub use prusti_contracts_impl::after_expiry;

    /// A macro for writing a conditional pledge on a function.
    pub use prusti_contracts_impl::after_expiry_if;

    /// A macro for marking a function as pure.
    pub use prusti_contracts_impl::pure;

    /// A macro for marking a function as trusted.
    pub use prusti_contracts_impl::trusted;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_impl::body_invariant;

    /// A macro for defining a closure with a specification.
    pub use prusti_contracts_impl::closure;

    /// A macro for specifying external functions.
    pub use prusti_contracts_impl::extern_spec;
}

#[cfg(feature = "prusti")]
mod private {
    /// A macro for writing a precondition on a function.
    pub use prusti_contracts_internal::requires;

    /// A macro for writing a postcondition on a function.
    pub use prusti_contracts_internal::ensures;

    /// A macro for writing a pledge on a function.
    pub use prusti_contracts_internal::after_expiry;

    /// A macro for writing a conditional pledge on a function.
    pub use prusti_contracts_internal::after_expiry_if;

    /// A macro for marking a function as pure.
    pub use prusti_contracts_internal::pure;

    /// A macro for marking a function as trusted.
    pub use prusti_contracts_internal::trusted;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_internal::body_invariant;

    /// A macro for defining a closure with a specification.
    pub use prusti_contracts_internal::closure;

    /// A macro for specifying external functions.
    pub use prusti_contracts_internal::extern_spec;

    struct FakeFuture<T> {
        phantom: std::marker::PhantomData<T>
    }

    impl<T> std::future::Future for FakeFuture<T> {
        type Output = T;
        fn poll(self: std::pin::Pin<&mut Self>, _cx: &mut std::task::Context<'_>) -> std::task::Poll<T> {
            // For a simpler implementation, we always return `Pending`. It is
            // not a problem, since fake futures are never actually used.
            std::task::Poll::Pending
        }
    }

    /// A function that mimics the type signature of an async block.
    pub fn fake_async<T, F: Fn() -> T>(_val: F) -> impl std::future::Future<Output = T> {
        FakeFuture {
            phantom: std::marker::PhantomData
        }
    }

    /// A function that mimics the type signature of an .await expression.
    pub fn fake_await<T, F: std::future::Future<Output = T>>(_fut: F) -> T {
        unimplemented!()
    }
}


/// This function is used to evaluate an expression in the context just
/// before the borrows expires.
pub fn before_expiry<T>(arg: T) -> T {
    arg
}

/// This function is used to evaluate an expression in the “old”
/// context, that is at the beginning of the method call.
pub fn old<T>(arg: T) -> T {
    arg
}

pub use private::*;
