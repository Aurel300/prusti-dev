#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

enum List<T> {
    Cons(T, Box<List<T>>),
    Nil(),
}

#[pure]
fn len<T>(head: &List<T>) -> usize {
    match head {
        &List::Nil() => 0,
        &List::Cons(_, box ref cdr) => 1 + len(cdr),
    }
}

// Even though the postcondition of this function may not
// hold, we should *not* be getting verification errors in
// the pure encoding (which will cause Prusti to panic).
// Instead, the impure encoding should raise the proper
// verification error.
#[pure]
#[ensures(result == len(head) + 1)] //~ERROR: postcondition
fn len_2<T>(head: &List<T>) -> usize {
    match head {
        &List::Nil() => 0,
        &List::Cons(_, box ref cdr) => {
            match cdr {
                &List::Nil() => 1,
                &List::Cons(_, box ref cdr0) => {
                    2 + len_2(cdr0)
                }
            }
        },
    }
}

#[requires(len_2(xs) > 0)]
fn f<T>(xs: &List<T>) {}
