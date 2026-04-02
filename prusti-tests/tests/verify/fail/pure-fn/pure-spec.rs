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

// Thanks to the generated `trig` annotations, the impure
// encoding of this function will verify. Meanwhile, the
// pure encoding will fail to verify on its own.
#[pure]
#[ensures(result == len(head))]
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