#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

enum List {
    Cons(u32, Box<List>),
    Nil(),
}

#[pure]
fn len(head: &List) -> usize {
    match *head {
        List::Nil() => 0,
        List::Cons(car, box ref cdr) => 1 + len(cdr),
    }
}

// Thanks to the generated `trig` annotations, the impure
// encoding of this function will verify. Meanwhile, the
// pure encoding will fail to verify unless the `Spec`
// axiom is correctly generated
#[pure]
#[ensures(result == len(head) + 1)]
fn len_2(head: &List) -> usize {
    match *head {
        List::Nil() => 0,
        List::Cons(car, box ref cdr) => {
            match *cdr {
                List::Nil() => 1,
                List::Cons(car0, box ref cdr0) => {
                    2 + len_2(cdr0)
                }
            }
        },
    }
}

#[requires(len_2(xs) > 0)]
fn f(xs: &List) {}