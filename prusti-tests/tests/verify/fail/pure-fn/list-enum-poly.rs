#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

// use std::borrow::BorrowMut;

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

#[requires(len(&xs3) > 3)]
fn unpick<T>(xs3: List<T>) {
    let before= len(&xs3);

    let xs4 = if let List::Cons(_, cdr) = xs3 { *cdr } else { panic!() };
    let xs5 = if let List::Cons(_, cdr) = xs4 { *cdr } else { panic!() };
    let xs6 = if let List::Cons(_, cdr) = xs5 { *cdr } else { panic!() };
    
    let after = len(&xs6);
    assert!(before == after + 3);
}

fn main() {}
