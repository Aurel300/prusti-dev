#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

enum List {
    Cons(u32, Box<List>),
    Nil(),
}

#[pure]
#[ensures(result >= 0)]
fn len(head: &List) -> usize {
    match *head {
        List::Nil() => 0,
        List::Cons(car, box ref cdr) => 1 + len(cdr),
    }
}

fn pick_unpick() {
    let xs0 = List::Nil();
    let before = len(&xs0);

    let xs1 = List::Cons(1, Box::new(xs0));
    let xs2 = List::Cons(2, Box::new(xs1));
    let xs3 = List::Cons(3, Box::new(xs2));

    let after = len(&xs3);
    assert!(after == before + 3);

    let xs4 = if let List::Cons(_, cdr) = xs3 { *cdr } else { panic!() };
    let xs5 = if let List::Cons(_, cdr) = xs4 { *cdr } else { panic!() };
    let xs6 = if let List::Cons(_, cdr) = xs5 { *cdr } else { panic!() };
    
    let finally = len(&xs6);
    assert!(finally == before);
}

fn main() {}
