#![feature(nll)]

/*use prusti_contracts::*;*/

struct T {
    val: i32
}

/*#[ensures(false)]*/ // ERRXR: postcondition
fn identity(x: &mut T) -> &mut T {
    x
}

fn main() {}
