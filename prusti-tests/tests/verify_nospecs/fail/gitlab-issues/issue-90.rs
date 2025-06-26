/*use prusti_contracts::*;*/

/*#[requires(x > 0)]*/
fn foo(x: i32) {
    // nothing
}

fn test() {
    let x = -1;
    foo(x); // ERRXR: precondition
}

fn main() {}
