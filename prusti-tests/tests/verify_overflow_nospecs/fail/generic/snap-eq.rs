/*use prusti_contracts::*;*/

/*#[requires(a === b)]*/
fn foo<T>(a: T, b: T) {}

struct X { a: i32 }

fn test1() {
    foo(4, 5); // ERRXR: precondition might not hold
}

fn test2() {
    foo(false, true); // ERRXR: precondition might not hold
}

fn test3() {
    foo((1, 1), (1, 2)); // ERRXR: precondition might not hold
}

fn test4() {
    foo(X { a: 2 }, X { a: 1 }); // ERRXR: precondition might not hold
}

/*#[trusted]*/
fn main() {}
