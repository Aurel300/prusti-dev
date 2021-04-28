use prusti_contracts::*;

// ignore-test
// TODO: fix spec functions for function pointers

#[requires(add |= |a: i32, b: i32| [
    requires(a >= 0),
    requires(b >= 0),
    ensures(cl_result == a + b)
])]
#[ensures(result == 16)]
fn call_add<F: Fn (i32, i32) -> i32>(add: F) -> i32 {
    add(7, 9)
}

#[requires(a >= 0)]
#[requires(b >= 0)]
#[ensures(result == a + b)]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    call_add(add);
}
