use prusti_contracts::*;

#[requires(n >= 0)]
#[requires(f |= |x: i32| [ requires(x >= 0), ensures(cl_result == 42 + x) ])]
#[ensures(f ~>! |x: i32| { x == n } { result == cl_result })]
fn foo<T: FnOnce(i32) -> i32>(f: T, n: i32) -> i32 {
    f(n)
}

fn main() {
    assert!(foo(closure!(
        #[requires(x >= 0)]
        #[ensures(result == 42 + x)]
        |x: i32| -> i32 { 42 + x }
    ), 5) == 47);
}
