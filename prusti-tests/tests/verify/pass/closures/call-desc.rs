use prusti_contracts::*;

struct BoxNum {
    x: i32,
}

#[requires(f |= |x: i32| [ requires(true) ])]
#[ensures(
    f ~>! |x: i32|
        { x == slf.x }
        { cl_result == result.x }
)]
fn map<F: FnOnce(i32) -> i32>(slf: BoxNum, f: F) -> BoxNum {
    BoxNum {
        x: f(slf.x),
    }
}

#[requires(f |=! || [ requires(true), ensures(cl_result == 42) ])]
#[ensures(f ~> || {} { cl_result == 42 })]
#[ensures(result == 42)]
fn call_no_args<F: FnOnce() -> i32>(f: F) -> i32 {
    f()
}

#[requires(f |= |x: i32| [ requires(x == 5), ensures(cl_result == 0) ])]
#[ensures(f ~>! |x: i32| { x == 5 } { cl_result == 0 })]
fn call_const<F: FnMut(i32) -> i32>(mut f: F) {
    f(5);
}

fn main() {
    call_no_args(closure!(
        #[requires(true)]
        #[ensures(result == 42)]
        || -> i32 { 42 }
    ));

    call_const(closure!(
        #[requires(x > 0)]
        #[ensures(result == 0)]
        |x: i32| -> i32 { 0 }
    ));

    assert!(map(
        BoxNum { x: 5 },
        closure!(
            #[requires(true)]
            #[ensures(result == x * 2)]
            |x: i32| -> i32 { x * 2 }
        ),
    ).x == 10);
}
