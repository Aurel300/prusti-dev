use prusti_contracts::*;

struct S {
    f: i32
}

#[pure]
#[trusted]
fn pred(s: &S) -> bool {
    unimplemented!()
}

#[pure]
#[trusted]
#[ensures(result === *s)]
fn dup(s: &S) -> S {
    unimplemented!()
}

#[requires(pred(x))]
#[ensures(pred(&result))]
fn test(x: &S) -> S {
    dup(x)
}