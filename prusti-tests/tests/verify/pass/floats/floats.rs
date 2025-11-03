use prusti_contracts::*;

#[requires(f == 2.0)]
#[ensures(result == f)]
fn foo(f: f32) -> f32 {
    f
}

#[requires(f == 2.0)]
#[ensures(result == 2.5)]
fn foo2(f: f32) -> f32 {
    f + 0.5
}