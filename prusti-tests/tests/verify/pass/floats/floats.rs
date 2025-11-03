use prusti_contracts::*;

#[requires(f == 2.0)]
#[ensures(result == f)]
fn foo(f: f32) -> f32 {
    f
}