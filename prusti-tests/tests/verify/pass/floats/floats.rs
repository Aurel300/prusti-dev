use prusti_contracts::*;

#[ensures(result == f)]
fn foo(f: f32) -> f32 {
    f
}