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

#[requires(f == 4.5)]
#[ensures(result == 1.5)]
fn foo3(f: f32) -> f32 {
    f % 3.0
}

#[requires(f == 4.25)]
#[ensures(result == 1.25)]
fn foo4(f: f32) -> f32 {
    f % 3.0
}

#[requires(!f32_is_nan(f))]
#[ensures(result == f)]
fn foo5(f: f32) -> f32 {
    f
}

#[requires(!f.is_nan())]
#[ensures(result == f)]
fn foo6(f: f64) -> f64 {
    f
}