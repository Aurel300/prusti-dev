use prusti_contracts::*;

#[ensures(Real::from_f32(x) == Real::from_f32(result))]
pub fn foo(x: f32) -> f32 {
    x
}

#[requires(!x.is_nan())]
#[ensures(Real::from_f32(result) == Real::from_f32(2.0) * Real::from_f32(x))]
pub fn foo2(x: f32) -> f32 {
    x + x
}