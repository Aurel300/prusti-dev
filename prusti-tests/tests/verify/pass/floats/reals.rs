use prusti_contracts::*;

#[ensures(Real::from_f32(x) == Real::from_f32(result))]
pub fn foo(x: f32) -> f32 {
    x
}

#[requires(!x.is_nan())]
#[requires(x >= 1.0 && x <= 100.0)]
#[ensures(Real::from_f64(2.0) * Real::from_f64(x) - Real::from_f64(result) <= Real::from_f64(0.1))]
#[ensures(-Real::from_f64(0.1) <= Real::from_f64(2.0) * Real::from_f64(x) - Real::from_f64(result))]
pub fn foo2(x: f64) -> f64 {
    x + x
}

#[requires(!x.is_nan())]
#[requires(!f32_is_infinite(x))]
#[requires(!y.is_nan())]
#[requires(y != f32::INFINITY && y != -f32::INFINITY)]
#[ensures((Real::from_f32(x) - Real::from_f32(y)) - Real::from_f32(result) <= Real::from_f32(0.1))]
#[ensures(-Real::from_f32(0.1) <= (Real::from_f32(x) - Real::from_f32(y)) - Real::from_f32(result))]
pub fn foo3(x: f32, y: f32) -> f32 {
    x - y
}

#[ensures(Real::from_f32(1.0) <= Real::from_f32(2.0))]
pub fn foo4(){}

#[ensures(Real::from_f32(0.0) == Real::from_f32(-0.0))]
pub fn foo5(){}

#[ensures(Real::from_f32(2.5) > Real::from_f32(2.0))]
pub fn foo6(){}

#[ensures(Real::from_f32(8.5) / Real::from_f32(2.0) == Real::from_f32(4.25))]
pub fn foo7(){}

#[ensures(-Real::from_f32(8.5) == Real::from_f32(-8.5))]
pub fn foo8(){}