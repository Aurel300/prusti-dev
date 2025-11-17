use prusti_contracts::*;

#[ensures(Real::from_f32(x) == Real::from_f32(result))]
pub fn foo(x: f32) -> f32 {
    x
}

#[requires(!x.is_nan())]
#[requires(x >= 1.0)]
#[requires(!x.is_infinite())]
#[ensures((Real::from_f64(result) - Real::from_f64(2.0) * Real::from_f64(x) <= Real::from_f64(0.00001)) || (Real::from_f64(2.0) * Real::from_f64(x) - Real::from_f64(result) <= Real::from_f64(0.00001)))]
pub fn foo2(x: f64) -> f64 {
    2.0 * x
}

#[requires(!x.is_nan())]
#[requires(!f32_is_infinite(x))]
#[requires(!y.is_nan())]
#[requires(!f32_is_infinite(y))]
#[ensures(((Real::from_f32(x) - Real::from_f32(y)) - Real::from_f32(result) <= Real::from_f64(0.00001)) || (Real::from_f32(result) - (Real::from_f32(x) - Real::from_f32(y)) <= Real::from_f64(0.00001)))]
pub fn foo3(x: f32, y: f32) -> f32 {
    x - y
}

#[ensures(Real::from_f32(1.0) <= Real::from_f32(2.0))]
pub fn foo4(){}

#[ensures(Real::from_f32(0.0) == Real::from_f32(-0.0))]
pub fn foo5(){}

#[ensures(Real::from_f32(2.5) > Real::from_f32(2.0))]
pub fn foo6(){}