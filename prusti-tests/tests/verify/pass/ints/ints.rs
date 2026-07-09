use prusti_contracts::*;

#[ensures(Int::from(x) == Int::from(result))]
pub fn foo16(x: i16) -> i16 {
    x
}

#[ensures(Int::from(x) == Int::from(result))]
pub fn foo32(x: i32) -> i32 {
    x
}

#[ensures(Int::from(x) == Int::from(result))]
pub fn foo64(x: i64) -> i64 {
    x
}

#[ensures(Int::from(x) == Int::from(result))]
pub fn foo128(x: i128) -> i128 {
    x
}

#[ensures(Int::from(x) == Int::from(result))]
pub fn foousize(x: usize) -> usize {
    x
}

#[requires(x == usize::MAX)]
#[requires(y < usize::MAX)]
#[ensures(Int::from(y) < Int::from(x) + Int::from(100))]
#[ensures(Int::from(y) <= Int::from(x) + Int::from(100))]
#[ensures(Int::from(x) > Int::from(x) - Int::from(100))]
#[ensures(Int::from(x) >= Int::from(x) - Int::from(100))]
#[ensures(Int::from(x) % Int::from(100) < Int::from(100))]
#[ensures(Int::from(x) / Int::from(100) < Int::from(x))]
#[ensures(Int::from(x) * Int::from(100) > -Int::from(x))]
pub fn foo_ops(x: usize, y: usize) -> usize {
    x
}
