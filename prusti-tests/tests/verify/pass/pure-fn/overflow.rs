use prusti_contracts::*;

#[pure]
#[ensures(result == i * 2)]
fn double(i: u32) -> u32 {
    i + i
}

#[ensures(result == double(i))]
fn call_double(i:u32) -> u32 {
    double(i)
}
