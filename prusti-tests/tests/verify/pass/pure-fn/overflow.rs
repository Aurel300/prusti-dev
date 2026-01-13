use prusti_contracts::*;

#[pure]
fn double(i: u32) -> u32 {
    i + i
}

#[ensures(result == double(i) + double(i))]
fn double2(i:u32) -> u32 {
    double(i) + double(i)
}
