use prusti_contracts::*;

#[requires(x[2] > 10)]
fn test1(x: [i32; 3]) {
    assert!(x[2] > 0);
}

#[trusted]
fn main() {}
