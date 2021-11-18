use prusti_contracts::*;

#[requires(a ==> b)]
fn test1(a: bool, b: bool) {}

fn main() {
    test1(false, false);
    test1(false, true);
    test1(true, true);
}
