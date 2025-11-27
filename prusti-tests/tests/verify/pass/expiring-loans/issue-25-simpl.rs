/// Issue #25 "Exhaling postconditions with `old(..)`"

use prusti_contracts::*;

struct T {
    f: i32,
}

#[ensures(old(*x) == result)]
fn extract(x: &mut i32) -> i32 {
    *x
}

fn main() {

}
