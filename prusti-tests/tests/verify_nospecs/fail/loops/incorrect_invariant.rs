/*use prusti_contracts::*;*/

pub fn simple_loop() {
    let mut x = 0;
    while x < 100 {
        /*body_invariant*/drop(x == 42); // ERRXR: loop invariant might not hold
        x += 1;
    }
}

fn main() {}
