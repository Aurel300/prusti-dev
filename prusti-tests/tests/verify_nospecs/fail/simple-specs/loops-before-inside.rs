/*use prusti_contracts::*;*/

fn test_invariant_on_entry() -> i32 {
    let mut x = 0;
    while x < 10 {
        /*body_invariant*/drop(false); // ERRXR: loop invariant might not hold in the first loop iteration
        x += 1;
    }
    x
}

fn test_invariant_after_loop_iteration() -> i32 {
    let mut x = 0;
    while x < 10 {
        /*body_invariant*/drop(x == 0); // ERRXR: loop invariant might not hold after a loop iteration
        x += 1;
    }
    x
}

fn main() {}
