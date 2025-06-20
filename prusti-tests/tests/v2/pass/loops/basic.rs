use prusti_contracts::*;

fn main() {
    let mut x = 0;
    while {
        body_invariant!(x <= 10);
        x < 10
    } {
        x += 1;
    }
}
