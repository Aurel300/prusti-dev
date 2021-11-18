use prusti_contracts::*;

fn main() {
    let mut i = 0;
    while i < 10 {
        body_invariant!(i >= 0 && i < 10);
        assert!(i >= 0 && i < 10);
        i += 1;
    }
}
