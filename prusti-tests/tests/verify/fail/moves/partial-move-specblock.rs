use prusti_contracts::*;

fn main() {
    let x = (String::new(), 5);
    let _y = x.0;
    prusti_assert!(x.1 == 6); //~ ERROR: assertion might not hold
}
