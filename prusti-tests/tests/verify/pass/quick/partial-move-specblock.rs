use prusti_contracts::*;

fn main() {
    let x = (String::new(), 5);
    let y = x.0;
    prusti_assert!(x.1 == 5);
}
