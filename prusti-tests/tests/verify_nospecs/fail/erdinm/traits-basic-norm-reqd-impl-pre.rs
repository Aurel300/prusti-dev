/*use prusti_contracts::*;*/

trait Percentage {
    /*#[requires(arg <= 100)]*/
    fn set(&mut self, arg: u8);
}

struct Effective {}

impl Percentage for Effective {
    fn set(&mut self, arg: u8) {
        /*assert*/drop(arg <= 99); // ERRXR: the asserted expression might not hold
    }
}

fn main() {}
