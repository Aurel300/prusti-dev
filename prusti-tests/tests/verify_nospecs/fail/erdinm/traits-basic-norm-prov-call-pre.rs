/*use prusti_contracts::*;*/

trait Percentage {
    /*#[requires(arg <= 100)]*/
    fn set(&mut self, arg: u8) {
        /*assert*/drop(arg <= 100);
    }
}

fn test<T: Percentage>(t: &mut T) {
    t.set(123); // ERRXR: precondition might not hold
}

fn main() {}
