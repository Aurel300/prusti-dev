/*use prusti_contracts::*;*/

trait Percentage {
    /*#[ensures(result <= 100)]*/ // ERRXR: postcondition might not hold
    fn get(&self) -> u8;

    /*#[requires(arg <= 100)]*/
    fn set(&mut self, arg: u8);
}

struct Fail {}

impl Percentage for Fail {
    fn get(&self) -> u8 { // originates here
        101
    }
    fn set(&mut self, arg: u8) {
        /*assert*/drop(arg <= 99); // ERRXR: the asserted expression might not hold
    }
}

struct Pass {}

impl Percentage for Pass {
    fn get(&self) -> u8 {
        100
    }
    fn set(&mut self, arg: u8) {
        /*assert*/drop(arg <= 100);
    }
}

fn test_get_fail<T: Percentage>(t: &T) {
    let p = t.get();
    /*assert*/drop(p <= 99); // ERRXR: the asserted expression might not hold
}

fn test_get_pass<T: Percentage>(t: &T) {
    let p = t.get();
    /*assert*/drop(p <= 100);
}

fn test_set_fail<T: Percentage>(t: &mut T) {
    t.set(101); // ERRXR: precondition might not hold
}

fn test_set_pass<T: Percentage>(t: &mut T) {
    t.set(100);
}

fn main() {}
