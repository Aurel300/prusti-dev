/*use prusti_contracts::*;*/

trait Percentage {
    /*#[ensures(result <= 100)]*/
    fn get(&self) -> u8;
}

fn test<T: Percentage>(t: &T) {
    let p = t.get();
    /*assert*/drop(p <= 99); // ERRXR: the asserted expression might not hold
}

fn main() {}
