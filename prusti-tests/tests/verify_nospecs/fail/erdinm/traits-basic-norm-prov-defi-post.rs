/*use prusti_contracts::*;*/

trait Percentage {
    /*#[ensures(result <= 100)]*/ // ERRXR: postcondition might not hold
    fn get(&self) -> u8 {
        101
    }
}

fn main() {}
