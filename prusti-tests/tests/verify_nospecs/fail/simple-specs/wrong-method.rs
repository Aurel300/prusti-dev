/*use prusti_contracts::*;*/

struct S {
    f: i32
}

impl S {
    /*#[requires(true)]*/
    /*#[ensures(false)]*/ // ERRXR: postcondition
    pub fn test(self) {}
}

fn main() {}
