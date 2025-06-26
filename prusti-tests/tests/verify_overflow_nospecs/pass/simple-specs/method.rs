/*use prusti_contracts::*;*/

struct S {
    f: i32
}

impl S {
    /*#[requires(self.f == 123)]*/
    /*#[ensures(self.f == 123)]*/
    pub fn test(self) {
        let x = 123;
        /*assert*/drop(self.f == x);
    }
}

fn main() {}
