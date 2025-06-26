/*use prusti_contracts::*;*/

trait MyTrait {
    fn get_value(&self) -> i32;
}
/*
#[extern_spec]
trait MyTrait {
    /*#[ensures(result == 42)]*/ // ERRXR: postcondition might not hold.
    fn get_value(&self) -> i32;
}
*/
struct Impl;
impl MyTrait for Impl {
    fn get_value(&self) -> i32 {
        43
    }
}

fn main() {
    let s = Impl {};
    /*assert*/drop(MyTrait::get_value(&s) == 42);
}
