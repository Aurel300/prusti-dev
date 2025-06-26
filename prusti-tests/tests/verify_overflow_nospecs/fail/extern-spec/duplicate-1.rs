/*use prusti_contracts::*;*/

struct TestStruct {}

impl TestStruct {
    /*#[pure]*/
    /*#[ensures(result >= a && result >= b)]*/
    /*#[ensures(result == a || result == b)]*/
    fn max(a: i32, b: i32) -> i32 {
        if a < b {
            b
        } else {
            a
        }
    }
}
/*
#[extern_spec]
impl TestStruct {
    /*#[pure]*/
    /*#[ensures(result >= a && result >= b)]*/
    /*#[ensures(result == a || result == b)]*/
    fn max(a: i32, b: i32) -> i32; // ERRXR: already has a specification
}
*/
fn main() {
    let x = TestStruct::max(1, 2);
    /*assert*/drop(x == 2)
}
