/*use prusti_contracts::*;*/

fn get_u32() -> u32 {
    123
}

/*#[requires(get_u32() == 123)]*/
// ERRXR use of impure function "get_u32" in pure code
fn client_1() {}

/*#[requires(if false { get_u32() == 123 } else { 1 == 1 })]*/
// ERRXR use of impure function "get_u32" in pure code
fn client_2() {}

fn main() {}
