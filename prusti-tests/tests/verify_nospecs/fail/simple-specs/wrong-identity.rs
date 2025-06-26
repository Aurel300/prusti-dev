/*use prusti_contracts::*;*/

/*#[ensures(result == old(x))]*/ // ERRXR: postcondition might not hold
fn identity(x: i32) -> i32 {
    x + 1
}

fn main() {

}
