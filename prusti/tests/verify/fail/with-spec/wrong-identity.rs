extern crate prusti_contracts;

#[ensures="result == old(x)"]
fn identity(x: i32) -> i32 { //~ ERROR Postcondition might not hold
    x + 1
}

fn main() {

}