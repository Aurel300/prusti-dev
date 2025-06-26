
/*use prusti_contracts::*;*/

/*#[requires(true)]*/
/*#[ensures(true)]*/
fn test1() {
}

/*#[requires(true)]*/
/*#[ensures(false)]*/   // ERRXR: postcondition might not hold.
fn test2() {
}

/*#[requires(a + a == b)]*/
/*#[ensures(2 * a == b)]*/
fn test3(a: u32, b: u32) {}

/*#[requires(a + a == b)]*/
/*#[ensures(3 * a == b)]*/  // ERRXR: postcondition might not hold.
fn test4(a: u32, b: u32) {}

fn test5() {
    test3(1, 3);    // ERRXR: precondition might not hold.
}

fn test6() {
    test4(1, 2);
    /*assert*/drop(false);
}

fn main() {}
