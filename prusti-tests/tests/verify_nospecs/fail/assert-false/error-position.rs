/*use prusti_contracts::*;*/

/*#[ensures(false)]*/ // ERRXR: postcondition might not hold
fn foo1(x: bool) {}

/*#[ensures(false && false)]*/ // ERRXR: postcondition might not hold
fn foo2(x: bool) {}

/*#[ensures(!true)]*/ // ERRXR: postcondition might not hold
fn foo3(x: bool) {}

/*#[ensures(!(true || x))]*/ // ERRXR: postcondition might not hold
fn foo4(x: bool) {}

/*#[ensures(!(false || true))]*/ // ERRXR: postcondition might not hold
fn foo5(x: bool) {}

/*#[ensures(!(x || !false))]*/ // ERRXR: postcondition might not hold
fn foo6(x: bool) {}

/*#[ensures(!(x || !x))]*/ // ERRXR: postcondition might not hold
fn foo7(x: bool) {}

/*#[ensures(true ==> false)]*/ // ERRXR: postcondition might not hold
fn foo8(x: bool) {}

/*#[ensures(x || true ==> !(x || !x))]*/ // ERRXR: postcondition might not hold
fn foo9(x: bool) {}

/*#[ensures(x == x)]*/
/*#[ensures(false)]*/ // ERRXR: postcondition might not hold
fn foo10(x: bool) {}

/*#[ensures(false)]*/ // ERRXR: postcondition might not hold
/*#[ensures(x == x)]*/
fn foo11(x: bool) {}

/*#[ensures(x == x)]*/
/*#[ensures(!true)]*/ // ERRXR: postcondition might not hold
/*#[ensures(x == x)]*/
fn foo12(x: bool) {}

/*#[ensures(false)]*/ // ERRXR: postcondition might not hold
/*#[ensures(result == x)]*/
pub fn foo13(x: u32) -> u32 {
    x
}

fn main() {}
