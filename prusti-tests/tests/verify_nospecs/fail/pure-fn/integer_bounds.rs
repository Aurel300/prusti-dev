/*use prusti_contracts::*;*/

/*#[pure]*/
/*#[requires(a + b <= std::u32::MAX)]*/
fn sum_pure(a: u32, b: u32) -> u32 {
    a + b
}

/*#[trusted]*/
/*#[pure]*/
fn u32_foo() -> u32 {
    5
}

fn u32_foo_call_1() {
    let n = u32_foo();
    /*assert*/drop(0 <= n);
}

fn u32_foo_call_2() {
    let n = u32_foo();
    /*assert*/drop(n <= 4294967295); // ERRXR
}

fn u32_foo_call_3() {
    /*assert*/drop(0 <= u32_foo());
}

fn u32_foo_call_4() {
    /*assert*/drop(u32_foo() <= 4294967295); // ERRXR
}

/*#[ensures(0 <= u32_foo())]*/
fn u32_foo_call_5() {
}

/*#[ensures(u32_foo() <= 4294967295)]*/ // ERRXR: postcondition
fn u32_foo_call_6() {
}

fn main() {}
