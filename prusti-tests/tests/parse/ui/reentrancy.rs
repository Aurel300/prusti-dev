// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

#[pure]
fn foo(x: bool) -> bool { true }

#[requires(true ==> foo(true ==> true))]
fn test1() {}

#[requires(true ==> forall(|x: usize| false ==> true))]
fn test2() {}

#[ensures(match true {
    b => (forall(|i: usize| true ==> false)),
})]
fn test3() {}

#[ensures(result == (forall(|i: i32| i < x ==> foo(true))))]
fn test4(x: i32) -> bool { true }

#[ensures(match result {
    Ok(x) => (forall(|i: i32| i < 1 ==> true)) && false,
    Err(_) => (forall(|i: i32| i < 1 ==> true))
})]
fn test5() -> Result<i32, i32> { Ok(0) }

fn main() {}
