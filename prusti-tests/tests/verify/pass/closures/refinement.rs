use prusti_contracts::*;

// ignore-test

#[requires(f |= |arg: i32| [ requires(true), ensures(cl_result >= 0) ])]
fn foo<T: Fn(i32) -> i32>(f: T) {}

#[requires(f |= |arg: i32| [ requires(arg >= 0), ensures(cl_result == arg) ])]
#[requires(f |= |arg: i32| [ requires(arg < 0), ensures(cl_result == arg * arg) ])]
fn bar<T: Fn(i32) -> i32>(f: T) {
    foo(f); // TODO: this causes an infinite loop inside Prusti?
}

fn main() {}
