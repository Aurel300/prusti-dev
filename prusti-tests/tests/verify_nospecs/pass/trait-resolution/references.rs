/*use prusti_contracts::*;*/

trait Trait<T> {
    fn foo(value: T) -> i32 {
        1
    }
}

struct Example;

/*#[refine_trait_spec]*/
impl Trait<&i32> for Example {
    /*#[ensures(result == *value)]*/
    fn foo(value: &i32) -> i32 {
        *value
    }
}

struct PureExample;

/*#[refine_trait_spec]*/
impl Trait<&i32> for PureExample {
    /*#[pure]*/
    /*#[ensures(result == *value)]*/
    fn foo(value: &i32) -> i32 {
        *value
    }
}

fn main() {
    let x = 5;
    let y = 6;
    /*assert*/drop(Example::foo(&x) == x);
    /*assert*/drop(Example::foo(&y) == y);
    /*assert*/drop(PureExample::foo(&x) == x);
    /*prusti_assert*/drop(PureExample::foo(&x) == x);
}
