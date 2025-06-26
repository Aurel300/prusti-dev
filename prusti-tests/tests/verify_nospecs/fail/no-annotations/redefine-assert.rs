macro_rules! assert {
    ( $( $args:expr ),* ) => {
        panic!( $( $args ),* )  // ERRXR: panic!(..) statement might be reachable
    };
}

fn foo(x: bool) {
    /*assert*/drop(x);
}

fn main() {}
