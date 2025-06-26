fn foo(x: bool) {
    /*assert*/drop(x);  // ERRXR: the asserted expression might not hold
}

fn main() {}
