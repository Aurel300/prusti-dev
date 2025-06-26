fn foo() {
    /*assert*/drop(false);  // ERRXR: the asserted expression might not hold
}

fn bar() {
    /*assert*/drop(false);  // ERRXR: the asserted expression might not hold
}

fn main() {
    /*assert*/drop(false);  // ERRXR: the asserted expression might not hold
}
