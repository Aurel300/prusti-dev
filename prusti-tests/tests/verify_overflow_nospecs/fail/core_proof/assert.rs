
/*use prusti_contracts::*;*/

fn assert1() {
    /*assert*/drop(false);     // ERRXR: the asserted expression might not hold
}

fn assert2() {
    /*assert*/drop(true);
}

fn main() {}
