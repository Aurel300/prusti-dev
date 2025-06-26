
/*use prusti_contracts::*;*/

fn test1() {
    /*assert*/drop(false);
}

fn test2() {
    /*prusti_assert*/drop(false);
}

/*#[requires(false)]*/
fn test3() { }

fn test4() {
    test3();
}

fn main() {}
