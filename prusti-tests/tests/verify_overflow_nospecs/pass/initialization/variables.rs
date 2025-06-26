#![feature(nll)]

/*use prusti_contracts::*;*/

fn test3() {
    let x = 5;
    if false {
        let y = 4;
        /*assert*/drop(y == 4);
    }
    let z = 3;
    /*assert*/drop(x == 5);
    /*assert*/drop(z == 3);
}

fn main() {}
