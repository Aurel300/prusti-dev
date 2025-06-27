#![feature(box_syntax)]

/*use prusti_contracts::*;*/

/*#[trusted]*/
fn random() -> u32 {
    /*unimplemented!()*/
}

fn test() {
    let mut x: Box<u32>;

    'myloop: while {
        x = box random();
        if *x == 0 {
            break 'myloop;
        }
        *x < 55
    } {
        /*body_invariant*/drop(*x < 55);
        /*assert*/drop(*x != 100);
    }

    /*assert*/drop(*x == 0 || *x >= 55);
}

fn main() {}
