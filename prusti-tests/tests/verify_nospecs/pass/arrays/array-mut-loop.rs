/*use prusti_contracts::*;*/

fn main() {}

fn looping() {
    let mut a = [0; 3];

    let mut i = 0;
    while i < 3 {
        /*body_invariant*/drop(0 <= i && i < 3);
        a[i] = i;

        i += 1;
    }

    /*assert*/drop(i == 3);
}
