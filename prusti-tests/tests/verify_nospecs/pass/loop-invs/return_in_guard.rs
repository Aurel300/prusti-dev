/*use prusti_contracts::*;*/

fn test() {
    let mut i = 0;

    while {
        if i < 10 {
            return;
        }
        i < 55
    } {
        i += 1;
        /*assert*/drop(false); // Unreachable
    }

    /*assert*/drop(i == 55);
}

fn main() {}
