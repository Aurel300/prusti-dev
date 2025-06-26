/*use prusti_contracts::*;*/

fn test() {
    let mut i = 0;

    while i < 10 {
        /*body_invariant*/drop(i < 10);
        'inner: while {
            i += 1;
            i -= 1;
            i < 10
        } {
            /*body_invariant*/drop(i < 10);
            i += 1;
            if i == 234 {
                break;
            }
            if i == 345 {
                continue;
            }
        }
        /*assert*/drop(i == 10);
    }

    /*assert*/drop(i == 10);
}

fn main() {}
