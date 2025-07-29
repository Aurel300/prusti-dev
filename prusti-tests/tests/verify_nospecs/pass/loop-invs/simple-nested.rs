/*use prusti_contracts::*;*/

/*#[requires(n >= 0)]*/
/*#[ensures(result == old(n))]*/
fn test(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    while ia < n {
        /*body_invariant*/drop(res == ia);
        /*body_invariant*/drop(ia < n);
        res += 1;

        while false {
            /*body_invariant*/drop(true);
        }

        ia += 1;
    }

    res
}

fn main() {

}
