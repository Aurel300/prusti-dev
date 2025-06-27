/*use prusti_contracts::*;*/

/*#[requires(n >= 0)]*/
/*#[ensures(result == old(n) * (1 + old(n) * (1 + old(n))))]*/
fn test(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    while ia < n {
        /*body_invariant*/drop(n == old(n));
        /*body_invariant*/drop(res == ia * (1 + n * (1 + n)));
        /*body_invariant*/drop(ia < n);
        res += 1;
        let mut ib = 0;

        while ib < n {
            /*body_invariant*/drop(n == old(n));
            /*body_invariant*/drop(res == ia * (1 + n * (1 + n)) + 1 + ib * (1 + n));
            /*body_invariant*/drop(ib < n);
            res += 1;
            let mut ic = 0;

            while ic < n {
                /*body_invariant*/drop(n == old(n));
                /*body_invariant*/drop(ic < n && res == ia * (1 + n * (1 + n)) + 1 + ib * (1 + n) + 1 + ic);
                res += 1;
                ic += 1;
            }

            ib += 1;
        }

        ia += 1;
    }

    res
}

fn main() {

}
