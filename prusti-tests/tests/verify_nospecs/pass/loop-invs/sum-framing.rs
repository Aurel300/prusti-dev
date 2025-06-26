/*use prusti_contracts::*;*/

/*#[requires(0 <= n)]*/
/*#[ensures(result == old(n) * (old(n) + 1) / 2)]*/
fn sum(n: i32) -> i32 {
    let mut res = 0;
    let mut i = 0;
    while i < n {
        // Note: here we use `n`, not `old(n)`
        /*body_invariant*/drop(i < n);
        /*body_invariant*/drop(res == i * (i + 1) / 2);
        i = i + 1;
        res = res + i;
    }
    res
}

fn test() {
    /*assert*/drop(sum(100) == 5050);
    /*assert*/drop(sum(100) != 5);
    /*assert*/drop(sum(0) != 1);
    /*assert*/drop(sum(0) == 0);
    /*assert*/drop(sum(1) != 0);
    /*assert*/drop(sum(1) == 1);
}

fn main() {}
