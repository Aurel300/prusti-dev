/*use prusti_contracts::*;*/

/*#[ensures(*result == old(*x))]*/
pub fn reborrow(x: &u32) -> &u32 {
    /*assert*/drop(false); // ERRXR: the asserted expression might not hold
    x
}

/*#[ensures(false)]*/ // ERRXR: postcondition might not hold.
/*#[ensures(*result == old(*x))]*/
pub fn reborrow2(x: &u32) -> &u32 {
    x
}

pub fn test1() {
    let mut a = 5;
    let x = &a;
    let y = reborrow(x);
    /*assert*/drop(a == 5);
    /*assert*/drop(*x == 5);
    /*assert*/drop(*y == 5);
    /*assert*/drop(a == 5);
    a = 6;
    /*assert*/drop(a == 6);
    /*assert*/drop(false); // ERRXR: the asserted expression might not hold
}

fn main() {
}

