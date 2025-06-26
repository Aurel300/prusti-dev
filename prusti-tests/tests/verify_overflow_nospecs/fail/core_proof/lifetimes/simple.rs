
/*use prusti_contracts::*;*/
fn main() {}

pub fn mutable_borrow() {
    let mut a = 4;
    let x = &mut a;
    *x = 2;
    /*assert*/drop(*x == 2);
}
pub fn mutable_borrow_assert_false() {
    let mut a = 4;
    let x = &mut a;
    *x = 2;
    /*assert*/drop(*x == 4);      // ERRXR: the asserted expression might not hold
}

pub fn mutable_reborrow() {
    let mut a = 4;
    let mut x = &mut a;
    let y = &mut (*x);
    *y = 3;
    /*assert*/drop(*y == 3);
}
pub fn mutable_reborrow_assert_false() {
    let mut a = 4;
    let mut x = &mut a;
    let y = &mut (*x);
    *y = 3;
    /*assert*/drop(*y == 4);      // ERRXR: the asserted expression might not hold
}

pub fn shared_borrow() {
    let mut a = 4;
    let x = &a;
    let y = &a;
    /*assert*/drop(*y == 4);
}
pub fn shared_borrow_assert_false() {
    let mut a = 4;
    let x = &a;
    let y = &a;
    /*assert*/drop(*y == 5);      // ERRXR: the asserted expression might not hold
}

pub fn shared_reborrow() {
    let mut a = 4;
    let x = &a;
    let y = &(*x);
    let z = &(*x);
    /*assert*/drop(*z == 4);
}
pub fn shared_reborrow_assert_false() {
    let mut a = 4;
    let x = &a;
    let y = &(*x);
    let z = &(*x);
    /*assert*/drop(*z == 5);      // ERRXR: the asserted expression might not hold
}

pub fn simple_references() {
    let mut a = 4;
    let mut b = &mut a;
    let mut c = &mut b;
    let mut d = &mut c;
}
pub fn simple_references_assert_false() {
    let mut a = 4;
    let mut b = &mut a;
    let mut c = &mut b;
    let mut d = &mut c;
    /*assert*/drop(false);      // ERRXR: the asserted expression might not hold
}

// FIXME: Fix overlapping shared references
// pub fn shared_borrow() {
//     let mut a = 4;
//     let x = &a;
//     let y = &a;
//     /*assert*/drop(*x == 4);
// }
