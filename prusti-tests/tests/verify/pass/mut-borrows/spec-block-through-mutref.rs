use prusti_contracts::*;

pub struct S {
    v: i32,
}

// The value behind a mutable reference lives in the heap rather than in the
// reference's snapshot, so a spec block has to read it from there, just like a
// pre/postcondition does.

#[requires(s.v == 5)]
#[ensures(s.v == 5)]
fn untouched(s: &mut S) {
    prusti_assert!(s.v == 5);
}

#[requires(s.v == 5)]
#[ensures(s.v == 6)]
fn bumped(s: &mut S) {
    prusti_assert!(s.v == 5);
    s.v += 1;
    prusti_assert!(s.v == 6);
}

#[requires(s.v == 5)]
fn through_a_reborrow(s: &mut S) {
    let r = &mut *s;
    prusti_assert!(r.v == 5);
}
