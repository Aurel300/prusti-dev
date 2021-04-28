use prusti_contracts::*;

#[requires(f |= |arg: i32| -> [ requires(vec_contains(v, arg)) ])]
#[ensures(
    result ==>
        exists(|idx: usize| 0 <= idx && idx < vec_len(v)
            && forall(|idx2: usize| 0 <= idx2 && idx2 < idx
                ==> f ~>! |arg: i32| -> { arg == vec_lookup(v, idx2) } { !cl_result })
            && f ~>! |arg: i32| -> { arg == vec_lookup(v, idx) } { cl_result })
)]
#[ensures(
    !result ==> forall(|idx: usize| 0 <= idx && idx < vec_len(v)
        ==> f ~>! |arg: i32| -> { arg == vec_lookup(v, idx) } { !cl_result })
)]
fn any_vec<T: Fn(i32) -> bool>(v: &Vec<i32>, f: T) -> bool {
    let mut i = 0;
    while i < vec_len(v) {
        body_invariant!(i >= 0 && i < vec_len(v));
        body_invariant!(
            forall(|idx: usize| 0 <= idx && idx < i
                ==> f ~>! |arg: i32| -> { arg == vec_lookup(v, idx) } { !cl_result })
        );
        let el = vec_lookup(v, i);
        if f(el) {
            return true;
        }
        i += 1;
    }
    false
}

#[requires(vec_len(v) == 3)]
#[requires(vec_lookup(v, 0) == 1)]
#[requires(vec_lookup(v, 1) == 2)]
#[requires(vec_lookup(v, 2) == 3)]
fn test1(v: &Vec<i32>) {
    assert!(any_vec(
        &v,
        closure!(
            #[requires(true)]
            #[ensures(result == (i % 3 == 0))]
            |i: i32| -> bool { i % 3 == 0 }
        ),
    ));
}

#[requires(vec_len(v) == 3)]
#[requires(vec_lookup(v, 0) == 1)]
#[requires(vec_lookup(v, 1) == 2)]
#[requires(vec_lookup(v, 2) == 3)]
fn test2(v: &Vec<i32>) {
    assert!(!any_vec(
        &v,
        closure!(
            #[requires(true)]
            #[ensures(result == (i == 100))]
            |i: i32| -> bool { i == 100 }
        ),
    ));
}

#[requires(vec_len(v) == 3)]
#[requires(vec_lookup(v, 0) == 1)]
#[requires(vec_lookup(v, 1) == 2)]
#[requires(vec_lookup(v, 2) == 3)]
fn test3(v: &Vec<i32>) {
    assert!(!any_vec(
        &v,
        closure!(
            #[requires(true)]
            #[ensures(result == (i > 10))]
            |i: i32| -> bool { i > 10 }
        ),
    ));
}

fn main() {}

// Prusti glue for Vec<i32>
    #[trusted]
    #[ensures(vec_len(&result) == 0)]
    fn vec_new() -> Vec<i32> {
        vec![]
    }

    #[pure]
    #[trusted]
    #[ensures(result >= 0)]
    fn vec_len(vec: &Vec<i32>) -> usize {
        vec.len()
    }

    #[pure]
    #[trusted]
    #[requires(idx >= 0 && idx < vec_len(vec))]
    #[ensures(vec_contains(vec, result))]
    fn vec_lookup(vec: &Vec<i32>, idx: usize) -> i32 {
        vec[idx]
    }

    #[pure]
    #[trusted]
    fn vec_contains(vec: &Vec<i32>, val: i32) -> bool {
        vec.contains(&val)
    }

    #[trusted]
    #[ensures(vec_len(vec) == old(vec_len(vec)) + 1)]
    #[ensures(
        forall(|idx: usize| 0 <= idx && idx < old(vec_len(vec))
            ==> vec_lookup(vec, idx) == old(vec_lookup(vec, idx)),
            triggers = [(vec_lookup(vec, idx),)])
    )]
    #[ensures(vec_lookup(vec, old(vec_len(vec))) == value)]
    #[ensures(vec_contains(vec, value))]
    fn vec_push(vec: &mut Vec<i32>, value: i32) {
        vec.push(value);
    }
// end Prusti glue
