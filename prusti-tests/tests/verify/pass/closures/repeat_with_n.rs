use prusti_contracts::*;

#[requires(f |= || [ requires(true), ensures(true) ])]
#[requires(n >= 0)]
#[ensures(vec_len(&result) == n)]
#[ensures(
    forall(|idx: usize| 0 <= idx && idx < vec_len(&result)
        ==> (f ~> || {} { cl_result == vec_lookup(&result, idx) }))
)]
fn repeat_with_n<F: FnMut() -> i32>(mut f: F, n: usize) -> Vec<i32> {
    let mut ret = vec_new();
    let mut i = 0;
    while i < n {
        body_invariant!(i < n);
        body_invariant!(vec_len(&ret) == i);
        body_invariant!(
            forall(|idx: usize| 0 <= idx && idx < i
                ==> f ~> || {} { cl_result == vec_lookup(&ret, idx) })
        );
        vec_push(&mut ret, f());
        i += 1;
    }
    ret
}

fn main() {
    let mut c = 5;
    let mut cl = closure!(
        #[view(c: i32)]
        #[invariant(*views.c >= old(*views.c))]
        #[requires(true)]
        #[ensures(*views.c == old(*views.c) + 1)]
        #[ensures(result == *views.c * 2)]
        || -> i32 { c += 1; c * 2 }
    );
    cl();

    let r = repeat_with_n(cl, 4);
    assert!(vec_lookup(&r, 0) >= 14);
    assert!(vec_lookup(&r, 1) >= 14);
    assert!(vec_lookup(&r, 2) >= 14);
    assert!(vec_lookup(&r, 3) >= 14);

    // verifies, but takes relatively long
    // assert!(vec_lookup(&r, 0) % 2 == 0);
}

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
