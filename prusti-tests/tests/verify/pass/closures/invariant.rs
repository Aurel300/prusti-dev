use prusti_contracts::*;

fn main() {
    let mut count = 0;
    let mut f = closure!(
        #[view(count: i32)]
        #[requires(i >= 0)]
        #[invariant(*views.count >= 0)]
        #[invariant(*views.count >= old(*views.count))]
        #[ensures(*views.count == old(*views.count) + 1)]
        |i: i32| -> i32 {
            assert!(count >= 0);
            count += 1;
            i + 1
        }
    );
    f(0);
}
