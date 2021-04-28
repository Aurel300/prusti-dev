use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

fn main() {
    let mut count = 0;
    let mut cl = closure!(
        #[view(count: i32)]
        #[ensures(*views.count == old(*views.count) + 1)]
        #[ensures(result == old(*views.count))]
        || -> i32 { let r = count; count += 1; r }
    );

    assert!(cl() == 0);
    assert!(cl() == 1);

    // cl is no longer live here
    //assert!(count == 2);
}
