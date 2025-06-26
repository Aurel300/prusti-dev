/*use prusti_contracts::*;*/

/* #[refine_spec(where T: Copy, [pure])] */
/*#[trusted]*/
fn test<T>(_t: T) -> bool {
    true
}

#[derive(PartialEq, Eq)]
struct Copyrighted; // not Copy

fn main() {
    /*prusti_assert*/drop(test(Copyrighted) == test(Copyrighted)); // ERRXR: [Prusti: invalid specification] use of impure function "test" in pure code is not allowed
}
