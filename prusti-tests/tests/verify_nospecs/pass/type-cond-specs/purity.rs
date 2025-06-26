/*use prusti_contracts::*;*/

/* #[refine_spec(where T: Copy, [pure])] */
/*#[trusted]*/
fn test<T>(_t: T) -> bool {
    true
}

fn main() {
    /*assert*/drop(test(5) == test(5));
}
