use prusti_contracts::*;

fn main() {
    let f = closure!(
        #[requires(i >= 0)]
        #[invariant(true)]
        |i: i32| -> i32 { i + 1 }
    );
    f(0);
}
