use prusti_contracts::*;

#[requires(ghost_pred(x, y))]
fn foo<GhostT: Fn(i32, i32) -> bool>(
    x: i32,
    y: i32,
    ghost_pred: GhostT,
) {}

#[pure]
fn is_five_and_ten(x: i32, y: i32) -> bool {
    x == 5 && y == 10
}

fn main() {
    let x = 5;
    let y = 10;
    // FIXME: inlining 5 and 10 does not work
    foo(x, y, is_five_and_ten);

    foo(y, x, closure!(
        #[pure]
        #[requires(true)]
        |a: i32, b: i32| -> bool { a == 10 && b == 5 }
    ));
}
