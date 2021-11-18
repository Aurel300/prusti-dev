#![feature(stmt_expr_attributes)]

use prusti_contracts::*;

#[pure]
fn blah(_a: bool, _b: usize) -> bool { true }

#[requires(
    forall(|_idx: bool, _x: usize| a == b, triggers = [ (blah(_idx, _x)) ])
)]
fn test1(a: bool, b: bool) {}

fn main() {
    test1(true, true);
    test1(false, false);
}
