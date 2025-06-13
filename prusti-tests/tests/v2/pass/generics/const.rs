use prusti_contracts::*;

// struct Foo<const N: usize> {
//     arr: [i32; N],
// }

#[requires(N > 0)]
fn foo<const N: usize, T>() {
    assert!(N > 0);
}
/*
#[requires(N > 10)]
fn bar<const N: usize, T>() {
    foo::<N, T>();
}
*/
fn main() {
    foo::<0, i32>();
}
