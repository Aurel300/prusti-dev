use prusti_contracts::*;

fn main() {
    let x = (String::new(), 5);
    let y = x.0;
    prusti_assert!(x.1 == 5);
}

struct Inner<T>(T, i32);
struct Outer<A, B>(B, Inner<A>); 

fn foo<X, Y>(x: Outer<Y, X>) {
    let _a = x.0;
    let _b = x.1.0;
    prusti_assert!(x.1.1 + 1 - 1 == x.1.1);
}
