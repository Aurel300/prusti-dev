use prusti_contracts::*;

struct Foo {
    foo: usize
}

enum Bar {
    Bar(usize)
}

fn main() {
    let f1 = closure!(
        #[requires(i >= 0)]
        #[ensures(result == 1)]
        |i: i32| -> i32 { 1 }
    );
    assert!(f1(0) == 1);

    let f2 = closure!(
        #[requires(i)]
        #[ensures(result == 1)]
        |i: bool| -> i32 { 1 }
    );
    assert!(f2(true) == 1);

    let f3 = closure!(
        #[requires(i >= 10)]
        #[ensures(result == 1)]
        |i: usize| -> i32 { 1 }
    );
    assert!(f3(10) == 1);

    let f4 = closure!(
        #[requires(i.foo >= 10)]
        #[ensures(result == 1)]
        |i: Foo| -> i32 { 1 }
    );
    assert!(f4(Foo { foo: 10 }) == 1);

    let f5 = closure!(
        #[requires(matches!(i, Bar::Bar(x) if x >= 10))]
        #[ensures(result == 1)]
        |i: Bar| -> i32 { 1 }
    );
    assert!(f5(Bar::Bar(10)) == 1);

    let f6 = closure!(
        #[ensures(result)]
        || -> bool { true }
    );
    assert!(f6());

    let f7 = closure!(
        #[ensures(result.foo == 42)]
        || -> Foo { Foo { foo: 42 } }
    );
    assert!(f7().foo == 42);
}
