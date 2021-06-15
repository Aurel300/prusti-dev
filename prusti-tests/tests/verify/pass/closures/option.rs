use prusti_contracts::*;

#[requires(
    opt.is_some() ==>
        f |=! |arg: i32| -> MyOption [ requires(arg == opt.unwrap()) ]
)]
#[ensures(!old(opt.is_some()) ==> !result.is_some())]
#[ensures(
    old(opt.is_some()) ==>
        f ~>! |arg: i32| -> MyOption
            { arg == old(opt.unwrap()) }
            { cl_result == result }
)]
fn and_then<F: FnMut(i32) -> MyOption>(opt: MyOption, f: &mut F) -> MyOption {
    match opt {
        MyOption::Some(x) => f(x),
        MyOption::None => MyOption::None,
    }
}

fn test_and_then() {
    let mut sq = closure!(
        #[ensures(result.is_some())]
        #[ensures(result.unwrap() == x * x)]
        |x: i32| -> MyOption { MyOption::Some(x * x) }
    );
    let mut nope = closure!(
        #[ensures(!result.is_some())]
        |x: i32| -> MyOption { MyOption::None }
    );
    assert!(and_then(and_then(MyOption::Some(2), &mut sq), &mut sq).unwrap() == 16);
    assert!(!and_then(and_then(MyOption::Some(2), &mut sq), &mut nope).is_some());
    assert!(!and_then(and_then(MyOption::Some(2), &mut nope), &mut sq).is_some());
    assert!(!and_then(and_then(MyOption::None, &mut sq), &mut sq).is_some());
}

#[requires(
    opt.is_some() ==>
        f |=! |arg: i32| -> bool [ requires(arg == opt.unwrap()) ]
)]
#[ensures(!old(opt.is_some()) ==> !result.is_some())]
#[ensures(
    old(opt.is_some()) ==>
        f ~>! |arg: i32| -> bool
            { arg == old(opt.unwrap()) }
            { cl_result == result.is_some() && (cl_result ==> result.unwrap() == arg) }
)]
fn filter<F: FnMut(i32) -> bool>(opt: MyOption, f: &mut F) -> MyOption {
    match opt {
        MyOption::Some(x) => {
            if f(x) {
                MyOption::Some(x)
            } else {
                MyOption::None
            }
        }
        _ => MyOption::None,
    }
}

fn test_filter() {
    let mut cl = closure!(
        #[ensures(result == (n >= 0))]
        |n: i32| -> bool { n >= 0 }
    );
    assert!(!filter(MyOption::None, &mut cl).is_some());
    assert!(!filter(MyOption::Some(-3), &mut cl).is_some());
    assert!(filter(MyOption::Some(4), &mut cl).unwrap() == 4);
}

#[requires(
    opt.is_some() ==>
        f |=! |arg: i32| -> i32 [ requires(arg == opt.unwrap()) ]
)]
#[ensures(old(opt.is_some()) == result.is_some())]
#[ensures(
    old(opt.is_some()) ==>
        f ~>! |arg: i32| -> i32
            { arg == old(opt.unwrap()) }
            { cl_result == result.unwrap() }
)]
fn map<F: FnMut(i32) -> i32>(opt: MyOption, f: &mut F) -> MyOption {
    match opt {
        MyOption::Some(x) => MyOption::Some(f(x)),
        MyOption::None => MyOption::None,
    }
}

fn test_map() {
    let mut cl = closure!(
        #[requires(i > 4)]
        #[ensures(result == i + 1)]
        |i: i32| -> i32 { i + 1 }
    );
    assert!(map(MyOption::Some(5), &mut cl).unwrap() == 6);
    assert!(!map(MyOption::None, &mut cl).is_some());

    let mut count = 0;
    let mut cl = closure!(
        #[view(count: i32)]
        #[requires(i != *views.count)]
        #[ensures(*views.count == old(*views.count) + 1)]
        |i: i32| -> i32 { count += 1; i * 2 }
    );
    map(MyOption::Some(1), &mut cl);
}

#[requires(
    opt.is_some() ==>
        f |=! |arg: i32| -> i32 [ requires(arg == opt.unwrap()) ]
)]
#[ensures(
    old(opt.is_some()) ==>
        f ~>! |arg: i32| -> i32
            { arg == old(opt.unwrap()) }
            { cl_result == result }
)]
#[ensures(
    !old(opt.is_some()) ==> result == default
)]
fn map_or<F: FnMut(i32) -> i32>(opt: MyOption, default: i32, f: &mut F) -> i32 {
    match opt {
        MyOption::Some(x) => f(x),
        MyOption::None => default,
    }
}

fn test_map_or() {
    let mut cl = closure!(
        #[requires(i > 4)]
        #[ensures(result == i + 1)]
        |i: i32| -> i32 { i + 1 }
    );
    assert!(map_or(MyOption::Some(15), 0, &mut cl) == 16);
    assert!(map_or(MyOption::None, 0, &mut cl) == 0);
}

#[requires(
    opt.is_some() ==>
        f |=! |arg: i32| -> i32 [ requires(arg == opt.unwrap()) ]
)]
#[requires(
    !opt.is_some() ==>
        default |=! |dummy: i32| -> i32 [ requires(true) ]
)]
#[ensures(
    old(opt.is_some()) ==>
        f ~>! |arg: i32| -> i32
            { arg == old(opt.unwrap()) }
            { cl_result == result }
)]
// TODO: postcondition does not verify without the dummy argument to default
#[ensures(
    !old(opt.is_some()) ==>
        default ~>! |dummy: i32| -> i32
            {}
            { cl_result == result }
)]
fn map_or_else<
    F: FnMut(i32) -> i32,
    D: FnMut(i32) -> i32,
>(opt: MyOption, default: &mut D, f: &mut F) -> i32 {
    match opt {
        MyOption::Some(x) => f(x),
        MyOption::None => default(0),
    }
}

fn test_map_or_else() {
    let mut cl = closure!(
        #[ensures(result == x * 3)]
        |x: i32| -> i32 { x * 3 }
    );
    let mut cl_def = closure!(
        #[ensures(result == 42)]
        |_: i32| -> i32 { 42 }
    );
    assert!(map_or_else(MyOption::Some(3), &mut cl_def, &mut cl) == 9);
    assert!(map_or_else(MyOption::None, &mut cl_def, &mut cl) == 42);
}

#[requires(
    !opt.is_some() ==>
        f |=! |dummy: i32| -> MyOption [ requires(true) ]
)]
#[ensures(old(opt.is_some()) ==> result.is_some())]
// TODO: fold/unfold issue
// #[ensures(old(opt.is_some()) ==> result == old(opt))]
// TODO: postcondition does not verify without the dummy argument to f
#[ensures(
    !old(opt.is_some()) ==>
        f ~>! |dummy: i32| -> MyOption
            {}
            { cl_result == result }
)]
fn or_else<F: FnMut(i32) -> MyOption>(opt: MyOption, f: &mut F) -> MyOption {
    match opt {
        MyOption::Some(x) => MyOption::Some(x),
        MyOption::None => f(0),
    }
}

fn test_or_else() {
    let mut cl_none = closure!(
        #[ensures(!result.is_some())]
        |_: i32| -> MyOption { MyOption::None }
    );
    let mut cl_some = closure!(
        #[ensures(result.is_some())]
        #[ensures(result.unwrap() == 42)]
        |_: i32| -> MyOption { MyOption::Some(42) }
    );
    //assert!(or_else(MyOption::Some(5), &mut cl_some).unwrap() == 5);
    assert!(or_else(MyOption::Some(5), &mut cl_some).is_some());
    assert!(or_else(MyOption::None, &mut cl_some).unwrap() == 42);
    assert!(!or_else(MyOption::None, &mut cl_none).is_some());
}

fn main() {}

// Prusti glue for Option<i32>
    #[derive(PartialEq, Eq)]
    enum MyOption {
        None,
        Some(i32),
    }

    impl MyOption {
        #[pure]
        fn is_some(&self) -> bool {
            matches!(self, MyOption::Some(_))
        }

        #[pure]
        #[requires(self.is_some())]
        fn unwrap(&self) -> i32 {
            match self {
                MyOption::Some(n) => *n,
                MyOption::None => unreachable!(),
            }
        }
    }
// end Prusti glue
