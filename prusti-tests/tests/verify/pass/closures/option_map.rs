use prusti_contracts::*;

#[requires(
    opt.is_some() ==>
        f |=! |arg: i32| [ requires(arg == opt.unwrap()) ]
)]
#[ensures(old(opt.is_some()) == result.is_some())]
#[ensures(
    old(opt.is_some()) ==>
        f ~>! |arg: i32|
            { arg == old(opt.unwrap()) }
            { cl_result == result.unwrap() }
)]
fn map<F: FnMut(i32) -> i32>(opt: MyOption, f: &mut F) -> MyOption {
    match opt {
        MyOption::Some(x) => MyOption::Some(f(x)),
        MyOption::None => MyOption::None,
    }
}

fn main() {
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

// Prusti glue for Option<i32>
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
