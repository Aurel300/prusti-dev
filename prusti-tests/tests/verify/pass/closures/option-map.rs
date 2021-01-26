use prusti_contracts::*;

enum MyOption {
    None,
    Some(i32),
}

impl MyOption {
    #[pure]
    fn is_some(&self) -> bool {
        matches!(self, MyOption::Some(_))
    }

    #[requires(
        f |=! |arg: i32| [ requires(arg == match self {
            MyOption::Some(n) => n,
            MyOption::None => unreachable!(),
        }) ]
    )]
    #[trusted]
    fn map<F: FnMut(i32) -> i32>(self, f: &mut F) -> MyOption {
        match self {
            MyOption::Some(x) => MyOption::Some(f(x)),
            MyOption::None => MyOption::None,
        }
    }
}

fn main() {
    let x = MyOption::Some(5);
    // let x = MyOption::None; // crashes, see #362

    let mut cl = closure!(
        #[requires(i > 4)]
        |i: i32| -> i32 { i + 1 }
    );

    x.map(&mut cl);
}
