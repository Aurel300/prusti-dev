use prusti_contracts::*;

fn main() {
    let mut cl = closure!(
        #[requires(err < 0 && err > -10000)]
        #[ensures(result == -err)]
        |err: i32| -> i32 { -err }
    );

    assert!(MyResult::Ok(7).unwrap_or_else(&mut cl) == 7);
    assert!(MyResult::Err(-42).unwrap_or_else(&mut cl) == 42);
}

impl MyResult {
    #[requires(
        !self.is_ok() ==>
            f |=! |arg: i32| [ requires(arg == self.unwrap_err()) ]
    )]
    #[ensures(
        old(self.is_ok()) ==> result == old(self.unwrap_ok())
    )]
    #[ensures(
        !old(self.is_ok()) ==>
            f ~>! |arg: i32|
                { arg == old(self.unwrap_err()) }
                { cl_result == result }
    )]
    fn unwrap_or_else<F: FnMut(i32) -> i32>(self, f: &mut F) -> i32 {
        match self {
            MyResult::Ok(x) => x,
            MyResult::Err(x) => f(x),
        }
    }

// Prusti glue for Result<i32, i32>
        #[pure]
        fn is_ok(&self) -> bool {
            match self {
                MyResult::Ok(_) => true,
                MyResult::Err(_) => false,
            }
        }

        #[pure]
        #[requires(self.is_ok())]
        fn unwrap_ok(&self) -> i32 {
            match self {
                MyResult::Ok(val) => *val,
                MyResult::Err(_) => unreachable!(),
            }
        }

        #[pure]
        #[requires(!self.is_ok())]
        fn unwrap_err(&self) -> i32 {
            match self {
                MyResult::Ok(_) => unreachable!(),
                MyResult::Err(err) => *err,
            }
        }
    }

    enum MyResult {
        Ok(i32),
        Err(i32),
    }
// end Prusti glue
