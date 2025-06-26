/*use prusti_contracts::*;*/

/*#[pure]*/
/*#[trusted]*/
fn size_of<T>() -> usize {
    std::mem::size_of::<T>()
}

fn test1() {
    /*assert*/drop(size_of::<u32>() == size_of::<u8>());   // ERRXR: the asserted expression might not hold
}

/*#[requires(size_of::<u32>() == size_of::<u8>())]*/
fn call<T>(_x: T) {}

fn test2() {
    call(4usize);   // ERRXR: precondition might not hold
}

struct S<G> {
    f: G
}

impl<H> S<H> {
    /*#[pure]*/
    /*#[trusted]*/
    fn size_of2(&self) -> usize {
        std::mem::size_of::<H>()
    }
}

fn test3() {
    let s1 = S { f: 3u32 };
    let s2 = S { f: 3u64 };
    /*assert*/drop(s1.size_of2() == s2.size_of2());    // ERRXR: the asserted expression might not hold
}

fn main() {}
