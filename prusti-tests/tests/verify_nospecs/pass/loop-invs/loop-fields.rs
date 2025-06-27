/*use prusti_contracts::*;*/

struct T {
    f: u32,
}

struct H {
    g: T,
}

/*#[requires(a.g.f < 5)]*/
/*#[ensures(result.f == 5)]*/
fn test1(a: H) -> T {
    let mut a = a;
    let mut cont = true;
    while cont {
        /*body_invariant*/drop(a.g.f < 5);
        /*body_invariant*/drop(cont == (a.g.f < 5));
        a.g.f += 1;
        cont = a.g.f < 5;
    }
    a.g
}

fn main() {}
