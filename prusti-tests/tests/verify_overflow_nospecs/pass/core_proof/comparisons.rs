//
// FIXME: This example requires a large smt_qi_bound_global
// because most of our quantifiers used in background theories are
// reinstantiated on every push/pop cycle performed by Silicon.

/*use prusti_contracts::*;*/

fn test1() {
    let a = 4u32;
    let b = 4u32;
    let c = 5u32;
    /*assert*/drop(a == b);
    /*assert*/drop(a != c);
    /*assert*/drop(!(a == c));
    /*assert*/drop(a < c);
    /*assert*/drop(a <= c);
}

fn main() {}
