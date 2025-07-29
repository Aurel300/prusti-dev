
/*use prusti_contracts::*;*/

fn main() {}

/*#[requires(a.len() > 5)]*/
fn slice(a: &[i32]) {
    let s = &a[1..4];
    /*assert*/drop(s[0] == a[1]);
    let s = &a[..2];
    /*assert*/drop(s[1] == a[1]);
    let s = &a[1..];
    /*assert*/drop(s[2] == a[3]);
    let s = &a[..];
    /*assert*/drop(s[3] == a[3]);
    // Unsupported
    //let s = &a[1..=4];
    ///*assert*/drop(s[3] == a[4]);
    let s = &a[..=5];
    /*assert*/drop(s[5] == a[5]);
}
