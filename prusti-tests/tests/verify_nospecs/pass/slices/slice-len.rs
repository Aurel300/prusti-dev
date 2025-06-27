/*use prusti_contracts::*;*/

fn main() {}

/*#[requires(a.len() > 5)]*/
fn slice(a: &[i32]) {
    let s = &a[1..4];
    /*assert*/drop(s.len() == 3);
    let s = &a[..2];
    /*assert*/drop(s.len() == 2);
    let s = &a[1..];
    /*assert*/drop(s.len() == a.len()-1);
    let s = &a[..];
    /*assert*/drop(s.len() == a.len());
    // Unsupported
    //let s = &a[1..=4];
    ///*assert*/drop(s.len() == 4);
    let s = &a[..=4];
    /*assert*/drop(s.len() == 5);
}
