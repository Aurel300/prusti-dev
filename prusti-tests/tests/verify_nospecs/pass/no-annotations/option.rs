//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(box_patterns)]

fn main() {
    let x = 123;
    let y = Some(x);
    let z = if let Some(zz) = y { zz } else { 0/*panic!()*/ };
    /*assert*/drop(x == z);
}
