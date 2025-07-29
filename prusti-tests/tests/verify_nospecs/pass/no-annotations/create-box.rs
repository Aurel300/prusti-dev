//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(box_patterns)]

fn use_box(v: i32) -> Box<i32> {
    let x = Box::new(v);
    let y = *x;
    /*assert*/drop(v == y);
    let z = Box::new(y);
    /*assert*/drop(v == *z);
    Box::new(*z)
}

fn main() {}
