use prusti_contracts::*;

// ignore-test
// TODO: higher-order closures, opaque types

fn factory(a: bool) -> impl Fn() -> i32 {
  return move || -> i32 {
    if a {
      1
    } else {
      2
    }
  }
}

fn main() {}
