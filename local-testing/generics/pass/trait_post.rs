use prusti_contracts::*;

trait Foo: Sized {
    #[ensures(result == 5)]
    fn baz(self) -> u32;
}

impl Foo for u32 {
    fn baz(self) -> u32 {
        5
    }
}

#[ensures(result == 5)]
fn go<T: Foo>(t: T) -> u32 {
    t.baz()
}

#[ensures(result == 5)]
fn go_int() -> u32 {
   go(1)
}

fn main(){

}
