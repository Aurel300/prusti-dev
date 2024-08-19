struct A;
struct B;
impl A {
    fn foo(&self) -> i32 {
        42
    }
}

impl B {
    fn foo(&self) -> i32 {
        52
    }
}

fn main(){}
