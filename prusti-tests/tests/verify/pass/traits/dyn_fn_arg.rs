trait MyTrait {}

struct S { x: i32 }

impl MyTrait for S {}

fn consume(_v: &dyn MyTrait) {}
