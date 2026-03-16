trait MyTrait {}

struct S { x: i32 }

impl MyTrait for S {}

fn consume(_v: &dyn MyTrait) {}

fn consume2(_v: &mut dyn MyTrait) {}
