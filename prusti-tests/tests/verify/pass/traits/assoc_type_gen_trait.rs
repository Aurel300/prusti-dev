
fn foo<X, Y: MyTrait<X, Z>, Z> (x: Y::SomeType, y: Y::SomeOtherType) {

}

trait MyTrait<T, T2> {
    type SomeType;
    type SomeOtherType;
}

struct St1{}
struct St2{}

impl<T, T2> MyTrait<T, T2> for St1 {
    type SomeType = T;
    type SomeOtherType = T2;
}

impl<T> MyTrait<T, T> for St2 {
    type SomeType = u64;
    type SomeOtherType = T;
}

fn bar() {
    foo::<f32, St1, u32>(5.2, 6);
    foo::<bool, St2, bool>(5, false);
}
