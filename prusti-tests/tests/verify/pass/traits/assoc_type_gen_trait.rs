
fn foo<Y: MyTrait<X>, X> (x: Y::SomeType) {

}

trait MyTrait<T> {
    type SomeType;
}

struct St1{}
struct St2{}

impl<T> MyTrait<T> for St1 {
    type SomeType = T;
}

impl<T> MyTrait<T> for St2 {
    type SomeType = u64;
}

fn bar() {
    foo::<St1, f32>(5.2);
}
