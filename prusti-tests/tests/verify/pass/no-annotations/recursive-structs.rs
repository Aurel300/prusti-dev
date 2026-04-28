struct A<K, V> {
    k: K,
    v: V,
    link: Option<*const B<K, V>>,
}
struct B<K, V> {
    data: A<K, V>,
}
fn main() {
    let _: A<i32, bool> = A { k: 0, v: false, link: None };
}
