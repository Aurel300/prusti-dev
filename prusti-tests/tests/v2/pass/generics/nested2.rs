<<<<<<< HEAD:prusti-tests/tests/v2/pass/generics/nested2.rs
/*struct R(Option<Box<u32>>);
fn main() {
    match R(None).0 {
        Some(_) => (),
        _ => (),
    }
}*/
struct R(Option<u32>);
=======
struct R(Option<Box<u32>>);
>>>>>>> ide/rewrite-2023-assistant-features:local-testing/generics/nested2.rs
fn main() {
    match R(None).0 {
        Some(_) => (),
        _ => (),
    }
}
