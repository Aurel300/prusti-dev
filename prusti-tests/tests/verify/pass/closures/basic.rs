use prusti_contracts::*;

#[requires(add |= |a: i32, b: i32| [
    requires(a >= 0),
    requires(b >= 0),
    ensures(result == a + b)
])]
#[ensures(result == 16)]
fn test1<F: FnMut (i32, i32) -> i32>(add: &mut F) -> i32 {
    add(7, 9)
}

fn main() {
    let f = closure!(
        #[ensures(result == i + 1)]
        |i: i32, j: u32| -> i32 { i + 1 }
    );
    let x = f(41, 1);
    assert!(x == 42);

    let mut count = 0;
    let mut other_count = 0;
    let mut add = closure!(
        // TODO: the order or views matters for now
        #[view(count: i32)]
        #[view(other_count: i32)]
        #[requires(a >= 0 && b >= 0)]
        #[ensures(result == a + b)]
        #[ensures(*views.count == old(*views.count) + 1)]
        #[ensures(*views.other_count == old(*views.other_count) + 2)]
        |a: i32, b: i32| -> i32 {
            count += 1;
            other_count += 2;
            a + b
        }
    );
    test1(&mut add);
}
