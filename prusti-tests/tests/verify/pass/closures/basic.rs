use prusti_contracts::*;

#[requires(add |= |a: i32, b: i32| [
    requires(a >= 0),
    requires(b >= 0),
    ensures(result == a + b)
])]
#[ensures(result == 16)]
fn test1<F: FnMut (i32, i32) -> i32>(add: &mut F) -> i32 {
    // TODO: higher-order calls cannot be encoded yet
    // add(7, 9)
    16
}

fn main() {
    let f = closure!(
        #[requires(i >= 0)]
        #[ensures(result == i + 1)]
        |i: i32| -> i32 { i + 1 }
    );
    f(0);

    let mut count = 0;
    let mut add = closure!(
        #[view(count: i32, 0)]
        #[requires(a >= 0 && b >= 0)]
        #[ensures(result == a + b)]
        #[ensures(*views.count == old(*views.count) + 1)]
        |a: i32, b: i32| -> i32 {
            count += 1;
            a + b
        }
    );
    test1(&mut add);
}
