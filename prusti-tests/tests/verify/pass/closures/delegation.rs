use prusti_contracts::*;

// From Kassios and Müller (2010)

#[requires(h |=! || [ requires(true) ])]
#[requires(g |=! || [ requires(true) ])]
#[ensures(*y == 4)]
#[ensures(h ~> || {} {})]
#[ensures(g ~> || {} {})]
fn f<T: FnMut() -> i32, U: FnMut() -> i32>(
    y: &mut i32,
    h: &mut T,
    g: &mut U,
) {
    let mut x = 3;
    *y = 4;
    h();
    g();
}

fn main() {
    let mut h = closure!(|| -> i32 { 0 });

    let mut x = 42;
    let mut g = closure!(
        #[view(x: i32)]
        #[ensures(*views.x == old(*views.x) + 1)]
        || -> i32 { x += 1; 0 }
    );

    let mut y = 0;

    f(&mut y, &mut h, &mut g);

    assert!(y == 4);
}
