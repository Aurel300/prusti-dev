
fn f(x: &mut i32, y: &mut i32, z: &mut i32) {
    let old_y = *y;
    *x = 1;
    assert!(*y == old_y);
}

fn main(){}
