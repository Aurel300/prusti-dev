use prusti_contracts::*;

fn main() {
    let mut x = 5;
    let p_x = &raw mut x;
    let p_x = p_x as *mut i8;
    unsafe { *p_x = 6 };
    prusti_assert!(x == 6);
}
