fn foo(x: i32, y: i32, guard: bool) {
    let mut z = x + y;

    if guard {
        z = 100;
    }

    // later...

    if guard {
        /*assert*/drop(z == 100);
    } else {
        /*assert*/drop(z - x == y);
    }
}

fn main() {
    let x = 10;
    let y = 10;
    /*debug_assert*/drop(x + y == 20);
}
