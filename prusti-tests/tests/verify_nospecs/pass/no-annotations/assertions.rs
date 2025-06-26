fn id(x: i32) -> i32 {
    x
}

fn id2(x: (i32, (u32, u64), i8)) -> (i32, (u32, u64), i8) {
    x
}

fn with_assert(x: i32) -> i32 {
    if x == 1 {
        /*assert*/drop(x != 0);
    } else {
        /*debug_assert*/drop(x != 1);
    }
    x
}

fn main() {

}
