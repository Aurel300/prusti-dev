fn test() {
    let mut idx: usize = 0;
    let length: usize = 10;;
    while idx < length {
        loop_invariant!(idx <= length);
        idx += 1;
    }
}

fn main() {
    test();
}