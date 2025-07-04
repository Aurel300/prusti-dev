fn test() {
    let mut idx: usize = 0;
    let length: usize = 10;;
    while idx < length {
        loop_invariant!(idx <= length);
        loop_invariant!(0 <= length);
        idx += 1;
        let mut jdx: usize = 0;
        let inner_length: usize = 5;
        while jdx < inner_length {
                loop_invariant!(jdx <= inner_length);
                jdx += 1;
            }
    }
}

fn main() {
    test();
}