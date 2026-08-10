fn test() {
    let boxed_array: Box<[i32; 3]> = Box::new([1, 2, 3]);
    let boxed_slice: Box<[i32]> = boxed_array;
    let len = boxed_slice.len();
}