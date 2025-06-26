fn test(x: i32) {
    let is_pos = x.is_positive();
    /*assert*/drop(is_pos); // ERRXR: the asserted expression might not hold
}

fn main(){}
