// a Box behind a mutable reference should trigger an unfold
fn test(x: &mut Box<i32>) -> i32{
  let res = (**x);
  res
}

// a Box behind a mutable reference should trigger no unfold and use purely snapshot representations
fn test2(x: &Box<i32>) -> i32{
  let res = (**x);
  res
}