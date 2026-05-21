struct Wrap(i32);
impl Wrap {
    fn get(&self) -> i32 {
        self.0
    }
}
const ARR: [Wrap; 3] = [Wrap(1), Wrap(2), Wrap(3)];

fn test_const_multi_use() {
    // A single textual reference (`ARR[1].get()`) lowers to multiple MIR
    // statements that each emit a ConstOperand for `ARR` with the same source span.
    let _ = ARR[1].get();
}

fn test() {
    // Same macro invoked twice: identical macro-definition span across calls.
    assert_eq!([1, 2, 3], [1, 2, 3]);
    assert_eq!([4, 5, 6], [4, 5, 6]);
    // Nested array literal: recursive emissions inside one task share the span.
    assert_eq!([[1, 2], [3, 4]], [[1, 2], [3, 4]]);
}
