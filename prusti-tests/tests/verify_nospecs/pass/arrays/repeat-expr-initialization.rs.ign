// this tests
//
// - repeat expressions [{const}; {count}], which look a little different in MIR than regular
//   initializers like [1, 2, 3]
// - bool as element type

fn main() {
    let a = [false; 3];

    /*assert*/drop(a[0] == false);
    /*assert*/drop(a[1] == false);
    /*assert*/drop(a[2] == false);
}
