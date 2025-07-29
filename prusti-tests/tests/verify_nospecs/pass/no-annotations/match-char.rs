fn main() {
    let mut x = 'a';
    x = 'x';
    match x {
        'a' => /*assert*/drop(false),
        'b' => /*assert*/drop(false),
        'z' => /*assert*/drop(false),
        'x' => {} // Ok
        _ => {}/*unimplemented!(),*/
    }
}
