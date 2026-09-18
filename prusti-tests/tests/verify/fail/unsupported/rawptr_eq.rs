fn foo() {
    let mut x = 5;
    let y = &raw mut x;
    let z = &raw mut x;

    assert_ne!(y, z); //~ERROR: verification error
}
