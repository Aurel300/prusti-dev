fn foo() {
    let mut x = 5;
    // setting to x2 to 5 is currently incomplete:
    // Viper would have to see that the underlying Refs
    // refer to disjunct heap chunks which we can only do by unfolding the i32 predicates
    let mut x2 = 6;
    let y = &raw mut x;
    let z = &raw mut x2;
    assert_ne!(y, z);
    let z = &raw mut x;
    assert_eq!(y, z);
}
