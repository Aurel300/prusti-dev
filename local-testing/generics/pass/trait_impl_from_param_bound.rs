use prusti_contracts::*;

fn f<T: Clone + Eq>(x: T) {
    g(x)
}

fn g<T: Clone>(t: T) {

}

fn main() {
}
