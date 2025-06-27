fn main() {
    let mut a = [1, 2, 3];
    a[1] = 23;

    /*assert*/drop(a[0] == 1);
    /*assert*/drop(a[1] == 23);
    /*assert*/drop(a[2] == 3);
}
