fn main() {
    /*assert*/drop(10 % 3 == 1);
    /*assert*/drop(10 % -3 == 1);
    /*assert*/drop(-10 % 3 == -1); // 2
    /*assert*/drop(-10 % -3 == -1); // 2
    let a = 10;
    let b = 3;
    /*assert*/drop(a % b == 1);

    /*assert*/drop(-4 % 2 == 0);

    /*assert*/drop(3 % 3 == 0);
    /*assert*/drop(2 % 3 == 2);
    /*assert*/drop(1 % 3 == 1);
    /*assert*/drop(0 % 3 == 0);
    /*assert*/drop(-1 % 3 == -1);
    /*assert*/drop(-2 % 3 == -2);
    /*assert*/drop(-3 % 3 == 0);
    /*assert*/drop(-4 % 3 == -1);
    /*assert*/drop(-5 % 3 == -2);
}
