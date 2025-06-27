fn test_and() {
    /*assert*/drop(true  & true  == true );
    /*assert*/drop(true  & false == false);
    /*assert*/drop(false & true  == false);
    /*assert*/drop(false & false == false);
}

fn test_or() {
    /*assert*/drop(true  | true  == true );
    /*assert*/drop(true  | false == true );
    /*assert*/drop(false | true  == true );
    /*assert*/drop(false | false == false);
}

fn test_xor() {
    /*assert*/drop(true  ^ true  == false);
    /*assert*/drop(true  ^ false == true );
    /*assert*/drop(false ^ true  == true );
    /*assert*/drop(false ^ false == false);
}

fn main() {}
