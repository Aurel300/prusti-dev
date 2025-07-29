fn foo(a: u8, b: i8, c: usize, d: isize) {
    /*assert*///drop(a as char as u8 as u16 as u32 as u64 as u128 == a as u128);
    /*assert*/drop(b as i8 as i16 as i32 as i64 as i128 == b as i128);
    /*assert*///drop(c as usize == c);
    /*assert*///drop(d as isize == d);
}

fn main() {}
