use prusti_contracts::*;

fn main() {
    let mut count: i32 = 0;
    let mut cl = closure!(
        #[view(count: i32, 0)]
        #[requires(i != *views.count)]
        #[ensures(*views.count == old(*views.count) + 1)]
        |i: i32| -> i32 {
            let r = i - count;
            count += 1;
            r
        }
    );
    cl(1);
    cl(2);
    cl(1);
    cl(0);
}
