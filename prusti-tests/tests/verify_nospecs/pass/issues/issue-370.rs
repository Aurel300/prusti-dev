/*use prusti_contracts::*;*/

/*#[trusted]*/
fn random() -> Option<usize> {
    None/*unimplemented!()*/
}

fn test() {
    loop {
        match random() {
            Some(_) => return,
            None => {}
        }
    }
}

fn main() {}
