use prusti_contracts::*;

trait CoerceTo<T> {
    fn coerce_to(self) -> T;
}

impl CoerceTo<u64> for u32 {
    fn coerce_to(self) -> u64 {
        1
    }
}

trait ToBool {
    fn to_bool(self) -> bool;
}

impl <T: ToBool> CoerceTo<bool> for T {
    fn coerce_to(self) -> bool {
        self.to_bool()
    }
}

impl ToBool for bool {
    fn to_bool(self) -> bool {
        self
    }
}

fn main() {
    let x: u32 = 1;
    let y: u64 = x.coerce_to();
    let z: bool = true.coerce_to();
}
