/// Source: https://carllerche.github.io/mio/src/mio/event_imp.rs.html
/*use prusti_contracts::*;*/

pub struct Token(pub usize);

pub struct Ready(usize);

pub struct Event {
    kind: Ready,
    token: Token
}

pub struct UnixReady(Ready);

/*#[ensures(false)]*/ // ERRXR: postcondition
pub fn kind_mut(event: &mut Event) -> &mut Ready {
    &mut event.kind
}

impl UnixReady {
    /*#[ensures(false)]*/ // ERRXR: postcondition
    fn deref_mut(&mut self) -> &mut Ready {
        &mut self.0
    }
}

fn main() {}
