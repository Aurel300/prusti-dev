#![feature(attr_literals)]

// ignore-test The shafe of the CFG of a loop is not supported

extern crate prusti_contracts;

pub struct VecWrapper<T> {
    v: Vec<T>,
}

impl<T: Eq> VecWrapper<T> {
    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires("0 <= index && index < self.len()")]
    pub fn present(&self, index: usize, value: &T) -> bool {
        self.v[index] == *value
    }
}

pub enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    pub fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            UsizeOption::Some(_) => false,
            UsizeOption::None => true,
        }
    }
}

#[ensures("result.is_none() ==>
            (forall k: usize :: (0 <= k && k < arr.len()) ==> !arr.present(k, elem))")]
#[ensures("match result {
                UsizeOption::Some(index) => (
                    0 <= index && index < arr.len() && arr.present(index, elem)
                ),
                UsizeOption::None => true,
            }")]
fn linear_search<T: Eq>(arr: &VecWrapper<T>, elem: &T) -> UsizeOption {
    let mut i = 0;
    let mut done = false;

    #[invariant("i <= arr.len()")]
    #[invariant("forall k: usize :: (0 <= k && k < i) ==> !arr.present(k, elem)")]
    #[invariant("done ==> (i < arr.len() && arr.present(i, elem))")]
    while i < arr.len() && !done { //~ ERROR
        if arr.present(i, elem) {
            done = true;
        } else {
            i += 1;
        }
    }

    if done {
        UsizeOption::Some(i)
    } else {
        UsizeOption::None
    }
}

fn main() {}