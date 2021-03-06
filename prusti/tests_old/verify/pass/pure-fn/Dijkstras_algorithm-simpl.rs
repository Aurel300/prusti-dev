//! An adaptation of the example from
//! https://rosettacode.org/wiki/Dijkstra%27s_algorithm#Rust

extern crate prusti_contracts;

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::usize;


struct VecWrapperNode{}

impl VecWrapperNode {
    #[pure]
    pub fn len(&self) -> usize {
        5
    }

}

struct Grid {
    nodes: VecWrapperNode,
}

impl Grid {
    fn find_path(&mut self){
        #[invariant="self.nodes.len() >= 0"]
        while true {}
    }
}

fn main() {}
