// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::acc_or_pred::*;
use encoder::vir;
use encoder::vir::utils::ExprIterator;
use std::collections::HashSet;
use std::iter::FromIterator;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    acc: HashSet<vir::Place>,
    pred: HashSet<vir::Place>,
}

impl State {
    pub fn new(acc: HashSet<vir::Place>, pred: HashSet<vir::Place>) -> Self {
        State {
            acc,
            pred
        }
    }

    pub fn check_consistency(&self) {
        for place in &self.pred {
            if !self.contains_acc(place) {
                panic!(
                    "Consistency error: state has pred {}, but not acc {}",
                    place,
                    place
                );
            }
        }
        for place in &self.acc {
            if !place.is_base() {
                if !self.contains_acc(place.parent().unwrap()) {
                    panic!(
                        "Consistency error: state has acc {}, but not acc {}",
                        place,
                        place.parent().unwrap()
                    );
                }
            }
        }
        for place in &self.pred {
            for other_place in &self.pred {
                if place.has_proper_prefix(other_place) {
                    panic!(
                        "Consistency error: state has pred {}, but also pred {}",
                        place,
                        other_place
                    );
                }
            }
        }
        for acc_place in &self.acc {
            for pred_place in &self.pred {
                if acc_place.has_proper_prefix(pred_place) {
                    panic!(
                        "Consistency error: state has acc {}, but also pred {}",
                        acc_place,
                        pred_place
                    );
                }
            }
        }
    }

    pub fn acc(&self) -> &HashSet<vir::Place> {
        &self.acc
    }

    pub fn pred(&self) -> &HashSet<vir::Place> {
        &self.pred
    }

    pub fn find<P>(&self, pred: P) -> Option<AccOrPred> where P: Fn(&vir::Place) -> bool {
        match self.acc.iter().find(|p| pred(p)).map(|p| AccOrPred::Acc(p.clone())) {
            Some(x) => Some(x),
            None => self.pred.iter().find(|p| pred(p)).map(|p| AccOrPred::Pred(p.clone()))
        }
    }

    pub fn set_acc(&mut self, acc: HashSet<vir::Place>) {
        self.acc = acc
    }

    pub fn set_pred(&mut self, pred: HashSet<vir::Place>) {
        self.pred = pred
    }

    pub fn contains(&self, item: &AccOrPred) -> bool {
        match item {
            &AccOrPred::Acc(ref place) => self.contains_acc(&place),
            &AccOrPred::Pred(ref place) => self.contains_pred(&place),
        }
    }

    pub fn contains_acc(&self, place: &vir::Place) -> bool {
        self.acc.contains(&place)
    }

    pub fn contains_pred(&self, place: &vir::Place) -> bool {
        self.pred.contains(&place)
    }

    pub fn contains_all<'a, I>(&mut self, mut items: I) -> bool where I: Iterator<Item = &'a AccOrPred> {
        items.all(|x| self.contains(x))
    }

    pub fn is_proper_prefix_of_some_pred(&self, prefix: &vir::Place) -> bool {
        for place in &self.pred {
            if place.has_proper_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_proper_prefix_of_some_acc(&self, prefix: &vir::Place) -> bool {
        for place in &self.acc {
            if place.has_proper_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn intersect_acc(&mut self, other_acc: &HashSet<vir::Place>) {
        self.acc = HashSet::from_iter(self.acc.intersection(other_acc).cloned());
    }

    pub fn intersect_pred(&mut self, other_pred: &HashSet<vir::Place>) {
        self.pred = HashSet::from_iter(self.pred.intersection(other_pred).cloned());
    }

    pub fn remove_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.remove_acc_matching(|x| pred(x));
        self.remove_pred_matching(|x| pred(x));
    }

    pub fn remove_acc_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.acc.retain(|e| !pred(e));
    }

    pub fn remove_pred_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.pred.retain(|e| !pred(e));
    }

    pub fn display_acc(&self) -> String {
        self.acc.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_pred(&self) -> String {
        self.pred.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_acc(&self) -> String {
        self.acc.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_pred(&self) -> String {
        self.pred.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn insert_acc(&mut self, place: vir::Place) {
        self.acc.insert(place);
    }

    pub fn insert_all_acc<I>(&mut self, items: I) where I: Iterator<Item = vir::Place> {
        for item in items {
            self.insert_acc(item);
        }
    }

    pub fn insert_all_pred<I>(&mut self, items: I) where I: Iterator<Item = vir::Place> {
        for item in items {
            self.insert_pred(item);
        }
    }

    pub fn insert_pred(&mut self, place: vir::Place) {
        self.pred.insert(place);
    }

    pub fn insert(&mut self, item: AccOrPred) {
        match item {
            AccOrPred::Acc(place) => self.acc.insert(place),
            AccOrPred::Pred(place) => self.pred.insert(place),
        };
    }

    pub fn insert_all<I>(&mut self, items: I) where I: Iterator<Item = AccOrPred> {
        for item in items {
            self.insert(item);
        }
    }

    pub fn remove_acc(&mut self, place: &vir::Place) {
        //assert!(self.acc.contains(place), "Place {} is not in state (acc), so it can not be removed.", place);
        self.acc.remove(place);
    }

    pub fn remove_pred(&mut self, place: &vir::Place) {
        //assert!(self.pred.contains(place), "Place {} is not in state (pred), so it can not be removed.", place);
        self.pred.remove(place);
    }

    pub fn remove(&mut self, item: &AccOrPred) {
        match item {
            &AccOrPred::Acc(ref place) => self.remove_acc(place),
            &AccOrPred::Pred(ref place) => self.remove_pred(place)
        }
    }

    pub fn remove_all<'a, I>(&mut self, items: I) where I: Iterator<Item = &'a AccOrPred> {
        for item in items {
            self.remove(item);
        }
    }

    pub fn as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];
        for place in &self.acc {
            if !place.is_base() {
                exprs.push(
                    vir::Expr::FieldAccessPredicate(
                        box place.clone().into(),
                        vir::Perm::full()
                    )
                );
            }
        }
        for place in &self.pred {
            if let Some(pred_name) = place.typed_ref_name() {
                exprs.push(
                    vir::Expr::PredicateAccessPredicate(
                        box vir::Expr::PredicateAccess(pred_name, vec![ place.clone().into() ]),
                        vir::Perm::full()
                    )
                );
            }
        }
        exprs.into_iter().conjoin()
    }

}
