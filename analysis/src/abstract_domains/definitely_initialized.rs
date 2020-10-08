// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::AbstractState;

pub struct DefinitelyInitializedState {}
impl AbstractState for DefinitelyInitializedState {
    fn join(self, other: Self) -> Self {
        unimplemented!()
    }
}
