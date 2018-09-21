// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(nll)]
#![feature(box_syntax)]

#[macro_use]
extern crate log;
extern crate prusti_interface;
extern crate prusti_filter;
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_mir;
extern crate syntax;
extern crate syntax_pos;
extern crate uuid;
extern crate viper;

mod encoder;
mod utils;
pub mod verifier;