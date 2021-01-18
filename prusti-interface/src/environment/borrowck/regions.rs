// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

///! Code for finding `rustc::ty::sty::RegionVid` associated with local
///! reference typed variables.

use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::BufRead;
use std::path::Path;

use log::debug;
use log::trace;
use regex::Regex;

use rustc_index::vec::Idx;
use rustc_middle::mir;

use crate::environment::borrowck::facts;

lazy_static! {
    static ref FN_SIG: Regex =
        Regex::new(r"^fn [a-zA-Z\d_]+\((?P<args>.*)\) -> (?P<result>.*)\{$").unwrap();

    static ref ARG: Regex =
        Regex::new(r"^_(?P<local>\d+): &'_#(?P<rvid>\d+)r (mut)? [a-zA-Z\d_]+\s*$").unwrap();

    static ref LOCAL: Regex =
        Regex::new(r"let( mut)? _(?P<local>\d+): &'_#(?P<rvid>\d+)r ").unwrap();

    static ref LOCAL_TUPLE: Regex =
        Regex::new(r"let( mut)? _(?P<local>\d+): \((?P<items>.*)\);").unwrap();

    static ref REF: Regex = Regex::new(r"&'_#(?P<rvid>\d+)r ").unwrap();
}
lazy_static! {
    static ref BLOCK: Regex = Regex::new(r"bb(?P<index>\d+)( \([a-z_]+\))?: \{$").unwrap();
}

#[derive(Debug, Hash, PartialEq, Eq)]
enum PlaceRegionProjection {
    Field(usize),
    Deref,
}

#[derive(Debug)]
pub struct PlaceRegions {
    locals: HashMap<(mir::Local, Vec<PlaceRegionProjection>), facts::Region>,
    //derefs: HashMap<(mir::Local, Vec<PlaceRegionProjection>, usize), facts::Region>,
}

#[derive(Clone, Debug)]
pub enum PlaceRegionsError {
    Unsupported(String),
}

// FIXME: (Aurel) hashmaps for all possible projections found in NLL facts are
// probably an overkill. According to the docs of [mir::ProjectionElem], the
// only projection kind that can refer to a different region is [Deref]. It
// should therefore be enough to store a map of Local -> Region instead of the
// current [locals] map.
// FIXME: currently, Deref parsing is not implemented; it should store the
// projection in addition to the block index (better yet mir::Location if it
// can be parsed accurately) mapping to regions.
impl PlaceRegions {
    fn new() -> Self {
        Self {
            locals: HashMap::new(),
        }
    }

    fn add_local(&mut self, local: mir::Local, rvid: facts::Region) {
        self.add(local, vec![], rvid);
    }

    fn add(&mut self, local: mir::Local, projections: Vec<PlaceRegionProjection>, rvid: facts::Region) {
        self.locals.insert((local, projections), rvid);
    }

    pub fn for_local(&self, local: mir::Local)-> Option<facts::Region> {
        self.for_place(local.into()).unwrap()
    }

    /// Determines the region of a MIR place. Right now, the only supported
    /// places are locals, tuples, and some dereferences. Tuples cannot be
    /// nested inside other tuples.
    pub fn for_place(&self, place: mir::Place)
        -> Result<Option<facts::Region>, PlaceRegionsError>
    {
        let (local, fields) = Self::translate_place(place)?;
        Ok(self.locals.get(&(local, fields)).cloned())
    }

    /// Translates a place like _3.0.1 into a local (here _3) and a list of
    /// field projections (like [Field(0), Field(1)]).
    fn translate_place(place: mir::Place)
        -> Result<(mir::Local, Vec<PlaceRegionProjection>), PlaceRegionsError>
    {
        let indices = place.projection.iter()
            .map(|elem| match elem {
                mir::ProjectionElem::Field(f, _) => Ok(PlaceRegionProjection::Field(f.index())),
                mir::ProjectionElem::Deref => Ok(PlaceRegionProjection::Deref),
                x => {
                    return Err(PlaceRegionsError::Unsupported(format!(
                        "determining the region of {:?} is not supported",
                        x,
                    )));
                }
            })
            .collect::<Result<_, _>>()?;
        Ok((place.local, indices))
    }
}

pub fn load_place_regions(path: &Path) -> io::Result<PlaceRegions> {
    trace!("[enter] load_place_regions(path={:?})", path);
    let mut place_regions = PlaceRegions::new();
    let file = File::open(path)?;
    let mut bb = usize::MAX;
    for line in io::BufReader::new(file).lines() {
        let line = line?;
        block_index(&mut bb, &line);
        regions_for_fn_sig(&mut place_regions, &line);
        regions_for_local_ref(&mut place_regions, &line);
        regions_for_local_tuple(&mut place_regions, &line)
    }
    trace!("[exit] load_place_regions");
    Ok(place_regions)
}

fn block_index(bb: &mut usize, line: &String) {
    if let Some(caps) = BLOCK.captures(&line) {
        debug!("block {}", &caps["index"]);
        *bb = caps["index"].parse().unwrap();
    }
}

/// This loads regions for parameters and return values in function signatures.
fn regions_for_fn_sig(place_regions: &mut PlaceRegions, line: &String) {
    if let Some(caps) = FN_SIG.captures(&line) {
        debug!("args: {} result: {}", &caps["args"], &caps["result"]);
        for arg_str in (&caps["args"]).split(", ") {
            if let Some(arg_caps) = ARG.captures(arg_str) {
                debug!("arg {} rvid {}", &arg_caps["local"], &arg_caps["rvid"]);
                let local_arg: usize = (&arg_caps["local"]).parse().unwrap();
                let rvid: usize = (&arg_caps["rvid"]).parse().unwrap();
                place_regions.add_local(mir::Local::new(local_arg), rvid.into());
            }
        }
    }
}

/// This loads regions for reference-typed local variables. For a local variable declaration like
///   let _3: &'2rv mut i32;
/// it would record that the place _3 has region 2.
fn regions_for_local_ref(place_regions: &mut PlaceRegions, line: &String) {
    if let Some(local_caps) = LOCAL.captures(&line) {
        debug!(
            "local {} rvid {}",
            &local_caps["local"], &local_caps["rvid"]
        );
        let local_arg: usize = (&local_caps["local"]).parse().unwrap();
        let rvid: usize = (&local_caps["rvid"]).parse().unwrap();
        place_regions.add_local(mir::Local::new(local_arg), rvid.into());
    }
}

/// This loads regions for tuples. For a local variable declaration like
/// ```ignore
/// let _5: (&'6rv mut i32, &'7rv mut i32);
/// ```
/// it would record that the place _5.0 has region 6 and the place _5.1 has region 7.
fn regions_for_local_tuple(place_regions: &mut PlaceRegions, line: &String) {
    if let Some(m) = LOCAL_TUPLE.captures(&line) {
        let local = mir::Local::new(m["local"].parse().unwrap());
        let items = &m["items"];
        for (i, m) in REF.captures_iter(&items).enumerate() {
            let rvid: usize = m["rvid"].parse().unwrap();
            place_regions.add(local, vec![PlaceRegionProjection::Field(i)], rvid.into());
        }
    }
}
