// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::Encoder;
use crate::encoder::places;
use crate::encoder::fn_signatures::{extract_fn_sig, ExtractedFnKind};
use prusti_interface::data::ProcedureDefId;
// use prusti_interface::specifications::{
//     AssertionKind, SpecificationSet, TypedAssertion, TypedExpression, TypedSpecification,
//     TypedSpecificationSet,
// };
use rustc_hir::{self as hir, Mutability};
use rustc_middle::{mir, ty::FnSig, ty::subst::SubstsRef};
use rustc_index::vec::Idx;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeckResults};
// use rustc_data_structures::indexed_vec::Idx;
use std::collections::HashMap;
use std::fmt;
use crate::utils::type_visitor::{self, TypeVisitor};
use prusti_interface::specs::typed;
use log::{trace, debug};
use crate::encoder::errors::EncodingError;
use crate::encoder::errors::EncodingResult;
use crate::encoder::errors::SpannedEncodingResult;

#[derive(Clone, Debug)]
pub struct BorrowInfo<P>
where
    P: fmt::Debug,
{
    /// Region of this borrow. None means static.
    pub region: Option<ty::BoundRegion>,
    pub blocking_paths: Vec<(P, Mutability)>,
    pub blocked_paths: Vec<(P, Mutability)>,
    //blocked_lifetimes: Vec<String>, TODO: Get this info from the constraints graph.
}

impl<P: fmt::Debug> BorrowInfo<P> {
    fn new(region: Option<ty::BoundRegion>) -> Self {
        BorrowInfo {
            region,
            blocking_paths: Vec::new(),
            blocked_paths: Vec::new(),
        }
    }
}

impl<P: fmt::Debug> fmt::Display for BorrowInfo<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lifetime = match self.region {
            None => format!("static"),
            Some(ty::BoundRegion {kind: ty::BoundRegionKind::BrAnon(id)}) => format!("#{}", id),
            Some(ty::BoundRegion {kind: ty::BoundRegionKind::BrNamed(_, name)}) => name.to_string(),
            _ => unimplemented!(),
        };
        writeln!(f, "BorrowInfo<{}> {{", lifetime)?;
        for path in self.blocking_paths.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "  --*")?;
        for path in self.blocked_paths.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "}}")
    }
}

/// Contract of a specific procedure. It is a separate struct from a
/// general procedure info because we want to be able to translate
/// procedure calls before translating call targets.
/// TODO: Move to some properly named module.
/// TODO: perhaps specification does not actually belong to the contract
#[derive(Clone, Debug)]
pub struct ProcedureContractGeneric<'tcx, L, P>
where
    L: fmt::Debug,
    P: fmt::Debug,
{
    /// Definition ID of the procedure to which the contract is attached.
    pub def_id: rustc_hir::def_id::DefId,
    /// Formal arguments for which we should have permissions in the
    /// precondition. This includes both borrows and moved in values.
    /// For example, if `_2` is in the vector, this means that we have
    /// `T(_2)` in the precondition.
    pub args: Vec<L>,
    /// Borrowed arguments that are directly returned to the caller (not via
    /// a magic wand). For example, if `*(_2.1).0` is in the vector, this
    /// means that we have `T(old[precondition](_2.1.ref.0))` in the
    /// postcondition. It also includes information about the mutability
    /// of the original reference.
    pub returned_refs: Vec<(P, Mutability)>,
    /// The returned value for which we should have permission in
    /// the postcondition.
    pub returned_value: L,
    /// Magic wands passed out of the procedure.
    /// TODO: Implement support for `blocked_lifetimes` via nested magic wands.
    pub borrow_infos: Vec<BorrowInfo<P>>,
    /// The functional specification: precondition and postcondition
    pub specification: ProcedureContractSpecification<'tcx>,
}

#[derive(Clone, Debug)]
pub enum ProcedureContractSpecification<'tcx> {
    /// Contract of a procedure or regular procedure call.
    ProcedureSpecification(typed::ProcedureSpecification<'tcx>),
    /// Contract of a closure or closure call.
    ClosureSpecification(typed::ClosureSpecification<'tcx>, ty::Ty<'tcx>),
    /// Contract of an indirect call (Fn*::call).
    SpecFunctions(ty::Ty<'tcx>),
}

impl<'tcx, L: fmt::Debug, P: fmt::Debug> ProcedureContractGeneric<'tcx, L, P> {
    pub fn functional_precondition(&self) -> &[typed::Assertion<'tcx>] {
        match &self.specification {
            ProcedureContractSpecification::ProcedureSpecification(specs) => &specs.pres,
            ProcedureContractSpecification::ClosureSpecification(specs, _) => &specs.proc_spec.pres,
            _ => unreachable!(),
        }
    }

    pub fn functional_postcondition(&self) -> &[typed::Assertion<'tcx>] {
        match &self.specification {
            ProcedureContractSpecification::ProcedureSpecification(specs) => &specs.posts,
            ProcedureContractSpecification::ClosureSpecification(specs, _) => &specs.proc_spec.posts,
            _ => unreachable!(),
        }
    }

    pub fn history_invariant(&self) -> &[typed::Assertion<'tcx>] {
        match &self.specification {
            ProcedureContractSpecification::ClosureSpecification(specs, _) => &specs.invariants,
            _ => &[],
        }
    }

    pub fn pledges(&self) -> &[typed::Pledge<'tcx>] {
        match &self.specification {
            ProcedureContractSpecification::ProcedureSpecification(specs) => &specs.pledges,
            ProcedureContractSpecification::ClosureSpecification(specs, _) => &specs.proc_spec.pledges,
            _ => &[],
        }
    }
}

impl<'tcx> ProcedureContractSpecification<'tcx> {
    pub fn expect_mut_procedure(&mut self) -> &mut typed::ProcedureSpecification<'tcx> {
        match self {
            ProcedureContractSpecification::ProcedureSpecification(specs) => specs,
            ProcedureContractSpecification::ClosureSpecification(specs, _) => &mut specs.proc_spec,
            _ => unreachable!(),
        }
    }
}

/// Procedure contract as it is defined in MIR.
pub type ProcedureContractMirDef<'tcx> = ProcedureContractGeneric<'tcx, mir::Local, mir::Place<'tcx>>;

/// Specialized procedure contract for use in translation.
pub type ProcedureContract<'tcx> = ProcedureContractGeneric<'tcx, places::Local, places::Place<'tcx>>;

impl<L: fmt::Debug, P: fmt::Debug> fmt::Display for ProcedureContractGeneric<'_, L, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "ProcedureContract {{")?;
        writeln!(f, "IN:")?;
        for path in self.args.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "OUT:")?;
        for path in self.returned_refs.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "MAGIC:")?;
        for borrow_info in self.borrow_infos.iter() {
            writeln!(f, "{}", borrow_info)?;
        }
        writeln!(f, "SPECS:")?;
        writeln!(f, "  {:?}", self.specification);
        writeln!(f, "}}")
    }
}

fn get_place_root<'tcx>(place: &mir::Place<'tcx>) -> mir::Local {
    // match place {
    //     &mir::Place::Local(local) => local,
    //     &mir::Place::Projection(ref projection) => get_place_root(&projection.base),
    //     _ => unimplemented!(),
    // }
    place.local
}

impl<'tcx> ProcedureContractMirDef<'tcx> {
    /// Specialize to the definition site contract.
    pub fn to_def_site_contract(&self) -> ProcedureContract<'tcx> {
        let borrow_infos = self
            .borrow_infos
            .iter()
            .map(|info| BorrowInfo {
                region: info.region,
                blocking_paths: info
                    .blocking_paths
                    .iter()
                    .map(|(p, m)| (p.into(), *m))
                    .collect(),
                blocked_paths: info
                    .blocked_paths
                    .iter()
                    .map(|(p, m)| (p.into(), *m))
                    .collect(),
            })
            .collect();
        ProcedureContract {
            def_id: self.def_id,
            args: self.args.iter().map(|&a| a.into()).collect(),
            returned_refs: self
                .returned_refs
                .iter()
                .map(|(r, m)| (r.into(), *m))
                .collect(),
            returned_value: self.returned_value.into(),
            borrow_infos,
            specification: self.specification.clone(),
        }
    }

    /// Specialize to the call site contract.
    pub fn to_call_site_contract(
        &self,
        args: &Vec<places::Local>,
        target: places::Local,
    ) -> ProcedureContract<'tcx> {
        assert_eq!(self.args.len(), args.len());
        let mut substitutions = HashMap::new();
        substitutions.insert(self.returned_value, target);
        for (from, to) in self.args.iter().zip(args) {
            substitutions.insert(*from, *to);
        }
        let substitute = |(place, mutability): &(_, Mutability)| {
            let root = &get_place_root(place);
            let substitute_place = places::Place::SubstitutedPlace {
                substituted_root: *substitutions.get(root).unwrap(),
                place: place.clone(),
            };
            (substitute_place, *mutability)
        };
        let borrow_infos = self
            .borrow_infos
            .iter()
            .map(|info| BorrowInfo {
                region: info.region,
                blocking_paths: info.blocking_paths.iter().map(&substitute).collect(),
                blocked_paths: info.blocked_paths.iter().map(&substitute).collect(),
            })
            .collect();
        let returned_refs = self.returned_refs.iter().map(&substitute).collect();
        let result = ProcedureContract {
            def_id: self.def_id,
            args: args.clone(),
            returned_refs: returned_refs,
            returned_value: target,
            borrow_infos,
            specification: self.specification.clone(),
        };
        result
    }
}

pub struct BorrowInfoCollectingVisitor<'tcx> {
    borrow_infos: Vec<BorrowInfo<mir::Place<'tcx>>>,
    /// References that were passed as arguments. We are interested only in
    /// references that can be blocked.
    references_in: Vec<(mir::Place<'tcx>, Mutability)>,
    tcx: TyCtxt<'tcx>,
    /// Can the currently analysed path block other paths? For return
    /// type this is initially true, and for parameters it is true below
    /// the first reference.
    is_path_blocking: bool,
    current_path: Option<mir::Place<'tcx>>,
}

impl<'tcx> BorrowInfoCollectingVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        BorrowInfoCollectingVisitor {
            borrow_infos: Vec::new(),
            references_in: Vec::new(),
            tcx,
            is_path_blocking: false,
            current_path: None,
        }
    }

    fn analyse_return_ty(&mut self, ty: Ty<'tcx>)
        -> EncodingResult<()>
    {
        self.is_path_blocking = true;
        self.current_path = Some(mir::RETURN_PLACE.into());
        self.visit_ty(ty)?;
        self.current_path = None;
        Ok(())
    }

    fn analyse_arg(&mut self, arg: mir::Local, ty: Ty<'tcx>)
        -> EncodingResult<()>
    {
        self.is_path_blocking = false;
        self.current_path = Some(arg.into());
        self.visit_ty(ty)?;
        self.current_path = None;
        Ok(())
    }

    fn extract_bound_region(&self, region: ty::Region<'tcx>) -> Option<ty::BoundRegion> {
        match region {
            &ty::RegionKind::ReFree(free_region) => Some(ty::BoundRegion {
                kind: free_region.bound_region
            }),
            // TODO: is this correct?!
            &ty::RegionKind::ReLateBound(_, bound_region) => Some(bound_region),
            &ty::RegionKind::ReEarlyBound(early_region) => Some(ty::BoundRegion {
                kind: ty::BoundRegionKind::BrNamed(early_region.def_id, early_region.name)
            }),
            &ty::RegionKind::ReStatic => None,
            &ty::RegionKind::ReErased => None,
            // &ty::RegionKind::ReScope(_scope) => None,
            x => unimplemented!("{:?}", x),
        }
    }

    fn get_or_create_borrow_info(
        &mut self,
        region: Option<ty::BoundRegion>,
    ) -> &mut BorrowInfo<mir::Place<'tcx>> {
        if let Some(index) = self
            .borrow_infos
            .iter()
            .position(|info| info.region == region)
        {
            &mut self.borrow_infos[index]
        } else {
            let borrow_info = BorrowInfo::new(region);
            self.borrow_infos.push(borrow_info);
            self.borrow_infos.last_mut().unwrap()
        }
    }
}

impl<'tcx> TypeVisitor<'tcx> for BorrowInfoCollectingVisitor<'tcx> {
    type Error = EncodingError;

    fn visit_unsupported_sty(
        &mut self,
        sty: &TyKind<'tcx>
    ) -> Result<(), Self::Error> {
        Err(EncodingError::unsupported(
            format!("unsupported type {:?}", sty)
        ))
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_field(
        &mut self,
        index: usize,
        field: &ty::FieldDef,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> Result<(), Self::Error> {
        trace!("visit_field({}, {:?})", index, field);
        let old_path = self.current_path.take().unwrap();
        let ty = field.ty(self.tcx(), substs);
        let field_id = mir::Field::new(index);
        let new_path = self.tcx.mk_place_field(old_path, field_id, ty);
        self.current_path = Some(new_path);
        // self.current_path = Some(old_path.clone().field(field_id, ty));
        type_visitor::walk_field(self, field, substs)?;
        self.current_path = Some(old_path);
        Ok(())
    }

    fn visit_ref(
        &mut self,
        region: ty::Region<'tcx>,
        ty: ty::Ty<'tcx>,
        mutability: hir::Mutability,
    ) -> Result<(), Self::Error> {
        trace!(
            "visit_ref({:?}, {:?}, {:?}) current_path={:?}",
            region,
            ty,
            mutability,
            self.current_path
        );
        let bound_region = self.extract_bound_region(region);
        let is_path_blocking = self.is_path_blocking;
        let old_path = self.current_path.take().unwrap();
        let current_path = self.tcx.mk_place_deref(old_path);
        self.current_path = Some(current_path.clone());
        let borrow_info = self.get_or_create_borrow_info(bound_region);
        if is_path_blocking {
            borrow_info.blocking_paths.push((current_path, mutability));
        } else {
            borrow_info
                .blocked_paths
                .push((current_path.clone(), mutability));
            self.references_in.push((current_path, mutability));
        }
        self.is_path_blocking = true;
        //type_visitor::walk_ref(self, region, ty, mutability)?;
        self.is_path_blocking = is_path_blocking;
        self.current_path = Some(old_path);
        Ok(())
    }

    fn visit_tuple(
        &mut self,
        parts: SubstsRef<'tcx>,
    ) -> Result<(), Self::Error> {
        let old_path = self.current_path.take().unwrap();
        for (i, part) in parts.iter().enumerate() {
            let field = mir::Field::new(i);
            let ty = part.expect_ty();
            self.current_path = Some(
                self.tcx().mk_place_field(old_path.clone(), field, ty)
            );
            self.visit_ty(ty);
        }
        self.current_path = Some(old_path);
        Ok(())
    }

    fn visit_raw_ptr(
        &mut self,
        ty: ty::Ty<'tcx>,
        mutability: hir::Mutability,
    ) -> Result<(), Self::Error> {
        trace!(
            "visit_raw_ptr({:?}, {:?}) current_path={:?}",
            ty,
            mutability,
            self.current_path
        );
        // Do nothing.
        Ok(())
    }
}

pub fn compute_procedure_contract<'p, 'a: 'p, 'tcx: 'a>(
    proc_def_id: ProcedureDefId,
    tcx: TyCtxt<'tcx>,
    specification: typed::SpecificationSet<'tcx>,
    maybe_tymap: Option<&HashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>>,
) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
    trace!("[compute_procedure_contract] enter name={:?}", proc_def_id);
    let args_ty:Vec<ty::Ty<'tcx>>;
    let return_ty;
    let spec;

    if !tcx.is_closure(proc_def_id) {
        // FIXME: "skip_binder" is most likely wrong
        // FIXME: Replace with FakeMirEncoder.
        let fn_sig = tcx.fn_sig(proc_def_id).skip_binder();
        args_ty = fn_sig.inputs().to_vec();
        return_ty = fn_sig.output().clone(); // FIXME: Shouldn't this also go through maybe_tymap?
        spec = ProcedureContractSpecification::ProcedureSpecification(
            specification.expect_procedure().clone(),
        );
    } else {
        // TODO: relying on MIR here is not the best solution; we cannot use
        // tcx.fn_sig(...) because the compiler wants us to do
        // subst.as_closure().sig(), but we have no substs when getting here
        // from the encoder's processing queue.
        let (mir, _) = tcx.mir_promoted(ty::WithOptConstParam::unknown(proc_def_id.expect_local()));
        let mir = mir.borrow();
        // local_decls:
        // _0    - return, with closure's return type
        // _1    - closure's self
        // _2... - actual arguments
        // arg_count includes the extra self _1
        args_ty = (1usize ..= mir.arg_count)
            .map(|i| mir.local_decls[mir::Local::from_usize(i)].ty)
            .collect();
        return_ty = mir.local_decls[mir::Local::from_usize(0)].ty;
        spec = ProcedureContractSpecification::ClosureSpecification(
            specification.expect_closure().clone(),
            args_ty[0],
        );
    }

    compute_procedure_contract_internal(
        proc_def_id,
        args_ty,
        return_ty,
        tcx,
        spec,
        maybe_tymap,
    )
}

pub fn compute_procedure_contract_of_type<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    fn_type: ty::Ty<'tcx>,
    // TODO: should there be a tymap?
    // maybe_tymap: Option<&HashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>>,
) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
    trace!("[compute_procedure_contract] enter type={:?}", fn_type);
    let fn_sig = extract_fn_sig(encoder, fn_type);

    let specification = match fn_sig.kind {
        ExtractedFnKind::FnDef => ProcedureContractSpecification::ProcedureSpecification(
            encoder
                .get_procedure_specs(fn_sig.def_id)
                .unwrap_or_else(|| typed::ProcedureSpecification::empty()),
        ),
        ExtractedFnKind::Closure => ProcedureContractSpecification::ClosureSpecification(
            encoder
                .get_closure_specs(fn_sig.def_id)
                .unwrap_or_else(|| typed::ClosureSpecification::empty()),
            fn_type,
        ),
        ExtractedFnKind::Param => ProcedureContractSpecification::SpecFunctions(fn_type),
    };

    compute_procedure_contract_internal(
        fn_sig.def_id,
        fn_sig.inputs.clone(),
        fn_sig.output,
        encoder.env().tcx(),
        specification,
        None, // maybe_tymap,
    )
}

fn compute_procedure_contract_internal<'p, 'v: 'p, 'tcx: 'v>(
    proc_def_id: ProcedureDefId,
    args_ty: Vec<ty::Ty<'tcx>>,
    return_ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    specification: ProcedureContractSpecification<'tcx>,
    maybe_tymap: Option<&HashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>>,
) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
    let args_ty = args_ty
        .into_iter()
        .enumerate()
        .map(|(arg_num, arg_ty)| (mir::Local::from_usize(arg_num + 1), arg_ty))
        .collect::<Vec<_>>();

    let mut fake_mir_args = Vec::new();
    let mut fake_mir_args_ty = Vec::new();

    for (local, arg_ty) in args_ty {
        fake_mir_args.push(local);
        fake_mir_args_ty.push(if let Some(replaced_arg_ty) = maybe_tymap.and_then(|tymap| tymap.get(arg_ty)) {
            replaced_arg_ty.clone()
        } else {
            arg_ty.clone()
        });
    }

    let mut visitor = BorrowInfoCollectingVisitor::new(tcx);
    for (arg, arg_ty) in fake_mir_args.iter().zip(fake_mir_args_ty) {
        visitor.analyse_arg(*arg, arg_ty)?;
    }
    visitor.analyse_return_ty(return_ty)?;
    let borrow_infos: Vec<_> = visitor
        .borrow_infos
        .into_iter()
        .filter(|info| !info.blocked_paths.is_empty() && !info.blocking_paths.is_empty())
        .collect();
    let is_not_blocked = |place: &mir::Place<'tcx>| {
        !borrow_infos.iter().any(|info| {
            info.blocked_paths
                .iter()
                .any(|(blocked_place, _)| blocked_place == place)
        })
    };
    let returned_refs: Vec<_> = visitor
        .references_in
        .into_iter()
        .filter(|(place, _)| is_not_blocked(place))
        .collect();
    let contract = ProcedureContractGeneric {
        def_id: proc_def_id,
        args: fake_mir_args,
        returned_refs,
        returned_value: mir::RETURN_PLACE,
        borrow_infos,
        specification,
    };

    trace!("[compute_procedure_contract] exit result={}", contract);
    Ok(contract)
}
