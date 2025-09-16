use prusti_rustc_interface::{middle::ty, span::def_id::DefId};

use crate::encoders::ty::{generics::GParams, LazyRustTy};

pub struct RustSignature<'tcx> {
    pub gparams: GParams<'tcx>,
    pub inputs: &'tcx [LazyRustTy<'tcx>],
    pub output: LazyRustTy<'tcx>,
}

impl<'tcx> RustSignature<'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, def_id: DefId) -> Self {
        let fn_sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        let gparams = GParams::from(def_id);
        let inputs = LazyRustTy::new_slice(fn_sig.inputs());
        let output = LazyRustTy::new(fn_sig.output());
        Self { gparams, inputs, output }
    }
}
