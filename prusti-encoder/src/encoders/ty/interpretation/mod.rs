use vir::{AdtDestructorData, CompType, FunctionIdn};

pub mod bitvec;
pub mod float;
pub mod int;
pub mod real;

#[derive(Debug, Clone, Copy)]
pub struct TyPrimLocal<'vir, T: CompType> {
    pub prim_to_snap: FunctionIdn<'vir, T, vir::CSnap>,
    pub snap_to_prim: &'vir AdtDestructorData<'vir, vir::CSnap, T>,
}
