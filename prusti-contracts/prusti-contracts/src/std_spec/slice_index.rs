use crate::*;
use std::slice::SliceIndex;

#[extern_spec]
pub unsafe trait SliceIndex<T>
where
    T: ?Sized,
{
    #[trusted]
    #[pure]
    fn index(self, slice: &T) -> &Self::Output;
}
