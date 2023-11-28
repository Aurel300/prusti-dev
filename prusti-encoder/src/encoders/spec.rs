use prusti_rustc_interface::{
    //middle::{mir, ty},
    span::def_id::DefId,
};
use prusti_interface::specs::typed::{DefSpecificationMap, ProcedureSpecification};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};

pub struct SpecEnc;

pub type SpecEncError = ();

#[derive(Clone, Debug)]
pub struct SpecEncOutput<'vir> {
    //pub expr: vir::Expr<'vir>,
    pub pres: &'vir [DefId],
    pub posts: &'vir [DefId],
}

use std::cell::RefCell;
thread_local! {
    static DEF_SPEC_MAP: RefCell<Option<DefSpecificationMap>> = RefCell::new(Default::default());
    static CACHE: task_encoder::CacheStaticRef<SpecEnc> = RefCell::new(Default::default());
}

pub fn with_def_spec<F, R>(f: F) -> R
where
    F: FnOnce(&DefSpecificationMap) -> R,
{
    DEF_SPEC_MAP.with_borrow(|def_spec: &Option<DefSpecificationMap>| {
        let def_spec = def_spec.as_ref().unwrap();
        f(def_spec)
    })
}

pub fn with_proc_spec<F, R>(def_id: DefId, f: F) -> Option<R>
where
    F: FnOnce(&ProcedureSpecification) -> R,
{
    DEF_SPEC_MAP.with_borrow(|def_spec: &Option<DefSpecificationMap>| {
        let def_spec = def_spec.as_ref().unwrap();
        // TODO: handle `SpecGraph` better than simply taking the `base_spec`
        def_spec.get_proc_spec(&def_id).map(|spec| &spec.base_spec).map(f)
    })
}

pub fn init_def_spec(def_spec: DefSpecificationMap) {
    DEF_SPEC_MAP.replace(Some(def_spec));
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpecEncTask {
    pub def_id: DefId, // ID of the function
    // TODO: substs here?
}

impl TaskEncoder for SpecEnc {
    type TaskDescription<'vir> = SpecEncTask;

    type TaskKey<'vir> = (
        DefId, // ID of the function
    );

    type OutputFullLocal<'vir> = SpecEncOutput<'vir>;

    type EncodingError = SpecEncError;

    fn with_cache<'tcx, 'vir, F, R>(f: F) -> R
       where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, SpecEnc>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        (
            // TODO
            task.def_id,
        )
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        deps.emit_output_ref::<Self>(task_key.clone(), ());
        vir::with_vcx(|vcx| {
            with_def_spec(|def_spec| {
                let specs = def_spec.get_proc_spec(&task_key.0);
                // TODO: handle specs other than `empty_or_inherent`
                let pres = specs
                    .and_then(|specs| specs.base_spec.pres.expect_empty_or_inherent())
                    .map(|specs| vcx.alloc_slice(specs))
                    .unwrap_or_default();
                let posts = specs
                    .and_then(|specs| specs.base_spec.posts.expect_empty_or_inherent())
                    .map(|specs| vcx.alloc_slice(specs))
                    .unwrap_or_default();
                Ok((SpecEncOutput { pres, posts, }, () ))
            })
        })
    }
}
