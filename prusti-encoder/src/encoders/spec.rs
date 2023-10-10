use prusti_interface::specs::typed::{DefSpecificationMap, SpecificationItem};
use prusti_rustc_interface::span::def_id::DefId;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};

pub struct SpecEncoder;

pub type SpecEncoderError = ();

#[derive(Clone, Debug)]
pub struct SpecEncoderOutput<'vir> {
    //pub expr: vir::Expr<'vir>,
    pub pres: &'vir [DefId],
    pub posts: &'vir [DefId],
}

use std::cell::RefCell;
thread_local! {
    static DEF_SPEC_MAP: RefCell<Option<DefSpecificationMap>> = RefCell::new(Default::default());
    static CACHE: task_encoder::CacheStaticRef<SpecEncoder> = RefCell::new(Default::default());
}

fn with_def_spec<F, R>(f: F) -> R
where
    F: FnOnce(&DefSpecificationMap) -> R,
{
    DEF_SPEC_MAP.with_borrow(|def_spec: &Option<DefSpecificationMap>| {
        let def_spec = def_spec.as_ref().unwrap();
        f(def_spec)
    })
}

pub fn init_def_spec(def_spec: DefSpecificationMap) {
    DEF_SPEC_MAP.replace(Some(def_spec));
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpecEncoderTask {
    pub def_id: DefId, // ID of the function
    // TODO: substs here?
}

impl TaskEncoder for SpecEncoder {
    type TaskDescription<'vir> = SpecEncoderTask;

    type TaskKey<'vir> = (
        DefId, // ID of the function
    );

    type OutputFullLocal<'vir> = SpecEncoderOutput<'vir>;

    type EncodingError = SpecEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
       where F: FnOnce(&'vir task_encoder::CacheRef<'vir, SpecEncoder>) -> R,
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

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        deps.emit_output_ref::<Self>(task_key.clone(), ());
        vir::with_vcx(|vcx| {
            with_def_spec(|def_spec| {
                let specs = def_spec.get_proc_spec(&task_key.0);
                if let Some(specs) = specs {
                    Ok((
                        // QUESTION: Is this correct what i am doing here?
                        SpecEncoderOutput {
                            pres: match &specs.base_spec.pres {
                                SpecificationItem::Inherent(inh) => vcx.alloc_slice(inh),
                                SpecificationItem::Empty => &[],
                                _ => todo!(),
                            },
                            posts: match &specs.base_spec.posts {
                                SpecificationItem::Inherent(inh) => vcx.alloc_slice(inh),
                                SpecificationItem::Empty => &[],
                                _ => todo!(),
                            },
                        },
                        (),
                    ))
                } else {
                    Ok((
                        SpecEncoderOutput {
                            pres: &[],
                            posts: &[],
                        },
                        (),
                    ))
                }
            })
        })
    }
}
