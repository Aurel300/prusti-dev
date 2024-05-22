use prusti_interface::specs::{
    specifications::{SpecQuery, Specifications},
    typed::{DefSpecificationMap, ProcedureSpecification, SpecificationItem},
};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::VirCtxt;

pub struct SpecEnc;

pub type SpecEncError = ();

#[derive(Clone, Debug)]
pub struct SpecEncOutput<'vir> {
    //pub expr: vir::Expr<'vir>,
    pub pres: &'vir [DefId],
    pub posts: &'vir [DefId],
}

pub fn with_proc_spec<'tcx, F, R>(query: SpecQuery<'tcx>, f: F) -> Option<R>
where
    F: FnOnce(&ProcedureSpecification) -> R,
{
    vir::with_vcx(|vcx| {
        let specs = vcx.specs.as_ref().unwrap();
        specs
            .borrow_mut()
            .get_and_refine_proc_spec(vcx.tcx(), query)
            .map(f)
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpecEncTask {
    pub def_id: DefId, // ID of the function
                       // TODO: substs here?
}

impl TaskEncoder for SpecEnc {
    task_encoder::encoder_cache!(SpecEnc);

    type TaskDescription<'vir> = SpecEncTask;

    type TaskKey<'vir> = (
        DefId, // ID of the function
    );

    type OutputFullLocal<'vir> = SpecEncOutput<'vir>;

    type EncodingError = SpecEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        (
            // TODO
            task.def_id,
        )
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let (pres, posts) = with_proc_spec(
                SpecQuery::GetProcKind(
                    task_key.0,
                    ty::List::identity_for_item(vcx.tcx(), task_key.0),
                ),
                |specs| {
                    // TODO: handle specs other than `empty_or_inherent`
                    let pres = get_spec_def_ids(vcx, &specs.pres);
                    let posts = get_spec_def_ids(vcx, &specs.posts);
                    (pres, posts)
                },
            )
            .unwrap_or((&[], &[]));
            Ok((SpecEncOutput { pres, posts }, ()))
        })
    }
}

fn get_spec_def_ids<'vir>(vcx: &'vir VirCtxt<'_>, spec: &SpecificationItem<Vec<DefId>>) -> &'vir [DefId] {
    match spec {
        SpecificationItem::Inherent(ids) | SpecificationItem::Inherited(ids) => {
            vcx.alloc_slice(&ids)
        }
        SpecificationItem::Empty => &[],
        other => todo!("{other:?}"),
    }
}
