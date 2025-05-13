use prusti_rustc_interface::span::def_id::DefId;
use prusti_interface::specs::typed::ProcedureSpecification;
use crate::encoders::spec::{with_proc_spec, with_def_spec};

pub(crate) fn is_function_trusted(def_id: DefId) -> bool {
    with_proc_spec(def_id, |def_spec: &ProcedureSpecification| {
        def_spec.trusted.extract_inherit().unwrap_or_default()
    })
    .unwrap_or_default()
}

pub(crate) fn is_adt_trusted(def_id: DefId) -> bool {
    with_def_spec(|def_spec| 
        def_spec.get_type_spec(&def_id)
            .map(|type_spec| type_spec.trusted.extract_inherit().unwrap_or_default())
            .unwrap_or_default()
    )
}
