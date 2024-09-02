use std::collections::{HashMap, HashSet};
use prusti_interface::{PrustiError, environment::EnvDiagnostic};
use prusti_rustc_interface::hir::def_id::LOCAL_CRATE;
use prusti_rustc_interface::span::{
    Span,
    DUMMY_SP,
    source_map::SourceMap,
    def_id::DefId
};
use crate::VirCtxt;
use ide::{SpanOfCallContracts, EncodingInfo};

pub struct VirSpanHandler<'vir> {
    error_kind: &'static str,
    handler: Box<dyn Fn(Option<Span>) -> Option<Vec<PrustiError>> + 'vir>,
    next: Option<Box<VirSpanHandler<'vir>>>,
}

#[derive(Hash)]
pub struct VirSpan<'vir> {
    pub id: usize,
    span: Span,
    parent: Option<&'vir VirSpan<'vir>>,
}

unsafe impl<'vir> Send for VirSpan<'vir> {}
unsafe impl<'vir> Sync for VirSpan<'vir> {}

impl serde::Serialize for VirSpan<'_> {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where S: serde::ser::Serializer
    {
        ser.serialize_u64(self.id as u64)
    }
}
impl<'de> serde::Deserialize<'de> for VirSpan<'_> {
    fn deserialize<D>(deser: D) -> Result<Self, D::Error>
    where D: serde::de::Deserializer<'de>
    {
        let id = u64::deserialize(deser)? as usize;
        Ok(VirSpan {
            id,
            span: Default::default(),
            parent: None,
        })
    }
}

/// The span manager. Maintains a vector of all allocated spans, as well as
/// the stack, used when allocating AST nodes.
#[derive(Default)]
pub struct VirSpanManager<'vir> {
    /// Vector of all allocated spans. The `id` field of a `VirSpan` is an
    /// index into this vector. The same `id` can thus be used as the position
    /// ID given to Viper over JNI, and when backtranslating error positions
    /// can be used to index into this vector again, to find any error
    /// transformers.
    all: Vec<&'vir crate::spans::VirSpan<'vir>>,

    /// Stack of "current" spans. This is maintained such that an encoder can
    /// walk down the MIR primitives recursively, adding their stacks onto the
    /// stack as it works. At the same time, these spans will be linked with
    /// their parent, i.e. the preceding span in the stack. This parent link
    /// can be used during error backtranslation to find the closest ancestor
    /// to an offending node with an error transformer.
    // TODO: it might be good to insert sentinel nodes into the stack whenever
    //   crossing an encoder context (e.g. when a different encoder is used as
    //   part of a `deps.require_*` call) to avoid linking unrelated spans
    //   together
    stack: Vec<&'vir crate::spans::VirSpan<'vir>>,

    handlers: HashMap<usize, VirSpanHandler<'vir>>,

    /// Vector of objects holding for each method call the spans of any 
    /// associated contracts. Intended for consuption by Prusti-Assistant.
    call_contract_spans: Vec<SpanOfCallContracts>,

    /// Map of identifiers composed of a method `DefId` and a label to the
    /// span of the respective block.
    /// Only populated if `GENERATE_BLOCK_MESSAGES` is set.
    block_spans: HashMap<(DefId, String), Span>,

    /// Map of specifically local, non-trusted, selected,
    /// impure method identifier strings to their `DefId`s.
    /// (See `prusti_encoder::ImpureFunctionEnc::encode`)
    /// Used for backtranslation of viper names where the identifier is all to
    /// go off of.
    // TODO: If useful, extend to include other identifiers too. But take care
    // to also change the usage as well - these currently server as a filter
    // for EntitySuccess/FailureMessages in prusti-server's viper backend
    viper_identifiers: HashMap<String, DefId>,

}

impl<'tcx> VirCtxt<'tcx> {
    /// Execute the given function with the given span (temporarily) added to
    /// the span stack.
    pub fn with_span<T>(&'tcx self, span: Span, f: impl FnOnce(&'tcx Self) -> T) -> T {
        let mut manager = self.spans.borrow_mut();
        let span = self.alloc(VirSpan {
            id: manager.all.len(),
            span,
            parent: manager.stack.last().copied(),
        });
        manager.all.push(span);
        manager.stack.push(span);
        let len_before = manager.stack.len();
        drop(manager);
        let res = f(self);
        let mut manager = self.spans.borrow_mut();
        debug_assert_eq!(manager.stack.len(), len_before);
        manager.stack.pop().unwrap();
        res
    }

    /// Add an error handler to the span currently on top of the stack.
    /// `error_kind` is the machine-readable identifier of an error, as
    /// defined by Viper. The handler function should construct one or more
    /// `PrustiError`s to report the error with the correct span etc.
    pub fn handle_error(
        &'tcx self,
        error_kind: &'static str,
        handler: impl Fn(Option<Span>) -> Option<Vec<PrustiError>> + 'tcx,
    ) {
        let top_span_id = self.top_span().unwrap().id;
        let mut manager = self.spans.borrow_mut();
        let previous = manager.handlers.remove(&top_span_id);
        manager.handlers.insert(top_span_id, VirSpanHandler {
            error_kind,
            handler: Box::new(handler),
            next: previous.map(Box::new),
        });
    }

    // TODO: eventually, this should not be an Option
    pub fn top_span(&'tcx self) -> Option<&'tcx VirSpan<'tcx>> {
        self.spans.borrow().stack.last().copied()
    }

    /// Attempt to backtranslate the given error at the given position.
    pub fn backtranslate(
        &'tcx self,
        error_kind: &str,
        offending_pos_id: usize,
        reason_pos_id: Option<usize>,
     ) -> Option<Vec<PrustiError>> {
        let manager = self.spans.borrow();
        let reason_span_opt = reason_pos_id
            .and_then(|id| manager.all.get(id))
            .map(|vir_span| vir_span.span);
        let mut span_opt = manager.all.get(offending_pos_id);
        while let Some(span) = span_opt {
            let mut handler_opt = manager.handlers.get(&span.id);
            while let Some(handler) = handler_opt {
                if handler.error_kind == error_kind {
                    if let Some(errors) = (handler.handler)(reason_span_opt) {
                        return Some(errors);
                    }
                }
                handler_opt = handler.next.as_deref();
            }
            span_opt = span.parent.as_ref();
        }
        None
    }

    /// Attempt to backtranslate a position id to a rust span
    pub fn get_span_from_id(
        &'tcx self,
        pos_id: usize
    ) -> Option<Span> {
        let manager = self.spans.borrow();
        manager.all
            .get(pos_id)
            .map(|vir_span| vir_span.span)
    }

    pub fn viper_to_rust_identifier(
        &'tcx self,
        viper_method: &str,
    ) -> Option<String> {
        self
            .get_viper_identifier(viper_method)
            .map(|def_id|
                self.get_unique_item_name(&def_id)
            )
    }

    /// Get the crate name of `def_id_opt` or the local crate name if it is `None`
    pub fn get_crate_name(
        &'tcx self,
        def_id_opt: Option<DefId>,
    ) -> String {
        def_id_opt.map_or(
            self
                .tcx()
                .crate_name(LOCAL_CRATE)
                .to_string(),
            |def_id| self
                .tcx()
                .crate_name(def_id.krate)
                .to_string(),
        )
    }

    pub fn insert_block_span(
        &'tcx self,
        key: (DefId, String),
        span: Span,
    ) {
        let mut manager = self.spans.borrow_mut();
        manager.block_spans.insert(key, span);
    }

    pub fn get_block_span(
        &'tcx self,
        key: &(DefId, String),
    ) -> Option<Span> {
        let manager = self.spans.borrow();
        manager
            .block_spans
            .get(key)
            .copied()
    }

    pub fn insert_viper_identifier(
        &'tcx self,
        identifier: String,
        def_id: &DefId,
    ) {
        let mut manager = self.spans.borrow_mut();
        manager.viper_identifiers.insert(identifier, *def_id);
    }

    /// Attempt to retrieve the def id from a viper identifier string.
    /// Currently, these are only stored for locally defined, selected methods.
    /// See `prusti_encoder::ImpureFunctionEnc::encode`.
    pub fn get_viper_identifier(
        &'tcx self,
        identifier: &str,
    ) -> Option<DefId> {
        let manager = self.spans.borrow();
        manager.viper_identifiers.get(identifier).copied()
    }

    /// Return the set of all viper identifiers with encoded bodies
    pub fn get_viper_identifiers(
        &'tcx self,
    ) -> HashSet<String> {
        let manager = self.spans.borrow();
        manager.viper_identifiers.keys().cloned().collect()
    }

    /// The unique itemname is of form `<crate name>::<defpath>`
    pub fn get_unique_item_name(
        &'tcx self,
        def_id: &DefId,
    ) -> String {
        format!(
            "{}::{}",
            self.tcx().crate_name(def_id.krate),
            self.tcx().def_path_str(def_id),
        ).to_string()
    }

    pub fn push_call_contract_span(
        &'tcx self,
        defpath: String,
        call_span: Span,
        contracts_spans: Vec<Span>,
        source_map: &SourceMap
    ) {
        let span_of_call_contracts = SpanOfCallContracts::new(
            defpath,
            call_span,
            contracts_spans,
            source_map,
        );
        let mut manager = self.spans.borrow_mut();
        manager.call_contract_spans.push(span_of_call_contracts);
    }

    /// Emit contract spans as diagnostic. (For Prusti-Assistant)
    pub fn emit_contract_spans(
        &'tcx self,
        env_diagnostic: &EnvDiagnostic<'_>,
    ) {
        let mut call_contract_spans = self
            .spans
            .borrow()
            .call_contract_spans
            .clone();
        // sort, so the order is deterministic
        call_contract_spans
            .sort_by(|a,b| a.defpath.cmp(&b.defpath));

        let encoding_info = EncodingInfo { call_contract_spans };
        PrustiError::message(
            format!("encodingInfo{}", encoding_info.to_json_string()),
            DUMMY_SP.into(),
        )
        .emit(env_diagnostic);
    }
}
