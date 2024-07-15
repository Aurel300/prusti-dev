use prusti_rustc_interface::span::{source_map::SourceMap, Span};
use serde::Serialize;
use super::vsc_span::VscSpan;

/// Represents the locations of specifications of a function call.
/// Generated for each encoded function call to be used by prusti-assistant.
#[derive(Serialize, Clone, Debug)]
pub struct SpanOfCallContracts {
    /// the defpath of the method that is called
    pub defpath: String,
    /// the spans where this method is called
    pub call_spans: Vec<VscSpan>,
    /// the spans of all the specifications of the called method
    pub contracts_spans: Vec<VscSpan>,
}

impl SpanOfCallContracts {
    pub fn new(
        defpath: String,
        call_spans: Vec<Span>,
        contracts_spans: Vec<Span>,
        source_map: &SourceMap
    ) -> Self {
        let call_spans = call_spans
            .iter()
            .map(|sp| VscSpan::from_span(sp, source_map))
            .collect::<Vec<VscSpan>>();
        let contracts_spans = contracts_spans
            .iter()
            .map(|sp| VscSpan::from_span(sp, source_map))
            .collect::<Vec<VscSpan>>();
        Self {
            defpath,
            call_spans,
            contracts_spans,
        }
    }

    pub fn set_contract_spans(&mut self, spans: Vec<Span>, source_map: &SourceMap) {
        self.contracts_spans = spans
            .iter()
            .map(|sp| VscSpan::from_span(sp, source_map))
            .collect::<Vec<VscSpan>>();
    }

    pub fn push_call_span(&mut self, span: &Span, source_map: &SourceMap) {
        let vsc_span = VscSpan::from_span(span, source_map);
        self.call_spans.push(vsc_span);
    }
}

#[derive(Serialize)]
pub struct EncodingInfo {
    pub call_contract_spans: Vec<SpanOfCallContracts>,
}

impl EncodingInfo {
    pub fn to_json_string(self) -> String {
        serde_json::to_string(&self).unwrap()
    }
}

