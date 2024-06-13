use serde::Serialize;
use super::vsc_span::VscSpan;

#[derive(Serialize)]
pub struct EncodingInfo {
    pub call_contract_spans: String,
}

impl EncodingInfo {
    pub fn to_json_string(self) -> String {
        serde_json::to_string(&self).unwrap()
    }
}

