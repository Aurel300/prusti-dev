// TODO: headers in this folder

use rustc_middle::ty;
use prusti_common::vir;
use prusti_common::vir::{Expr, Type};
use std::collections::HashMap;

pub mod encoder;
mod patcher;

#[derive(Debug, Clone)]
pub enum Snapshot {
    /// Corresponds directly to an existing Viper type.
    Primitive(Type),
    /// Encodes types with no content; these need not be provided as arguments
    /// to snapshot constructors.
    Unit,
    /// Encodes a complex type: tuples, ADTs, or closures.
    Complex {
        predicate_name: String,
        domain: vir::Domain,
        discriminant_func: vir::DomainFunc,
        snap_func: vir::Function,
        /// [variants] has one entry for tuples, structs, and closures.
        /// For enums, it has as many entries as there are variants.
        variants: Vec<HashMap<String, vir::DomainFunc>>,
        /// Mapping of variant names (as used by Prusti) to variant indices
        /// in the [variants] vector. Empty for non-enums.
        variant_names: HashMap<String, usize>,
    }, // TODO: separate variant for enums and one-variant Complexes?
    /// Type could not be encoded.
    Abstract,

    /// A type which will be resolved to a different snapshot kind.
    /// (Should only appear while encoding is in progress!)
    Lazy(Type),
}

impl Snapshot {
    pub fn get_type(&self) -> Type {
        match self {
            Self::Primitive(ty) => ty.clone(),
            Self::Unit => Type::Domain(encoder::UNIT_DOMAIN_NAME.to_string()),
            Self::Complex { predicate_name, .. } => Type::Snapshot(predicate_name.to_string()),
            Self::Abstract => Type::Domain(encoder::UNIT_DOMAIN_NAME.to_string()),
            Self::Lazy(ty) => ty.clone(),
            _ => unimplemented!("snapshot type of {:?}", self),
        }
    }

    pub fn is_quantifiable(&self) -> bool {
        // TODO: more types?
        match self {
            Self::Primitive(_) => true,
            _ => false,
        }
    }

    pub fn supports_equality(&self) -> bool {
        match self {
            Self::Primitive(_) => true,
            Self::Unit => true,
            Self::Complex { .. } => true,
            _ => false,
        }
    }
}
