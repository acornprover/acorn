use std::fmt;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::unresolved_constant::UnresolvedConstant;

pub static EMPTY_TYPE_PARAMS: [TypeParam; 0] = [];

/// Could be a value, but could also be an unresolved constant.
#[derive(Debug, Clone)]
pub enum PotentialValue {
    /// (module, constant name, type, type parameters)
    Unresolved(UnresolvedConstant),

    /// Something that we do know the type of.
    Resolved(AcornValue),
}

impl PotentialValue {
    /// Convert this to a value, panicking if it's unresolved.
    pub fn force_value(self) -> AcornValue {
        match self {
            PotentialValue::Unresolved(u) => {
                panic!("tried to force unresolved constant {}", u.name);
            }
            PotentialValue::Resolved(c) => c,
        }
    }

    /// Convert this to a value, or return an error if it's unresolved.
    pub fn as_value(self, source: &dyn ErrorContext) -> error::Result<AcornValue> {
        match self {
            PotentialValue::Unresolved(u) => {
                Err(source.error(&format!("value {} has unresolved type", u.name)))
            }
            PotentialValue::Resolved(c) => Ok(c),
        }
    }

    /// If this is an unresolved value, it will have a generic type.
    pub fn get_type(&self) -> AcornType {
        match &self {
            PotentialValue::Unresolved(u) => u.generic_type.clone(),
            PotentialValue::Resolved(v) => v.get_type(),
        }
    }

    /// Gets the unresolved parameters, if this is unresolved.
    pub fn unresolved_params(&self) -> &[TypeParam] {
        match &self {
            PotentialValue::Unresolved(u) => &u.params,
            PotentialValue::Resolved(_) => &EMPTY_TYPE_PARAMS,
        }
    }

    pub fn as_unresolved(&self) -> Option<&UnresolvedConstant> {
        match self {
            PotentialValue::Unresolved(u) => Some(u),
            PotentialValue::Resolved(_) => None,
        }
    }

    pub fn to_unresolved(self, source: &dyn ErrorContext) -> error::Result<UnresolvedConstant> {
        match self {
            PotentialValue::Unresolved(u) => Ok(u),
            PotentialValue::Resolved(v) => {
                Err(source.error(&format!("expected unresolved value, but found {}", v)))
            }
        }
    }

    /// Resolve this into a value, using type variables for unknown parameters.
    pub fn to_generic_value(self) -> AcornValue {
        match self {
            PotentialValue::Unresolved(u) => u.to_generic_value(),
            PotentialValue::Resolved(v) => v,
        }
    }

    /// Treat this as a constant, and resolve it with the given parameters.
    /// Return an error if there's a mismatch between number of parameters.
    pub fn resolve_constant(
        &self,
        params: &[AcornType],
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        match self {
            PotentialValue::Unresolved(u) => u.resolve(source, params.to_vec()),
            PotentialValue::Resolved(v) => {
                if !params.is_empty() {
                    return Err(
                        source.error(&format!("expected unresolved constant, but found {}", v))
                    );
                }
                Ok(v.clone())
            }
        }
    }

    pub fn resolve_constant_with_datatype_args(
        &self,
        type_params: &[AcornType],
        value_params: &[AcornValue],
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        self.resolve_constant(type_params, source)?
            .bind_value_params(value_params, source)
    }
}

impl fmt::Display for PotentialValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PotentialValue::Unresolved(u) => write!(f, "{}", u),
            PotentialValue::Resolved(v) => write!(f, "{}", v),
        }
    }
}
