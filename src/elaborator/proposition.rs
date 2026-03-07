use std::collections::HashMap;
use std::fmt;

use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::error::{ErrorContext, Result};
use crate::elaborator::source::{Source, SourceType};

/// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    /// A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    /// The type parameters that this proposition can be instantiated with.
    pub params: Vec<TypeParam>,

    /// The number of leading value arguments that came from statement syntax.
    /// This does not include type parameters in `params`.
    pub arg_count: usize,

    /// Where this proposition came from.
    pub source: Source,
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.params.is_empty() {
            write!(f, "{} ", TypeParam::params_to_str(&self.params))?;
        }
        self.value.fmt(f)
    }
}

impl Proposition {
    /// Creates a proposition that may be generic. Params can be empty.
    pub fn new(value: AcornValue, params: Vec<TypeParam>, source: Source) -> Proposition {
        if source.importable && value.has_arbitrary() {
            panic!(
                "importable propositions should not have arbitrary types, at {:?}",
                source
            );
        }
        Proposition {
            value,
            params,
            arg_count: 0,
            source,
        }
    }

    /// Records how many leading value arguments came from statement syntax.
    pub fn with_arg_count(mut self, arg_count: usize) -> Proposition {
        self.arg_count = arg_count;
        self
    }

    /// Just changes the value while keeping the other stuff intact
    pub fn with_value(self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            params: self.params,
            arg_count: self.arg_count,
            source: self.source,
        }
    }

    /// Theorems have theorem names, and so do axioms because those work like theorems.
    pub fn theorem_name(&self) -> Option<&str> {
        match &self.source.source_type {
            SourceType::Axiom(name) | SourceType::Theorem(name) => name.as_deref(),
            _ => None,
        }
    }

    /// Validates that the params exactly match the type variables used in the value.
    /// Returns an error if there's a mismatch.
    pub fn validate_params(&self, source: &dyn ErrorContext) -> Result<()> {
        // Collect all type variables from the value
        let mut value_vars = HashMap::new();
        self.value.find_type_vars(&mut value_vars, source)?;

        // Check that every param is used in the value
        for param in &self.params {
            if !value_vars.contains_key(&param.name) {
                return Err(source.error(&format!(
                    "Type parameter '{}' is declared but not used in the value",
                    param.name
                )));
            }
        }

        // Check that every type variable in the value is declared in params
        for (var_name, var_param) in &value_vars {
            if !self.params.iter().any(|p| &p.name == var_name) {
                return Err(source.error(&format!(
                    "Type variable '{}' is used in the value but not declared in parameters",
                    var_name
                )));
            }

            // Check that the typeclasses match for declared parameters
            if let Some(param) = self.params.iter().find(|p| &p.name == var_name) {
                if param.typeclass != var_param.typeclass {
                    return Err(source.error(&format!(
                        "Type variable '{}' has different typeclass constraints in declaration ({:?}) and usage ({:?})",
                        var_name, param.typeclass, var_param.typeclass
                    )));
                }
            }
        }

        // Check that the number of params matches the number of unique type variables
        if self.params.len() != value_vars.len() {
            return Err(source.error(&format!(
                "Mismatch between number of declared type parameters ({}) and used type variables ({})",
                self.params.len(), value_vars.len()
            )));
        }

        Ok(())
    }
}
