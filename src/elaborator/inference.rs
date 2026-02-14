use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::unresolved_constant::UnresolvedConstant;

/// Orchestrates inference over unresolved constants using the current bindings.
pub struct InferenceEngine<'a> {
    bindings: &'a BindingMap,
}

impl<'a> InferenceEngine<'a> {
    pub fn new(bindings: &'a BindingMap) -> Self {
        Self { bindings }
    }

    /// If we have an expected type and this is unresolved, try to resolve it.
    pub fn maybe_resolve_value(
        &self,
        potential: PotentialValue,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        self.bindings
            .unifier()
            .maybe_resolve_value(potential, expected_type, source)
    }

    /// Resolve an unresolved constant application by inferring type arguments.
    pub fn resolve_unresolved_call(
        &self,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        self.bindings
            .unifier()
            .resolve_with_inference(unresolved, args, expected_type, source)
    }
}
