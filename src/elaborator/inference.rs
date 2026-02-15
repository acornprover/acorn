use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::unresolved_constant::UnresolvedConstant;
use crate::syntax::expression::Expression;

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

    /// Try to apply a potential value to arguments, allowing unresolved outputs.
    pub fn try_apply_potential(
        &self,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        self.bindings
            .try_apply_potential(potential, args, expected_type, source)
    }

    /// Apply a potential value and fail with a caller-provided message if inference is incomplete.
    pub fn apply_potential_or_error(
        &self,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        unresolved_error: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        match self.try_apply_potential(potential, args, expected_type, source)? {
            PotentialValue::Resolved(value) => Ok(value),
            PotentialValue::Unresolved(_) => Err(source.error(unresolved_error)),
        }
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

    /// Resolve an unresolved call by evaluating each argument as a generic value.
    pub fn resolve_unresolved_call_from_exprs<'expr, F>(
        &self,
        unresolved: UnresolvedConstant,
        arg_exprs: &[&'expr Expression],
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
        mut evaluate_generic_arg: F,
    ) -> error::Result<AcornValue>
    where
        F: FnMut(&'expr Expression) -> error::Result<AcornValue>,
    {
        let mut args = Vec::with_capacity(arg_exprs.len());
        for arg_expr in arg_exprs {
            args.push(evaluate_generic_arg(arg_expr)?);
        }
        self.resolve_unresolved_call(unresolved, args, expected_type, source)
    }

    /// Resolve an unresolved constant by explicitly providing type arguments.
    pub fn resolve_unresolved_with_type_params(
        &self,
        unresolved: UnresolvedConstant,
        type_params: Vec<AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        unresolved.resolve(source, type_params)
    }

    /// Resolve equality operands, inferring one side from the other when possible.
    pub fn resolve_equality_operands(
        &self,
        left: PotentialValue,
        left_source: &dyn ErrorContext,
        right: PotentialValue,
        right_source: &dyn ErrorContext,
    ) -> error::Result<(AcornValue, AcornValue)> {
        match (left, right) {
            (PotentialValue::Resolved(left_value), PotentialValue::Resolved(right_value)) => {
                right_value.check_type(Some(&left_value.get_type()), right_source)?;
                Ok((left_value, right_value))
            }
            (
                PotentialValue::Unresolved(left_unresolved),
                PotentialValue::Resolved(right_value),
            ) => {
                let left_resolved = self.maybe_resolve_value(
                    PotentialValue::Unresolved(left_unresolved),
                    Some(&right_value.get_type()),
                    left_source,
                )?;
                Ok((left_resolved.as_value(left_source)?, right_value))
            }
            (
                PotentialValue::Resolved(left_value),
                PotentialValue::Unresolved(right_unresolved),
            ) => {
                let right_resolved = self.maybe_resolve_value(
                    PotentialValue::Unresolved(right_unresolved),
                    Some(&left_value.get_type()),
                    right_source,
                )?;
                Ok((left_value, right_resolved.as_value(right_source)?))
            }
            (PotentialValue::Unresolved(left_unresolved), PotentialValue::Unresolved(_)) => {
                Err(left_source.error(&format!(
                    "value {} has unresolved type",
                    left_unresolved.name
                )))
            }
        }
    }

    /// Infer type arguments on a function value so its return type matches the expected type.
    pub fn infer_function_return_type(
        &self,
        function: AcornValue,
        expected_return_type: &AcornType,
        what: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        let function_type = function.get_type();
        let actual_return_type = match &function_type {
            AcornType::Function(function_type) => function_type.return_type.as_ref(),
            _ => {
                return Err(source.error(&format!(
                    "expected a function type, but got {}",
                    function_type
                )))
            }
        };

        if actual_return_type == expected_return_type {
            return Ok(function);
        }

        let mut unifier = self.bindings.unifier();
        unifier.user_match_instance(actual_return_type, expected_return_type, what, source)?;
        if unifier.mapping.is_empty() {
            return Ok(function);
        }

        let substitutions: Vec<_> = unifier.mapping.into_iter().collect();
        Ok(function.instantiate(&substitutions))
    }
}
