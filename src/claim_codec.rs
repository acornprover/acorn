use std::collections::HashMap;

use crate::code_generator::{CodeGenerator, Error as CodeGenError};
use crate::elaborator::acorn_type::{AcornType, PotentialType, TypeParam, Typeclass};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::stack::Stack;
use crate::elaborator::to_term::lower_value_to_term_existing_with_stack;
use crate::elaborator::to_term::TypeVarMap;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::Claim;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::{Decomposition, Term};
use crate::kernel::term_normalization::normalize_term;
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::project::Project;
use crate::syntax::expression::{Declaration, Expression, TypeParamExpr};
use crate::syntax::statement::{Statement, StatementInfo};
use crate::syntax::token::TokenType;

/// Encodes and decodes certificate claim lines.
pub(crate) struct ClaimCodec;

/// The function half of a `function[...] (...) { ... } [..] (...)` claim expression.
struct ClaimFunctionValue {
    type_param_names: Vec<String>,
    type_param_constraints: Vec<Option<Typeclass>>,
    type_args: Vec<AcornType>,
    arg_types: Vec<AcornType>,
    body: AcornValue,
}

/// The parsed surface pieces of a `function[...] (...) { ... } [..] (...)` claim expression.
struct ClaimExpressionShape<'a> {
    type_params: &'a [TypeParamExpr],
    declarations: &'a [Declaration],
    body: &'a Expression,
    type_args: Vec<&'a Expression>,
    value_args: Vec<&'a Expression>,
}

impl ClaimCodec {
    /// Wrap generated code so the parser treats it as a claim statement.
    pub(crate) fn ensure_claim_code_parses_as_claim(code: String) -> Result<String, CodeGenError> {
        let parses_as_claim = |candidate: &str| -> Result<bool, CodeGenError> {
            Ok(matches!(
                Statement::parse_str_with_options(candidate, true)?.statement,
                StatementInfo::Claim(_)
            ))
        };

        let trimmed = code.trim_start();
        if trimmed.starts_with("forall(")
            || trimmed.starts_with("if ")
            || trimmed.starts_with("if(")
        {
            let wrapped = format!("({code})");
            if parses_as_claim(&wrapped)? {
                return Ok(wrapped);
            }
        }

        if parses_as_claim(&code)? {
            return Ok(code);
        }

        let wrapped = format!("({code})");
        if parses_as_claim(&wrapped)? {
            return Ok(wrapped);
        }

        Err(CodeGenError::GeneratedBadCode(format!(
            "generated claim did not parse as a claim: {}",
            code
        )))
    }

    /// Serialize a claim in clause-plus-arguments form and require the claim codec roundtrip.
    pub(crate) fn serialize_claim_with_args(
        claim: &Claim,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        let local_context = claim.clause().get_local_context();
        let var_count = local_context.len();
        if var_count == 0 {
            return Err(CodeGenError::GeneratedBadCode(
                "cannot serialize claim-with-args for a clause with no local variables".to_string(),
            ));
        }

        let mut generator = CodeGenerator::new_for_certificate(bindings);
        let local_type_params = Self::local_type_param_infos(local_context, kernel_context);
        let generic_value = kernel_context.quote_clause(claim.clause(), None, None, false);
        let generic_code = generator.value_to_code(&generic_value)?;
        if claim.var_map().iter().next().is_none() {
            let mut arbitrary_params = vec![];
            for var_id in 0..local_context.len() {
                let var_type = local_context
                    .get_var_type(var_id)
                    .expect("local context should provide all variable types")
                    .clone();
                kernel_context
                    .quote_type_with_context(var_type, local_context, false)
                    .collect_arbitrary_params(&mut arbitrary_params);
            }

            if arbitrary_params.is_empty() {
                if !local_type_params.is_empty() {
                    let local_type_param_names: Vec<String> = local_type_params
                        .iter()
                        .map(|(name, _)| name.clone())
                        .collect();
                    let named_generic_code =
                        generator.value_to_code(&kernel_context.quote_clause(
                            claim.clause(),
                            None,
                            Some(local_type_param_names.as_slice()),
                            false,
                        ))?;
                    let mut type_param_decl_codes = vec![];
                    for (type_param_name, kind) in &local_type_params {
                        let decl_code = match kind {
                            AcornType::Type0 => type_param_name.clone(),
                            _ => {
                                format!("{}: {}", type_param_name, generator.type_to_expr(kind)?)
                            }
                        };
                        type_param_decl_codes.push(decl_code);
                    }
                    if local_type_params
                        .iter()
                        .all(|(_, kind)| matches!(kind, AcornType::Type0))
                    {
                        return Ok(format!(
                            "function[{}] {{ {} }}",
                            type_param_decl_codes.join(", "),
                            named_generic_code
                        ));
                    }

                    let mut type_arg_codes = vec![];
                    for (type_param_name, kind) in &local_type_params {
                        let arg_code = if let Some(selected_type) =
                            Self::infer_in_scope_type_arg(kind, bindings)
                        {
                            generator.type_to_expr(&selected_type)?.to_string()
                        } else {
                            type_param_name.clone()
                        };
                        type_arg_codes.push(arg_code);
                    }
                    return Ok(format!(
                        "function[{}] {{ {} }}[{}]",
                        type_param_decl_codes.join(", "),
                        named_generic_code,
                        type_arg_codes.join(", ")
                    ));
                }
                return Self::ensure_claim_code_parses_as_claim(generic_code);
            }

            arbitrary_params.sort_by(|a, b| a.name.cmp(&b.name));
            let mut type_param_decl_codes = vec![];
            let mut type_arg_codes = vec![];
            for param in &arbitrary_params {
                let kind = if let Some(typeclass) = &param.typeclass {
                    AcornType::TypeclassConstraint(typeclass.clone())
                } else {
                    AcornType::Type0
                };
                let decl_code = match &kind {
                    AcornType::Type0 => param.name.clone(),
                    _ => format!("{}: {}", param.name, generator.type_to_expr(&kind)?),
                };
                type_param_decl_codes.push(decl_code);

                let arg_code =
                    if let Some(selected_type) = Self::infer_in_scope_type_arg(&kind, bindings) {
                        generator.type_to_expr(&selected_type)?.to_string()
                    } else {
                        param.name.clone()
                    };
                type_arg_codes.push(arg_code);
            }
            return Ok(format!(
                "function[{}] {{ {} }}[{}]",
                type_param_decl_codes.join(", "),
                generic_code,
                type_arg_codes.join(", ")
            ));
        }
        let num_type_params = local_context
            .get_var_types()
            .iter()
            .take_while(|var_type| {
                var_type
                    .as_ref()
                    .is_some_and(|term| term.as_ref().is_type_param_kind())
            })
            .count();
        let body_code = if matches!(generic_value, AcornValue::ForAll(_, _)) {
            let generic_expr = Expression::parse_value_string(&generic_code)?;
            match generic_expr {
                Expression::Binder(token, _, body, _) if token.token_type == TokenType::ForAll => {
                    body.to_string()
                }
                _ => {
                    return Err(CodeGenError::GeneratedBadCode(
                        "expected quoted generic claim to have forall shape".to_string(),
                    ));
                }
            }
        } else {
            generic_code
        };

        let mut type_param_decl_codes = vec![];
        let mut type_arg_codes = vec![];
        let mut roundtrip_type_param_names = vec![];
        let mut roundtrip_type_param_constraints = vec![];
        let mut roundtrip_type_args = vec![];
        let mut resolved_type_var_map = VariableMap::new();
        let mut value_decl_codes = vec![];
        let mut value_arg_codes = vec![];
        let mut value_lambda_arg_types = vec![];
        let mut value_arg_values = vec![];
        let mut next_value_decl_id = 0;
        let mut value_decl_name_by_var = vec![None; local_context.len()];

        for var_id in 0..local_context.len() {
            let var_type = local_context
                .get_var_type(var_id)
                .expect("local context should provide all variable types");
            if var_type.as_ref().is_type_param_kind() {
                continue;
            }
            if claim.var_map().get_mapping(var_id as AtomId).is_none() {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "missing claim var map entry for x{}",
                    var_id
                )));
            }
            value_decl_name_by_var[var_id] =
                Some(bindings.next_indexed_var('x', &mut next_value_decl_id));
        }
        let initial_value_var_names: Vec<String> = value_decl_name_by_var
            .iter()
            .filter_map(|name| name.clone())
            .collect();

        for var_id in 0..local_context.len() {
            let var_type = local_context
                .get_var_type(var_id)
                .expect("local context should provide all variable types")
                .clone();
            let arg_term = claim.var_map().get_mapping(var_id as AtomId);

            if var_type.as_ref().is_type_param_kind() {
                let type_param_name = format!("T{}", var_id);
                let kind = kernel_context.quote_type_with_context(var_type, local_context, false);
                let roundtrip_constraint = match &kind {
                    AcornType::Type0 => None,
                    AcornType::TypeclassConstraint(typeclass) => Some(typeclass.clone()),
                    _ => {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "invalid type-parameter kind for x{}",
                            var_id
                        )));
                    }
                };
                let decl_code = match kind {
                    AcornType::Type0 => type_param_name.clone(),
                    AcornType::TypeclassConstraint(_) => {
                        let kind_code = generator.type_to_expr(&kind)?.to_string();
                        format!("{}: {}", type_param_name, kind_code)
                    }
                    _ => unreachable!(),
                };
                type_param_decl_codes.push(decl_code);
                roundtrip_type_param_names.push(type_param_name.clone());
                roundtrip_type_param_constraints.push(roundtrip_constraint.clone());

                let mapped_type = arg_term.map(|term| {
                    kernel_context.quote_type_with_context(term.clone(), local_context, false)
                });
                let (selected_type, type_arg_code) = match mapped_type {
                    Some(mapped) if !matches!(mapped, AcornType::Variable(_)) => (
                        Some(mapped.clone()),
                        generator.type_to_expr(&mapped)?.to_string(),
                    ),
                    Some(_) | None => {
                        if let Some(in_scope_type) = Self::infer_in_scope_type_arg(&kind, bindings)
                        {
                            (
                                Some(in_scope_type.clone()),
                                generator.type_to_expr(&in_scope_type)?.to_string(),
                            )
                        } else {
                            (None, type_param_name.clone())
                        }
                    }
                };
                if let Some(selected_type) = selected_type {
                    resolved_type_var_map.set(
                        var_id as AtomId,
                        kernel_context
                            .type_store
                            .to_type_term_with_vars(&selected_type, None),
                    );
                    roundtrip_type_args.push(selected_type);
                } else {
                    roundtrip_type_args.push(AcornType::Variable(TypeParam {
                        name: type_param_name.clone(),
                        typeclass: roundtrip_constraint,
                    }));
                }
                type_arg_codes.push(type_arg_code);
                continue;
            }

            let arg_term = arg_term.ok_or_else(|| {
                CodeGenError::GeneratedBadCode(format!(
                    "missing claim var map entry for x{}",
                    var_id
                ))
            })?;

            let var_name = value_decl_name_by_var[var_id]
                .as_ref()
                .expect("value variable names should be precomputed")
                .clone();
            let acorn_type = kernel_context.quote_type_with_context(var_type, local_context, false);
            value_lambda_arg_types.push(acorn_type.clone());
            value_decl_codes.push(format!(
                "{}: {}",
                var_name,
                generator.type_to_expr(&acorn_type)?
            ));

            let substituted_arg_term = apply_to_term(arg_term.as_ref(), &resolved_type_var_map);
            let arg_value = if substituted_arg_term.max_variable().is_some() {
                let quoted = kernel_context.quote_term_with_context(
                    &substituted_arg_term,
                    local_context,
                    true,
                );
                Self::rebase_value_to_standalone(&quoted, num_type_params as AtomId).map_err(
                    |err| {
                        CodeGenError::GeneratedBadCode(format!(
                            "{} [claim arg term: {}; quoted: {}]",
                            err, substituted_arg_term, quoted
                        ))
                    },
                )?
            } else {
                let quoted = kernel_context.quote_term_with_context(
                    &substituted_arg_term,
                    &LocalContext::empty(),
                    true,
                );
                Self::shift_value_variables(&quoted, initial_value_var_names.len() as AtomId)
            };
            value_arg_values.push(arg_value.clone());
            if Self::value_has_variable(&arg_value) {
                value_arg_codes.push(
                    generator
                        .value_to_code_with_initial_vars(&arg_value, &initial_value_var_names)?,
                );
            } else {
                value_arg_codes.push(generator.value_to_code(&arg_value)?);
            }
        }

        let lambda_body_value = match &generic_value {
            AcornValue::ForAll(_, body) => body.as_ref().clone(),
            _ => generic_value.clone(),
        };
        let lambda_value = AcornValue::lambda(value_lambda_arg_types, lambda_body_value);
        let roundtrip_function = if roundtrip_type_param_names.is_empty() {
            lambda_value
        } else {
            AcornValue::type_apply(
                lambda_value,
                roundtrip_type_param_names.clone(),
                roundtrip_type_param_constraints.clone(),
                roundtrip_type_args.clone(),
            )
        };
        let mut expected_kernel_context = kernel_context.clone();
        let expected_roundtrip_claim = Self::expected_roundtrip_claim(
            &claim,
            &roundtrip_type_param_names,
            &roundtrip_type_param_constraints,
            &roundtrip_type_args,
            &value_arg_values,
            &mut expected_kernel_context,
        )?;
        let mut roundtrip_kernel_context = kernel_context.clone();
        let actual_roundtrip = Self::deserialize_claim_with_args_parts(
            roundtrip_function,
            value_arg_values,
            &mut roundtrip_kernel_context,
        )?;
        if actual_roundtrip.as_ref() != Some(&expected_roundtrip_claim) {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "{}: expected {:?}, got {:?}",
                Self::claim_with_args_roundtrip_error(),
                expected_roundtrip_claim,
                actual_roundtrip
            )));
        }

        if value_decl_codes.is_empty() {
            if type_param_decl_codes.is_empty() {
                let specialized = claim
                    .normalized_specialized_clause(kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;
                let specialized_value = kernel_context.quote_clause(&specialized, None, None, true);
                let code = generator.value_to_code(&specialized_value)?;
                return Self::ensure_claim_code_parses_as_claim(code);
            }

            return Ok(format!(
                "function[{}] {{ {} }}[{}]",
                type_param_decl_codes.join(", "),
                body_code,
                type_arg_codes.join(", ")
            ));
        }

        if type_param_decl_codes.is_empty() {
            return Ok(format!(
                "function({}) {{ {} }}({})",
                value_decl_codes.join(", "),
                body_code,
                value_arg_codes.join(", ")
            ));
        }

        Ok(format!(
            "function[{}]({}) {{ {} }}[{}]({})",
            type_param_decl_codes.join(", "),
            value_decl_codes.join(", "),
            body_code,
            type_arg_codes.join(", "),
            value_arg_codes.join(", ")
        ))
    }

    /// Parse a serialized claim-with-args line.
    pub(crate) fn deserialize_claim_with_args(
        code: &str,
        project: &Project,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
        allow_choose: bool,
    ) -> Result<Claim, CodeGenError> {
        let statement = Statement::parse_str_with_options(code, true)?;
        let StatementInfo::Claim(claim_statement) = statement.statement else {
            return Err(CodeGenError::GeneratedBadCode(
                "expected a claim expression".to_string(),
            ));
        };

        let mut kernel_context_clone = kernel_context.clone();
        Self::try_deserialize_claim_expression(
            &claim_statement.claim,
            project,
            bindings,
            &mut kernel_context_clone,
            allow_choose,
        )?
        .ok_or_else(|| {
            CodeGenError::GeneratedBadCode(
                "expected a function(...) { ... }(...) claim shape".to_string(),
            )
        })
    }

    /// Try to parse a claim-with-args expression without falling back to plain claim parsing.
    pub(crate) fn try_deserialize_claim_expression(
        expr: &Expression,
        project: &Project,
        bindings: &BindingMap,
        kernel_context: &mut KernelContext,
        allow_choose: bool,
    ) -> Result<Option<Claim>, CodeGenError> {
        let Some(shape) = Self::split_claim_expression(expr) else {
            return Ok(None);
        };
        let (function_value, args) =
            Self::evaluate_claim_expression_shape(shape, project, bindings, allow_choose)?;
        Self::claim_from_function_value(function_value, args, kernel_context).map(Some)
    }

    /// Build a plain claim from an already-lowered boolean term.
    pub(crate) fn claim_from_plain_term(
        term: &Term,
        kernel_context: &mut KernelContext,
    ) -> Result<Claim, CodeGenError> {
        if Self::should_preserve_single_literal_claim(term) {
            if let Some(clause) = Self::try_deserialize_single_literal_clause(term, &[]) {
                return Self::claim_from_clause(clause);
            }
        }
        if let Some(clause) = Self::try_deserialize_exists_literal_clause(term, &[], kernel_context)
        {
            return Self::claim_from_clause(clause);
        }

        let clauses = kernel_context.term_to_checker_clauses(term, None)?;
        if clauses.len() != 1 {
            let checker_term = kernel_context.term_to_checker_term(term, None)?;
            let clause = Clause::from_literals_unnormalized(
                vec![Literal::positive(checker_term)],
                &LocalContext::empty(),
            );
            return Self::claim_from_clause(clause);
        }

        let clause = clauses
            .into_iter()
            .next()
            .expect("clauses has exactly one element");
        if !clause.get_local_context().is_empty() && !Self::clause_references_local_vars(&clause) {
            let checker_term = kernel_context.term_to_checker_term(term, None)?;
            let literal = Self::try_term_to_single_checker_literal(&checker_term)
                .unwrap_or_else(|| Literal::positive(checker_term));
            let clause = Clause::from_literals_unnormalized(vec![literal], &LocalContext::empty());
            return Self::claim_from_clause(clause);
        }

        Self::claim_from_clause(clause)
    }

    /// Pick a stable in-scope type when a quoted type parameter needs a concrete instantiation.
    fn infer_in_scope_type_arg(kind: &AcornType, bindings: &BindingMap) -> Option<AcornType> {
        let mut candidates = vec![];
        for (name, potential_type) in bindings.iter_types() {
            let PotentialType::Resolved(AcornType::Arbitrary(type_param)) = potential_type else {
                continue;
            };
            let compatible = match kind {
                AcornType::TypeclassConstraint(typeclass) => {
                    type_param.typeclass.as_ref() == Some(typeclass)
                }
                AcornType::Type0 => true,
                _ => false,
            };
            if compatible {
                candidates.push((name.clone(), AcornType::Arbitrary(type_param.clone())));
            }
        }
        candidates.sort_by(|a, b| a.0.cmp(&b.0));
        candidates.into_iter().next().map(|(_, ty)| ty)
    }

    /// Collect the claim-local type parameters that quote_clause should name explicitly.
    fn local_type_param_infos(
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<(String, AcornType)> {
        let mut params = vec![];
        for var_id in 0..local_context.len() {
            let Some(var_type) = local_context.get_var_type(var_id) else {
                continue;
            };
            if !var_type.as_ref().is_type_param_kind() {
                continue;
            }

            params.push((
                format!("T{}", var_id),
                kernel_context.quote_type_with_context(var_type.clone(), local_context, false),
            ));
        }
        params
    }

    /// Rebuild the canonical claim defined by quote-clause plus per-argument lowering.
    fn expected_roundtrip_claim(
        claim: &Claim,
        type_param_names: &[String],
        type_param_constraints: &[Option<Typeclass>],
        type_args: &[AcornType],
        args: &[AcornValue],
        kernel_context: &mut KernelContext,
    ) -> Result<Claim, CodeGenError> {
        let quoted_clause = kernel_context.quote_clause(claim.clause(), None, None, false);
        let type_var_map = Self::build_claim_type_var_map(
            type_param_names,
            type_param_constraints,
            kernel_context,
        );
        let clause = kernel_context
            .lower_clause(&quoted_clause, NewConstantType::Local, type_var_map)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let var_map = Self::build_claim_var_map(type_args, args, kernel_context)?;
        Self::claim_with_var_map(clause, var_map)
    }

    /// Lower the claim function body as an exact quoted clause and combine it with lowered args.
    fn claim_from_function_value(
        function_value: ClaimFunctionValue,
        args: Vec<AcornValue>,
        kernel_context: &mut KernelContext,
    ) -> Result<Claim, CodeGenError> {
        if function_value.arg_types.is_empty() && function_value.type_param_names.is_empty() {
            return Err(CodeGenError::GeneratedBadCode(
                "claim-with-args requires at least one value or type parameter".to_string(),
            ));
        }
        if function_value.arg_types.len() != args.len() {
            return Err(CodeGenError::GeneratedBadCode(
                "argument count does not match function declaration".to_string(),
            ));
        }
        let omits_type_args =
            function_value.type_args.is_empty() && !function_value.type_param_names.is_empty();
        if omits_type_args && (!function_value.arg_types.is_empty() || !args.is_empty()) {
            return Err(CodeGenError::GeneratedBadCode(
                "generic claims with value arguments require explicit type arguments".to_string(),
            ));
        }
        if function_value.type_param_names.len() != function_value.type_param_constraints.len()
            || (!omits_type_args
                && function_value.type_param_names.len() != function_value.type_args.len())
        {
            return Err(CodeGenError::GeneratedBadCode(
                "type-argument metadata does not match type argument count".to_string(),
            ));
        }

        let type_var_map = Self::build_claim_type_var_map(
            &function_value.type_param_names,
            &function_value.type_param_constraints,
            kernel_context,
        );
        let generic_value = AcornValue::forall(function_value.arg_types, function_value.body);
        let clause = kernel_context
            .lower_clause(&generic_value, NewConstantType::Local, type_var_map)
            .map_err(CodeGenError::GeneratedBadCode)?;
        Self::claim_with_args_from_clause(clause, &function_value.type_args, &args, kernel_context)
    }

    /// Deserialize a roundtrip value built from an already-evaluated function and arg list.
    fn deserialize_claim_with_args_parts(
        function_value: AcornValue,
        args: Vec<AcornValue>,
        kernel_context: &mut KernelContext,
    ) -> Result<Option<Claim>, CodeGenError> {
        let function_shape = match Self::split_claim_function_value(function_value) {
            Some(function_shape) => function_shape,
            None => return Ok(None),
        };
        Self::claim_from_function_value(function_shape, args, kernel_context).map(Some)
    }

    /// Split the surface claim expression into its function body and separately applied args.
    fn split_claim_expression(expr: &Expression) -> Option<ClaimExpressionShape<'_>> {
        let mut current = Self::strip_expression_groupings(expr);
        let mut type_args = None;
        let mut value_args = None;

        while let Expression::Concatenation(function_expr, args_expr) = current {
            let Expression::Grouping(left, inner, _) = args_expr.as_ref() else {
                break;
            };
            match left.token_type {
                TokenType::LeftParen => {
                    if value_args.is_some() {
                        return None;
                    }
                    value_args = Some(inner.flatten_comma_separated_list());
                    current = Self::strip_expression_groupings(function_expr);
                }
                TokenType::LeftBracket | TokenType::LessThan => {
                    if type_args.is_some() {
                        return None;
                    }
                    type_args = Some(inner.flatten_comma_separated_list());
                    current = Self::strip_expression_groupings(function_expr);
                }
                _ => break,
            }
        }

        match current {
            Expression::Binder(token, declarations, body, _)
                if token.token_type == TokenType::Function && type_args.is_none() =>
            {
                Some(ClaimExpressionShape {
                    type_params: &[],
                    declarations,
                    body,
                    type_args: vec![],
                    value_args: value_args.unwrap_or_default(),
                })
            }
            Expression::GenericBinder(token, type_params, declarations, body, _)
                if token.token_type == TokenType::Function =>
            {
                Some(ClaimExpressionShape {
                    type_params,
                    declarations,
                    body,
                    type_args: type_args.unwrap_or_default(),
                    value_args: value_args.unwrap_or_default(),
                })
            }
            _ => None,
        }
    }

    /// Evaluate a structurally split claim expression without collapsing body and args together.
    fn evaluate_claim_expression_shape(
        shape: ClaimExpressionShape<'_>,
        project: &Project,
        bindings: &BindingMap,
        allow_choose: bool,
    ) -> Result<(ClaimFunctionValue, Vec<AcornValue>), CodeGenError> {
        let mut type_param_evaluator =
            Evaluator::new_with_allow_choose(project, bindings, None, allow_choose);
        let type_params = type_param_evaluator.evaluate_type_params(shape.type_params)?;

        let mut scoped_bindings = bindings.clone();
        for type_param in &type_params {
            scoped_bindings.add_arbitrary_type(type_param.clone());
        }

        let mut evaluator =
            Evaluator::new_with_allow_choose(project, &scoped_bindings, None, allow_choose);
        let type_args = shape
            .type_args
            .iter()
            .map(|expr| evaluator.evaluate_type(expr))
            .collect::<Result<Vec<_>, _>>()?;

        let mut stack = Stack::new();
        let (arg_names, arg_types) = evaluator.bind_args(&mut stack, shape.declarations, None)?;
        let body =
            evaluator.evaluate_value_with_stack(&mut stack, shape.body, Some(&AcornType::Bool))?;

        if shape.value_args.len() != arg_types.len() {
            return Err(CodeGenError::GeneratedBadCode(
                "argument count does not match function declaration".to_string(),
            ));
        }

        let substitutions: Vec<(String, AcornType)> = type_params
            .iter()
            .map(|param| param.name.clone())
            .zip(type_args.iter().cloned())
            .collect();
        let specialized_arg_types: Vec<AcornType> = arg_types
            .iter()
            .map(|arg_type| arg_type.instantiate(&substitutions))
            .collect();
        let mut specialized_stack = Stack::new();
        for (arg_name, arg_type) in arg_names.iter().zip(specialized_arg_types.iter()) {
            specialized_stack.insert(arg_name.clone(), arg_type.clone());
        }
        let args = shape
            .value_args
            .iter()
            .zip(specialized_arg_types.iter())
            .map(|(expr, arg_type)| {
                evaluator.evaluate_value_with_stack(&mut specialized_stack, expr, Some(arg_type))
            })
            .collect::<Result<Vec<_>, _>>()?;
        stack.remove_all(&arg_names);

        let function_value = ClaimFunctionValue {
            type_param_names: type_params.iter().map(|param| param.name.clone()).collect(),
            type_param_constraints: type_params
                .iter()
                .map(|param| param.typeclass.clone())
                .collect(),
            type_args,
            arg_types,
            body,
        };
        Ok((function_value, args))
    }

    /// Build the lowering map that turns type parameter names into free type variables.
    fn build_claim_type_var_map(
        type_param_names: &[String],
        type_param_constraints: &[Option<Typeclass>],
        kernel_context: &mut KernelContext,
    ) -> Option<HashMap<String, (AtomId, Term)>> {
        if type_param_names.is_empty() {
            return None;
        }

        let mut map = HashMap::new();
        for (i, (name, constraint)) in type_param_names
            .iter()
            .zip(type_param_constraints.iter())
            .enumerate()
        {
            let var_type = if let Some(typeclass) = constraint {
                let typeclass_id = kernel_context.type_store.add_typeclass(typeclass);
                Term::typeclass(typeclass_id)
            } else {
                Term::type_sort()
            };
            map.insert(name.clone(), (i as AtomId, var_type));
        }
        Some(map)
    }

    /// Recover the unevaluated generic lambda structure from the function half of a claim line.
    fn split_claim_function_value(value: AcornValue) -> Option<ClaimFunctionValue> {
        match value {
            AcornValue::Lambda(arg_types, body) => Some(ClaimFunctionValue {
                type_param_names: vec![],
                type_param_constraints: vec![],
                type_args: vec![],
                arg_types,
                body: *body,
            }),
            AcornValue::TypeApplication(type_app) => match *type_app.function {
                AcornValue::Lambda(arg_types, body) => Some(ClaimFunctionValue {
                    type_param_names: type_app.type_param_names,
                    type_param_constraints: type_app.type_param_constraints,
                    type_args: type_app.type_args,
                    arg_types,
                    body: *body,
                }),
                body => Some(ClaimFunctionValue {
                    type_param_names: type_app.type_param_names,
                    type_param_constraints: type_app.type_param_constraints,
                    type_args: type_app.type_args,
                    arg_types: vec![],
                    body,
                }),
            },
            _ => None,
        }
    }

    /// Remove the leading type-parameter slots from a quoted claim arg's variable numbering.
    ///
    /// Claim args are serialized with all generic value binders preloaded as initial vars, so we
    /// only compact away the local-context type-parameter prefix. Binder vars remain offset by the
    /// number of generic value binders and must not be renumbered relative to inner scopes.
    fn rebase_value_to_standalone(
        value: &AcornValue,
        removed_prefix_len: AtomId,
    ) -> Result<AcornValue, CodeGenError> {
        Ok(match value {
            AcornValue::Variable(var_id, var_type) => {
                if *var_id < removed_prefix_len {
                    AcornValue::Variable(*var_id, var_type.clone())
                } else {
                    AcornValue::Variable(var_id - removed_prefix_len, var_type.clone())
                }
            }
            AcornValue::Constant(constant) => AcornValue::Constant(constant.clone()),
            AcornValue::Application(app) => AcornValue::apply(
                Self::rebase_value_to_standalone(&app.function, removed_prefix_len)?,
                app.args
                    .iter()
                    .map(|arg| Self::rebase_value_to_standalone(arg, removed_prefix_len))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            AcornValue::TypeApplication(app) => AcornValue::type_apply(
                Self::rebase_value_to_standalone(&app.function, removed_prefix_len)?,
                app.type_param_names.clone(),
                app.type_param_constraints.clone(),
                app.type_args.clone(),
            ),
            AcornValue::Lambda(arg_types, body) => AcornValue::lambda(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, removed_prefix_len)?,
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(Self::rebase_value_to_standalone(left, removed_prefix_len)?),
                Box::new(Self::rebase_value_to_standalone(right, removed_prefix_len)?),
            ),
            AcornValue::Not(value) => AcornValue::Not(Box::new(Self::rebase_value_to_standalone(
                value,
                removed_prefix_len,
            )?)),
            AcornValue::Try(value, unwrapped_type) => AcornValue::Try(
                Box::new(Self::rebase_value_to_standalone(value, removed_prefix_len)?),
                unwrapped_type.clone(),
            ),
            AcornValue::ForAll(arg_types, body) => AcornValue::forall(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, removed_prefix_len)?,
            ),
            AcornValue::Exists(arg_types, body) => AcornValue::exists(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, removed_prefix_len)?,
            ),
            AcornValue::Choose(choice_type, body) => AcornValue::choose(
                choice_type.clone(),
                Self::rebase_value_to_standalone(body, removed_prefix_len)?,
            ),
            AcornValue::Bool(value) => AcornValue::Bool(*value),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(Self::rebase_value_to_standalone(cond, removed_prefix_len)?),
                Box::new(Self::rebase_value_to_standalone(
                    if_value,
                    removed_prefix_len,
                )?),
                Box::new(Self::rebase_value_to_standalone(
                    else_value,
                    removed_prefix_len,
                )?),
            ),
            AcornValue::Match(scrutinee, cases) => AcornValue::Match(
                Box::new(Self::rebase_value_to_standalone(
                    scrutinee,
                    removed_prefix_len,
                )?),
                cases
                    .iter()
                    .map(|case| {
                        Ok(crate::elaborator::acorn_value::MatchCase {
                            new_vars: case.new_vars.clone(),
                            pattern: Self::rebase_value_to_standalone(
                                &case.pattern,
                                removed_prefix_len,
                            )?,
                            result: Self::rebase_value_to_standalone(
                                &case.result,
                                removed_prefix_len,
                            )?,
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        })
                    })
                    .collect::<Result<Vec<_>, CodeGenError>>()?,
            ),
        })
    }

    /// Shift a standalone quoted arg into the namespace where claim value vars are preloaded.
    fn shift_value_variables(value: &AcornValue, amount: AtomId) -> AcornValue {
        match value {
            AcornValue::Variable(var_id, var_type) => {
                AcornValue::Variable(var_id + amount, var_type.clone())
            }
            AcornValue::Constant(constant) => AcornValue::Constant(constant.clone()),
            AcornValue::Application(app) => AcornValue::apply(
                Self::shift_value_variables(&app.function, amount),
                app.args
                    .iter()
                    .map(|arg| Self::shift_value_variables(arg, amount))
                    .collect::<Vec<_>>(),
            ),
            AcornValue::TypeApplication(app) => AcornValue::type_apply(
                Self::shift_value_variables(&app.function, amount),
                app.type_param_names.clone(),
                app.type_param_constraints.clone(),
                app.type_args.clone(),
            ),
            AcornValue::Lambda(arg_types, body) => {
                AcornValue::lambda(arg_types.clone(), Self::shift_value_variables(body, amount))
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(Self::shift_value_variables(left, amount)),
                Box::new(Self::shift_value_variables(right, amount)),
            ),
            AcornValue::Not(value) => {
                AcornValue::Not(Box::new(Self::shift_value_variables(value, amount)))
            }
            AcornValue::Try(value, unwrapped_type) => AcornValue::Try(
                Box::new(Self::shift_value_variables(value, amount)),
                unwrapped_type.clone(),
            ),
            AcornValue::ForAll(arg_types, body) => {
                AcornValue::forall(arg_types.clone(), Self::shift_value_variables(body, amount))
            }
            AcornValue::Exists(arg_types, body) => {
                AcornValue::exists(arg_types.clone(), Self::shift_value_variables(body, amount))
            }
            AcornValue::Choose(choice_type, body) => AcornValue::choose(
                choice_type.clone(),
                Self::shift_value_variables(body, amount),
            ),
            AcornValue::Bool(value) => AcornValue::Bool(*value),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(Self::shift_value_variables(cond, amount)),
                Box::new(Self::shift_value_variables(if_value, amount)),
                Box::new(Self::shift_value_variables(else_value, amount)),
            ),
            AcornValue::Match(scrutinee, cases) => AcornValue::Match(
                Box::new(Self::shift_value_variables(scrutinee, amount)),
                cases
                    .iter()
                    .map(|case| crate::elaborator::acorn_value::MatchCase {
                        new_vars: case.new_vars.clone(),
                        pattern: Self::shift_value_variables(&case.pattern, amount),
                        result: Self::shift_value_variables(&case.result, amount),
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    })
                    .collect(),
            ),
        }
    }

    /// Detect whether a quoted arg still depends on the claim's preloaded value-variable namespace.
    fn value_has_variable(value: &AcornValue) -> bool {
        match value {
            AcornValue::Variable(_, _) => true,
            AcornValue::Constant(_) | AcornValue::Bool(_) => false,
            AcornValue::Application(app) => {
                Self::value_has_variable(&app.function)
                    || app.args.iter().any(Self::value_has_variable)
            }
            AcornValue::TypeApplication(app) => Self::value_has_variable(&app.function),
            AcornValue::Lambda(_, body)
            | AcornValue::ForAll(_, body)
            | AcornValue::Exists(_, body)
            | AcornValue::Choose(_, body)
            | AcornValue::Not(body)
            | AcornValue::Try(body, _) => Self::value_has_variable(body),
            AcornValue::Binary(_, left, right) => {
                Self::value_has_variable(left) || Self::value_has_variable(right)
            }
            AcornValue::IfThenElse(cond, then_value, else_value) => {
                Self::value_has_variable(cond)
                    || Self::value_has_variable(then_value)
                    || Self::value_has_variable(else_value)
            }
            AcornValue::Match(scrutinee, cases) => {
                Self::value_has_variable(scrutinee)
                    || cases.iter().any(|case| {
                        Self::value_has_variable(&case.pattern)
                            || Self::value_has_variable(&case.result)
                    })
            }
        }
    }

    /// Build a claim from a quoted clause and its separately lowered argument list.
    fn claim_with_args_from_clause(
        clause: Clause,
        type_args: &[AcornType],
        args: &[AcornValue],
        kernel_context: &mut KernelContext,
    ) -> Result<Claim, CodeGenError> {
        let var_map = Self::build_claim_var_map(type_args, args, kernel_context)?;
        Self::claim_with_var_map(clause, var_map)
    }

    /// Lower type and value arguments into the claim variable map.
    fn build_claim_var_map(
        type_args: &[AcornType],
        args: &[AcornValue],
        kernel_context: &mut KernelContext,
    ) -> Result<VariableMap, CodeGenError> {
        let mut var_map = VariableMap::new();
        let mut type_var_map = TypeVarMap::new();
        for (var_id, acorn_type) in type_args.iter().enumerate() {
            let type_term = match acorn_type {
                AcornType::Variable(type_param) => {
                    let kind_term = if let Some(typeclass) = &type_param.typeclass {
                        let typeclass_id = kernel_context.type_store.add_typeclass(typeclass);
                        Term::typeclass(typeclass_id)
                    } else {
                        Term::type_sort()
                    };
                    type_var_map.insert(type_param.name.clone(), (var_id as AtomId, kind_term));
                    Term::atom(Atom::FreeVariable(var_id as AtomId))
                }
                _ => kernel_context
                    .type_store
                    .to_type_term_with_vars(acorn_type, None),
            };
            var_map.set(var_id as AtomId, type_term);
        }

        let type_var_map = (!type_var_map.is_empty()).then_some(type_var_map);
        let value_offset = var_map.len();
        let initial_stack: Vec<Term> = (0..args.len())
            .map(|i| Term::new_variable((value_offset + i) as AtomId))
            .collect();
        for (var_id, arg) in args.iter().enumerate() {
            kernel_context.symbol_table.add_from(
                arg,
                NewConstantType::Local,
                &mut kernel_context.type_store,
            );
            let term = lower_value_to_term_existing_with_stack(
                kernel_context,
                arg,
                type_var_map.as_ref(),
                &initial_stack,
            )?;
            let term = normalize_term(&term);
            let term = kernel_context.term_to_claim_arg(&term)?;
            var_map.set((value_offset + var_id) as AtomId, term);
        }
        Ok(var_map)
    }

    /// Construct a claim that has no extra argument map entries.
    fn claim_from_clause(clause: Clause) -> Result<Claim, CodeGenError> {
        Claim::new(clause, VariableMap::new()).map_err(CodeGenError::GeneratedBadCode)
    }

    /// Construct a claim from a clause and an explicit variable map.
    fn claim_with_var_map(clause: Clause, var_map: VariableMap) -> Result<Claim, CodeGenError> {
        Claim::new(clause, var_map).map_err(CodeGenError::GeneratedBadCode)
    }

    /// Remove top-level parentheses around a claim expression without touching its internals.
    fn strip_expression_groupings(expr: &Expression) -> &Expression {
        let mut current = expr;
        while let Expression::Grouping(_, inner, _) = current {
            current = inner;
        }
        current
    }

    /// Detect when a plain claim must preserve its single-literal shape.
    fn should_preserve_single_literal_claim(term: &Term) -> bool {
        let body = Self::strip_foralls(term);
        if let Some(literal) = Self::try_term_to_single_checker_literal(&body) {
            let mentions_local = literal
                .left
                .iter_atoms()
                .chain(literal.right.iter_atoms())
                .any(|atom| matches!(atom, Atom::FreeVariable(_) | Atom::BoundVariable(_)));
            let contains_inline_binder = matches!(
                literal.left.as_ref().decompose(),
                Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _)
                    | Decomposition::Lambda(_, _)
            ) || matches!(
                literal.right.as_ref().decompose(),
                Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _)
                    | Decomposition::Lambda(_, _)
            );
            if mentions_local && !contains_inline_binder {
                return true;
            }
        }

        let eq_term = if let Some(args) = Self::split_symbol_application(&body, Symbol::Not, 1) {
            args[0].clone()
        } else {
            body
        };
        let Some(args) = Self::split_symbol_application(&eq_term, Symbol::Eq, 3) else {
            return false;
        };
        args[0].as_ref().split_pi().is_some()
            || args[0]
                .iter_atoms()
                .any(|atom| matches!(atom, Atom::FreeVariable(_) | Atom::BoundVariable(_)))
    }

    /// Strip leading `forall`s when checking whether a plain claim should stay literal-shaped.
    fn strip_foralls(term: &Term) -> Term {
        let mut body = term.clone();
        while let Some((_binder_type, binder_body)) = body.as_ref().split_forall() {
            body = binder_body.to_owned();
        }
        body
    }

    /// Rebuild a single literal clause from a term that already uses checker inline syntax.
    fn try_deserialize_single_literal_clause(
        generic_term: &Term,
        type_param_kinds: &[Term],
    ) -> Option<Clause> {
        let mut local_context = LocalContext::empty();
        for kind in type_param_kinds {
            local_context.push_type(kind.clone());
        }

        let mut body = generic_term.clone();
        while let Some((binder_type, binder_body)) = body.as_ref().split_forall() {
            let fresh_var = local_context.push_type(binder_type.to_owned()) as AtomId;
            body = binder_body
                .to_owned()
                .substitute_bound(0, &Term::new_variable(fresh_var))
                .shift_bound(0, -1);
        }
        let literal = Self::try_term_to_single_checker_literal(&body)?;
        Some(Clause::from_literals_unnormalized(
            vec![literal],
            &local_context,
        ))
    }

    /// Rebuild a single-literal negated-existential claim as a checker clause.
    fn try_deserialize_exists_literal_clause(
        generic_term: &Term,
        type_param_kinds: &[Term],
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let mut local_context = LocalContext::empty();
        for kind in type_param_kinds {
            local_context.push_type(kind.clone());
        }

        let args = Self::split_symbol_application(generic_term, Symbol::Not, 1)?;
        let negate_literal = true;
        let mut body = args[0].clone();

        let mut saw_exists = false;
        while let Some((binder_type, binder_body)) = body.as_ref().split_exists() {
            saw_exists = true;
            let fresh_var = local_context.push_type(binder_type.to_owned()) as AtomId;
            body = binder_body
                .to_owned()
                .substitute_bound(0, &Term::new_variable(fresh_var))
                .shift_bound(0, -1);
        }
        if !saw_exists {
            return None;
        }

        let mut literal = Self::try_term_to_single_checker_literal(&body)?;
        if negate_literal {
            literal = literal.negate();
        }
        let clause = Clause::from_literals_unnormalized(vec![literal], &local_context);
        let quoted = kernel_context.quote_clause(&clause, None, None, false);
        if quoted.has_arbitrary() {
            return None;
        }
        Some(clause)
    }

    /// Detect whether a quoted plain-claim clause still mentions its local variables.
    fn clause_references_local_vars(clause: &Clause) -> bool {
        (0..clause.context.len()).any(|var_id| {
            clause.literals.iter().any(|literal| {
                literal.left.has_variable(var_id as AtomId)
                    || literal.right.has_variable(var_id as AtomId)
            })
        })
    }

    /// Split an application headed by a specific builtin symbol.
    fn split_symbol_application(term: &Term, symbol: Symbol, arity: usize) -> Option<Vec<Term>> {
        let (head, args) = term.as_ref().split_application_multi()?;
        if args.len() != arity {
            return None;
        }
        match head.get_head_atom() {
            Atom::Symbol(s) if *s == symbol => Some(args),
            _ => None,
        }
    }

    /// Convert a checker-inline term back into a single literal when possible.
    fn try_term_to_single_checker_literal(term: &Term) -> Option<Literal> {
        if let Some(args) = Self::split_symbol_application(term, Symbol::Not, 1) {
            if let Some(eq_args) = Self::split_symbol_application(&args[0], Symbol::Eq, 3) {
                return Some(Literal::not_equals(eq_args[1].clone(), eq_args[2].clone()));
            }
            return Some(Literal::negative(args[0].clone()));
        }
        if let Some(args) = Self::split_symbol_application(term, Symbol::Eq, 3) {
            return Some(Literal::equals(args[1].clone(), args[2].clone()));
        }
        if Self::split_symbol_application(term, Symbol::And, 2).is_some()
            || Self::split_symbol_application(term, Symbol::Or, 2).is_some()
            || matches!(
                term.as_ref().decompose(),
                Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _)
                    | Decomposition::Lambda(_, _)
            )
        {
            return None;
        }
        Some(Literal::positive(term.clone()))
    }

    /// Return the fixed roundtrip error prefix for claim-with-args serialization.
    fn claim_with_args_roundtrip_error() -> &'static str {
        "claim-with-args serialization did not roundtrip"
    }
}
