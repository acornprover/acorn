use std::collections::HashMap;

use crate::code_generator::{CodeGenerator, Error as CodeGenError};
use crate::elaborator::acorn_type::{AcornType, PotentialType, TypeParam, Typeclass};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::to_term::lower_value_to_term;
use crate::elaborator::to_term::{lower_value_to_term_existing, TypeVarMap};
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
use crate::syntax::expression::Expression;
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

    /// Serialize a claim in clause-plus-arguments form and require an exact roundtrip.
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
        let generic_value = kernel_context.quote_clause(claim.clause(), None, None, false);
        let generic_code = generator.value_to_code(&generic_value)?;
        let standalone_arg_context = LocalContext::from_types(
            local_context
                .get_var_types()
                .iter()
                .take_while(|var_type| {
                    var_type
                        .as_ref()
                        .is_some_and(|term| term.as_ref().is_type_param_kind())
                })
                .flatten()
                .cloned()
                .collect(),
        );
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
            let (arg_context, scope_len) = if substituted_arg_term.max_variable().is_none() {
                (LocalContext::empty(), 0)
            } else {
                (
                    standalone_arg_context.clone(),
                    standalone_arg_context.len() as AtomId,
                )
            };
            let arg_value =
                kernel_context.quote_term_with_context(&substituted_arg_term, &arg_context, true);
            let arg_value =
                Self::rebase_value_to_standalone(&arg_value, scope_len).map_err(|err| {
                    CodeGenError::GeneratedBadCode(format!(
                        "{} [claim arg term: {}; quoted: {}]",
                        err, substituted_arg_term, arg_value
                    ))
                })?;
            value_arg_values.push(arg_value.clone());
            if let Decomposition::Atom(Atom::FreeVariable(mapped_var_id)) =
                substituted_arg_term.as_ref().decompose()
            {
                if let Some(Some(mapped_name)) = value_decl_name_by_var.get(*mapped_var_id as usize)
                {
                    value_arg_codes.push(mapped_name.clone());
                    continue;
                }
            }
            value_arg_codes.push(generator.value_to_code(&arg_value)?);
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

        let lambda_body_value = match &generic_value {
            AcornValue::ForAll(_, body) => body.as_ref().clone(),
            _ => generic_value.clone(),
        };
        let roundtrip_function = AcornValue::type_apply(
            AcornValue::lambda(value_lambda_arg_types, lambda_body_value),
            roundtrip_type_param_names.clone(),
            roundtrip_type_param_constraints.clone(),
            roundtrip_type_args.clone(),
        );
        let mut expected_kernel_context = kernel_context.clone();
        let expected_roundtrip_claim = Self::expected_roundtrip_claim(
            claim,
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
        let mut evaluator = Evaluator::new_with_allow_choose(project, bindings, None, allow_choose);
        let value = evaluator.evaluate_value(expr, Some(&AcornType::Bool))?;
        Self::try_deserialize_claim_value(value, kernel_context)
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

    /// Rebuild the canonical claim defined by the current clause and argument codecs.
    fn expected_roundtrip_claim(
        claim: &Claim,
        type_args: &[AcornType],
        args: &[AcornValue],
        kernel_context: &mut KernelContext,
    ) -> Result<Claim, CodeGenError> {
        let clause = Self::canonicalize_roundtrip_clause(claim.clause());
        let var_map = Self::build_claim_var_map(type_args, args, kernel_context)?;
        Self::claim_with_var_map(clause, var_map)
    }

    /// Canonicalize a clause into the exact literal shapes produced by `lower_clause`.
    fn canonicalize_roundtrip_clause(clause: &Clause) -> Clause {
        let literals = clause
            .literals
            .iter()
            .map(Self::canonicalize_roundtrip_literal)
            .collect();
        Clause::from_literals_unnormalized(literals, clause.get_local_context())
    }

    /// Canonicalize one literal into the shape the clause codec currently reconstructs.
    fn canonicalize_roundtrip_literal(literal: &Literal) -> Literal {
        if literal.is_signed_term() {
            if let Some(eq_args) = Self::split_symbol_application(&literal.left, Symbol::Eq, 3) {
                if literal.positive {
                    return Literal::equals(eq_args[1].clone(), eq_args[2].clone());
                }
                return Literal::not_equals(eq_args[1].clone(), eq_args[2].clone());
            }
        }
        literal.clone()
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
        if !function_value.type_param_names.is_empty()
            && (function_value.type_param_names.len()
                != function_value.type_param_constraints.len()
                || function_value.type_param_names.len() != function_value.type_args.len())
        {
            return Err(CodeGenError::GeneratedBadCode(
                "type-argument metadata does not match type argument count".to_string(),
            ));
        }

        let (type_param_kinds, type_var_map) = Self::build_claim_type_param_kinds_and_map(
            &function_value.type_param_names,
            &function_value.type_param_constraints,
            kernel_context,
        );
        let generic_value = AcornValue::forall(function_value.arg_types, function_value.body);
        let generic_term =
            lower_value_to_term_existing(kernel_context, &generic_value, type_var_map.as_ref())?;
        let generic_term = normalize_term(&generic_term);
        let clause = Self::deserialize_claim_clause(
            &generic_term,
            &type_param_kinds,
            kernel_context,
            type_var_map,
        )?;
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

    /// Split an already-evaluated claim expression into a function half and argument list.
    fn try_deserialize_claim_value(
        value: AcornValue,
        kernel_context: &mut KernelContext,
    ) -> Result<Option<Claim>, CodeGenError> {
        match value {
            AcornValue::Application(app) => {
                Self::deserialize_claim_with_args_parts(*app.function, app.args, kernel_context)
            }
            other => Self::deserialize_claim_with_args_parts(other, vec![], kernel_context),
        }
    }

    /// Build both the type-parameter kind list and the lowering map for claim bodies.
    fn build_claim_type_param_kinds_and_map(
        type_param_names: &[String],
        type_param_constraints: &[Option<Typeclass>],
        kernel_context: &mut KernelContext,
    ) -> (Vec<Term>, Option<HashMap<String, (AtomId, Term)>>) {
        if type_param_names.is_empty() {
            return (vec![], None);
        }

        let mut kinds = vec![];
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
            kinds.push(var_type.clone());
            map.insert(name.clone(), (i as AtomId, var_type));
        }
        (kinds, Some(map))
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
                _ => None,
            },
            _ => None,
        }
    }

    /// Rebase a quoted claim argument so it can stand alone outside the clause's local scope.
    fn rebase_value_to_standalone(
        value: &AcornValue,
        scope_len: AtomId,
    ) -> Result<AcornValue, CodeGenError> {
        Ok(match value {
            AcornValue::Variable(var_id, var_type) => {
                if *var_id < scope_len {
                    AcornValue::Variable(*var_id, var_type.clone())
                } else {
                    AcornValue::Variable(var_id - scope_len, var_type.clone())
                }
            }
            AcornValue::Constant(constant) => AcornValue::Constant(constant.clone()),
            AcornValue::Application(app) => AcornValue::apply(
                Self::rebase_value_to_standalone(&app.function, scope_len)?,
                app.args
                    .iter()
                    .map(|arg| Self::rebase_value_to_standalone(arg, scope_len))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            AcornValue::TypeApplication(app) => AcornValue::type_apply(
                Self::rebase_value_to_standalone(&app.function, scope_len)?,
                app.type_param_names.clone(),
                app.type_param_constraints.clone(),
                app.type_args.clone(),
            ),
            AcornValue::Lambda(arg_types, body) => AcornValue::lambda(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, scope_len + arg_types.len() as AtomId)?,
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(Self::rebase_value_to_standalone(left, scope_len)?),
                Box::new(Self::rebase_value_to_standalone(right, scope_len)?),
            ),
            AcornValue::Not(value) => AcornValue::Not(Box::new(Self::rebase_value_to_standalone(
                value, scope_len,
            )?)),
            AcornValue::Try(value, unwrapped_type) => AcornValue::Try(
                Box::new(Self::rebase_value_to_standalone(value, scope_len)?),
                unwrapped_type.clone(),
            ),
            AcornValue::ForAll(arg_types, body) => AcornValue::forall(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, scope_len + arg_types.len() as AtomId)?,
            ),
            AcornValue::Exists(arg_types, body) => AcornValue::exists(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, scope_len + arg_types.len() as AtomId)?,
            ),
            AcornValue::Choose(choice_type, body) => AcornValue::choose(
                choice_type.clone(),
                Self::rebase_value_to_standalone(body, scope_len + 1)?,
            ),
            AcornValue::Bool(value) => AcornValue::Bool(*value),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(Self::rebase_value_to_standalone(cond, scope_len)?),
                Box::new(Self::rebase_value_to_standalone(if_value, scope_len)?),
                Box::new(Self::rebase_value_to_standalone(else_value, scope_len)?),
            ),
            AcornValue::Match(scrutinee, cases) => AcornValue::Match(
                Box::new(Self::rebase_value_to_standalone(scrutinee, scope_len)?),
                cases
                    .iter()
                    .map(|case| {
                        let case_scope_len = scope_len + case.new_vars.len() as AtomId;
                        Ok(crate::elaborator::acorn_value::MatchCase {
                            new_vars: case.new_vars.clone(),
                            pattern: Self::rebase_value_to_standalone(
                                &case.pattern,
                                case_scope_len,
                            )?,
                            result: Self::rebase_value_to_standalone(&case.result, case_scope_len)?,
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        })
                    })
                    .collect::<Result<Vec<_>, CodeGenError>>()?,
            ),
        })
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
        for (var_id, arg) in args.iter().enumerate() {
            let term = lower_value_to_term(
                kernel_context,
                arg,
                NewConstantType::Local,
                type_var_map.as_ref(),
            )?;
            let term = normalize_term(&term);
            let term = kernel_context.term_to_claim_arg(&term)?;
            var_map.set((value_offset + var_id) as AtomId, term);
        }
        Ok(var_map)
    }

    /// Reconstruct the checker-facing claim clause from the lowered generic term.
    fn deserialize_claim_clause(
        generic_term: &Term,
        type_param_kinds: &[Term],
        kernel_context: &mut KernelContext,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Clause, CodeGenError> {
        if Self::term_has_inline_clause_shape(generic_term, true) {
            return Ok(
                Self::try_deserialize_inline_clause(generic_term, type_param_kinds)
                    .expect("inline clause shape should deserialize"),
            );
        }
        if Self::should_preserve_single_literal_claim(generic_term) {
            if let Some(clause) =
                Self::try_deserialize_single_literal_clause(generic_term, type_param_kinds)
            {
                return Ok(clause);
            }
        }

        let clauses = kernel_context.term_to_checker_clauses(generic_term, type_var_map)?;
        if clauses.len() != 1 {
            if let Some(clause) =
                Self::try_deserialize_single_literal_clause(generic_term, type_param_kinds)
            {
                return Ok(clause);
            }
            if let Some(clause) =
                Self::try_deserialize_single_formula_clause(generic_term, type_param_kinds)
            {
                return Ok(clause);
            }
            return Err(CodeGenError::GeneratedBadCode(
                "claim-with-args body did not lower to a single claim clause".to_string(),
            ));
        }

        Ok(clauses.into_iter().next().expect("clauses has one element"))
    }

    /// Construct a claim that has no extra argument map entries.
    fn claim_from_clause(clause: Clause) -> Result<Claim, CodeGenError> {
        Claim::new(clause, VariableMap::new()).map_err(CodeGenError::GeneratedBadCode)
    }

    /// Construct a claim from a clause and an explicit variable map.
    fn claim_with_var_map(clause: Clause, var_map: VariableMap) -> Result<Claim, CodeGenError> {
        Claim::new(clause, var_map).map_err(CodeGenError::GeneratedBadCode)
    }

    /// Detect when a plain claim must preserve its single-literal shape.
    fn should_preserve_single_literal_claim(term: &Term) -> bool {
        let body = Self::strip_foralls(term);
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

    /// Detect when the claim body is already an inline clause-shaped boolean formula.
    fn term_has_inline_clause_shape(term: &Term, positive: bool) -> bool {
        if let Some(args) = Self::split_symbol_application(term, Symbol::Not, 1) {
            return Self::term_has_inline_clause_shape(&args[0], !positive);
        }

        if positive {
            if Self::split_symbol_application(term, Symbol::Or, 2).is_some() {
                return true;
            }
        } else if Self::split_symbol_application(term, Symbol::And, 2).is_some() {
            return true;
        }

        if let Some((_binder_type, body)) = term.as_ref().split_forall() {
            return Self::term_has_inline_clause_shape(&body.to_owned(), positive);
        }

        false
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

    /// Rebuild a single signed formula clause when no finer checker clause form exists.
    fn try_deserialize_single_formula_clause(
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
        Some(Clause::from_literals_unnormalized(
            vec![Literal::positive(body)],
            &local_context,
        ))
    }

    /// Rebuild an inline disjunction into the exact checker literal list.
    fn try_deserialize_inline_clause(
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

        let literals = Self::try_term_to_inline_clause_literals(&body, true)?;
        Some(Clause::from_literals_unnormalized(literals, &local_context))
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

    /// Flatten one inline boolean formula into the checker literal list it represents.
    fn try_term_to_inline_clause_literals(term: &Term, positive: bool) -> Option<Vec<Literal>> {
        if let Some(args) = Self::split_symbol_application(term, Symbol::Not, 1) {
            return Self::try_term_to_inline_clause_literals(&args[0], !positive);
        }

        if positive {
            if let Some(args) = Self::split_symbol_application(term, Symbol::Or, 2) {
                let mut literals = Self::try_term_to_inline_clause_literals(&args[0], true)?;
                literals.extend(Self::try_term_to_inline_clause_literals(&args[1], true)?);
                return Some(literals);
            }
        } else if let Some(args) = Self::split_symbol_application(term, Symbol::And, 2) {
            let mut literals = Self::try_term_to_inline_clause_literals(&args[0], false)?;
            literals.extend(Self::try_term_to_inline_clause_literals(&args[1], false)?);
            return Some(literals);
        }

        if positive {
            if let Some(literal) = Self::try_term_to_single_checker_literal(term) {
                return Some(vec![literal]);
            }
            return Some(vec![Literal::positive(term.clone())]);
        }

        if let Some(args) = Self::split_symbol_application(term, Symbol::Eq, 3) {
            return Some(vec![Literal::not_equals(args[1].clone(), args[2].clone())]);
        }

        Some(vec![Literal::negative(term.clone())])
    }

    /// Return the fixed roundtrip error prefix for claim-with-args serialization.
    fn claim_with_args_roundtrip_error() -> &'static str {
        "claim-with-args serialization did not roundtrip"
    }
}
