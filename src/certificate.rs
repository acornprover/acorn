use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use std::borrow::Cow;

use crate::code_generator::{CodeGenerator, Error as CodeGenError};
use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_type::PotentialType;
use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::to_term::elaborate_value_to_term;
use crate::elaborator::to_term::{elaborate_value_to_term_existing, TypeVarMap};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::{CertificateStep, Claim};
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::clause::Clause;
use crate::kernel::clausifier::Clausifier;
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::{Decomposition, Term};
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::module::ModuleDescriptor;
use crate::project::Project;
use crate::prover::proof::ConcreteStep;
use crate::syntax::expression::Expression;
use crate::syntax::statement::{Statement, StatementInfo};
use crate::syntax::token::TokenType;

/// Information about a single line in a checked certificate proof.
#[derive(Debug, Clone)]
pub struct CertificateLine {
    /// The structured clause value after denormalization.
    pub value: AcornValue,

    /// The statement from the certificate (the code line).
    pub statement: String,

    /// The reason this step was accepted.
    pub reason: StepReason,
}

/// A successfully checked certificate, including how many proof lines were consumed.
#[derive(Debug, Clone)]
pub struct CheckedCertificate {
    pub lines: Vec<CertificateLine>,
    pub consumed_proof_steps: usize,
}

fn value_to_code(
    value: &AcornValue,
    bindings: &Cow<BindingMap>,
    code_line: Option<&str>,
) -> String {
    // First try normal code generation.
    let mut code_gen = CodeGenerator::new_for_certificate(bindings);
    if let Ok(code) = code_gen.value_to_code(&value) {
        return code;
    }

    // If we have the original certificate line, prefer it over reconstructed internal output.
    if let Some(code_line) = code_line {
        return code_line.to_string();
    }

    "<missing>".to_string()
}

/// A proof certificate containing the concrete proof steps as strings.
///
/// # Design: Robustness to Refactoring
///
/// A key design goal is that certificates should be robust to common refactorings:
/// - **Renaming**: If a theorem is renamed, certificates that don't use it should still work.
/// - **Reordering**: If constants are reordered (changing internal IDs), certificates should
///   still work because they use names, not numeric IDs.
/// - **Adding/removing definitions**: Unrelated changes shouldn't invalidate certificates.
///
/// This is achieved by using string-based proof steps that reference constants by name.
/// When a certificate is checked, names are resolved to current IDs at parse time.
/// This avoids the "brittleness" problem where machine-generated proofs break due to
/// unrelated codebase changes.
///
/// The string format also allows the checker to figure out *how* to verify each claim
/// (which theorems to use, etc.) rather than having the certificate spell it out.
/// This means certificates don't break when the *justification* for a claim changes,
/// only when the claim itself becomes unprovable.
///
/// See also: `ConcreteProof` for the in-memory representation with resolved IDs.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Certificate {
    /// The name of the goal that was proved
    pub goal: String,

    /// The proof steps as strings.
    /// None indicates no proof exists for this goal.
    /// This is useful as a placeholder to indicate that we need to find a proof.
    /// Some(vec![]) indicates a trivial proof requiring no steps.
    pub proof: Option<Vec<String>>,
}

impl Certificate {
    fn claim_with_args_roundtrip_error() -> &'static str {
        "claim-with-args serialization did not roundtrip"
    }

    fn logical_symbol_arity(symbol: Symbol) -> Option<usize> {
        match symbol {
            Symbol::Not => Some(1),
            Symbol::And | Symbol::Or => Some(2),
            Symbol::Eq => Some(3),
            Symbol::Ite => Some(4),
            Symbol::Choose => Some(2),
            _ => None,
        }
    }

    fn contains_partial_logical_builtin(term: crate::kernel::term::TermRef<'_>) -> bool {
        fn head_symbol_and_arg_count(
            mut term: crate::kernel::term::TermRef<'_>,
        ) -> Option<(Symbol, usize)> {
            let mut arg_count = 0;
            loop {
                match term.decompose() {
                    Decomposition::Application(func, _) => {
                        arg_count += 1;
                        term = func;
                    }
                    Decomposition::Atom(Atom::Symbol(symbol)) => return Some((*symbol, arg_count)),
                    _ => return None,
                }
            }
        }

        if let Some((symbol, arg_count)) = head_symbol_and_arg_count(term) {
            if let Some(arity) = Self::logical_symbol_arity(symbol) {
                if arg_count < arity {
                    return true;
                }
                for arg in term.iter_args() {
                    if Self::contains_partial_logical_builtin(arg) {
                        return true;
                    }
                }
                return false;
            }
        }

        match term.decompose() {
            Decomposition::Atom(_) => false,
            Decomposition::Application(_, _) => false,
            Decomposition::Pi(func, arg)
            | Decomposition::Lambda(func, arg)
            | Decomposition::ForAll(func, arg)
            | Decomposition::Exists(func, arg) => {
                Self::contains_partial_logical_builtin(func)
                    || Self::contains_partial_logical_builtin(arg)
            }
        }
    }

    fn references_value_local(
        term: crate::kernel::term::TermRef<'_>,
        local_context: &LocalContext,
    ) -> bool {
        (0..local_context.len()).any(|var_id| {
            local_context
                .get_var_type(var_id)
                .is_some_and(|var_type| !var_type.as_ref().is_type_param_kind())
                && term.has_variable(var_id as AtomId)
        })
    }

    fn clause_references_local_vars(clause: &Clause) -> bool {
        (0..clause.context.len()).any(|var_id| {
            clause.literals.iter().any(|literal| {
                literal.left.has_variable(var_id as AtomId)
                    || literal.right.has_variable(var_id as AtomId)
            })
        })
    }

    fn claim_requires_specialized_serialization(
        claim: &Claim,
        _kernel_context: &KernelContext,
    ) -> bool {
        let local_context = claim.clause.get_local_context();
        claim.var_map.iter().any(|(_, term)| {
            Self::contains_partial_logical_builtin(term.as_ref())
                || Self::references_value_local(term.as_ref(), local_context)
        })
    }

    fn rebase_value_to_standalone(
        value: &AcornValue,
        scope_len: AtomId,
    ) -> Result<AcornValue, CodeGenError> {
        Ok(match value {
            AcornValue::Variable(var_id, var_type) => {
                if *var_id < scope_len {
                    return Err(CodeGenError::GeneratedBadCode(
                        "claim argument unexpectedly referenced an outer local".to_string(),
                    ));
                }
                AcornValue::Variable(var_id - scope_len, var_type.clone())
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
                Self::rebase_value_to_standalone(body, scope_len)?,
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
                Self::rebase_value_to_standalone(body, scope_len)?,
            ),
            AcornValue::Exists(arg_types, body) => AcornValue::exists(
                arg_types.clone(),
                Self::rebase_value_to_standalone(body, scope_len)?,
            ),
            AcornValue::Choose(choice_type, body) => AcornValue::choose(
                choice_type.clone(),
                Self::rebase_value_to_standalone(body, scope_len)?,
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
                        Ok(crate::elaborator::acorn_value::MatchCase {
                            new_vars: case.new_vars.clone(),
                            pattern: Self::rebase_value_to_standalone(&case.pattern, scope_len)?,
                            result: Self::rebase_value_to_standalone(&case.result, scope_len)?,
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        })
                    })
                    .collect::<Result<Vec<_>, CodeGenError>>()?,
            ),
        })
    }

    fn ensure_claim_code_parses_as_claim(code: String) -> Result<String, CodeGenError> {
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

    /// Create a new certificate with proof steps
    pub fn new(goal: String, proof: Vec<String>) -> Self {
        Certificate {
            goal,
            proof: Some(proof),
        }
    }

    /// Create a placeholder certificate with no proof
    pub fn placeholder(goal: String) -> Self {
        Certificate { goal, proof: None }
    }

    /// Trim this certificate's proof to the consumed prefix.
    pub fn trim_to_consumed_prefix(mut self, keep_steps: usize) -> Self {
        if let Some(proof) = &mut self.proof {
            proof.truncate(keep_steps);
        }
        self
    }

    /// Check if this certificate has a proof
    pub fn has_proof(&self) -> bool {
        self.proof.is_some()
    }

    /// Convert a ConcreteProof to a Certificate (string format).
    ///
    /// This is the serialization boundary where resolved IDs are converted back to names.
    /// Requires the kernel_context (to denormalize clauses)
    /// and the bindings (to generate readable names).
    pub fn from_concrete_steps(
        goal: String,
        concrete_steps: &[ConcreteStep],
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<Certificate, CodeGenError> {
        let mut generator = CodeGenerator::new_for_certificate(bindings);
        let mut generation_kernel_context = kernel_context.clone();
        let mut ordered_steps: Vec<CertificateStep> = Vec::new();

        for step in concrete_steps {
            let cert_steps = generator
                .concrete_step_to_certificate_steps(step, &mut generation_kernel_context)
                .map_err(|err| {
                    CodeGenError::GeneratedBadCode(format!(
                        "{} [while converting concrete clause {}]",
                        err, step.generic
                    ))
                })?;
            for cert_step in cert_steps {
                if !ordered_steps.contains(&cert_step) {
                    ordered_steps.push(cert_step);
                }
            }
        }

        let mut answer = Vec::new();
        for step in &ordered_steps {
            let line = match step {
                CertificateStep::Claim(claim)
                    if !claim.clause.get_local_context().is_empty()
                        && !Self::claim_requires_specialized_serialization(
                            claim,
                            &generation_kernel_context,
                        ) =>
                {
                    let specialized_clause = claim
                        .var_map
                        .specialize_clause(&claim.clause, &generation_kernel_context);
                    match Self::serialize_claim_with_names(
                        claim,
                        &generation_kernel_context,
                        bindings,
                    ) {
                        Ok(line) => line,
                        Err(_) => match generator
                            .certificate_step_to_code(step, &generation_kernel_context)
                        {
                            Ok(line) => line,
                            Err(inner) => {
                                return Err(CodeGenError::GeneratedBadCode(format!(
                                    "{} [while serializing certificate claim step {}]",
                                    inner, specialized_clause
                                )));
                            }
                        },
                    }
                }
                _ => generator
                    .certificate_step_to_code(step, &generation_kernel_context)
                    .map_err(|err| {
                        CodeGenError::GeneratedBadCode(format!(
                            "{} [while serializing certificate step]",
                            err
                        ))
                    })?,
            };
            let line = Self::ensure_claim_code_parses_as_claim(line)?;
            answer.push(line);
        }

        Ok(Certificate::new(goal, answer))
    }

    /// Convert a ConcreteProof to a Certificate (string format).
    ///
    /// This is the serialization boundary where resolved IDs are converted back to names.
    /// Requires the kernel_context (to denormalize clauses)
    /// and the bindings (to generate readable names).
    pub fn from_concrete_proof(
        concrete_proof: &ConcreteProof,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<Certificate, CodeGenError> {
        let mut concrete_steps = Vec::new();
        for clause in &concrete_proof.claims {
            // Create a ConcreteStep with an identity mapping (clause is already specialized)
            concrete_steps.push(ConcreteStep {
                generic: clause.clone(),
                var_maps: vec![(VariableMap::new(), clause.get_local_context().clone())],
            });
        }

        Certificate::from_concrete_steps(
            concrete_proof.goal.clone(),
            &concrete_steps,
            kernel_context,
            bindings,
        )
    }

    /// Parse all certificate proof lines into kernel-level certificate steps.
    ///
    /// Parsing may update bindings/kernel_context (for let...satisfy declarations), so callers
    /// should pass mutable views and then use the updated state for subsequent checking.
    pub fn parse_cert_steps(
        proof: &[String],
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        kernel_context: &mut Cow<KernelContext>,
    ) -> Result<Vec<CertificateStep>, CodeGenError> {
        let mut steps = Vec::with_capacity(proof.len());
        for code in proof {
            steps.push(Self::parse_code_line(
                code,
                project,
                bindings,
                kernel_context,
            )?);
        }
        Ok(steps)
    }

    /// Parse a single code line, updating bindings/kernel_context, and return structured result.
    pub fn parse_code_line(
        code: &str,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        kernel_context: &mut Cow<KernelContext>,
    ) -> Result<CertificateStep, CodeGenError> {
        let statement = Statement::parse_str_with_options(&code, true)?;
        let mut evaluator = Evaluator::new_with_allow_choose(project, bindings, None, true);
        let mut claim_step_from_expr =
            |expr: &Expression| -> Result<CertificateStep, CodeGenError> {
                let value = evaluator.evaluate_value(expr, Some(&AcornType::Bool))?;
                if let Some(claim) = Self::try_deserialize_claim_with_args_value(
                    value.clone(),
                    bindings.as_ref(),
                    kernel_context.to_mut(),
                )? {
                    return Ok(CertificateStep::Claim(claim));
                }
                let term = elaborate_value_to_term_existing(kernel_context.to_mut(), &value, None)?;
                if Self::should_preserve_single_literal_claim(&term) {
                    if let Some(clause) = Self::try_deserialize_single_literal_clause(&term, &[]) {
                        return Ok(CertificateStep::Claim(Claim {
                            clause,
                            var_map: VariableMap::new(),
                        }));
                    }
                }
                let mut view = Clausifier::new_mut(kernel_context.to_mut(), None);
                let clauses = view.clausify_term_to_denormalized_clauses(&term)?;
                if clauses.len() != 1 {
                    // A claim line may intentionally keep a boolean connective inline
                    // as a single signed literal term (for example, `a and b`) rather
                    // than expanding it into multiple CNF clauses.
                    let simple_term = view.clausify_term_to_simple_term(&term)?;
                    return Ok(CertificateStep::Claim(Claim {
                        clause: crate::kernel::clause::Clause::from_literals_unnormalized(
                            vec![Literal::positive(simple_term)],
                            &LocalContext::empty(),
                        ),
                        var_map: VariableMap::new(),
                    }));
                }
                let clause = clauses
                    .into_iter()
                    .next()
                    .expect("clauses has exactly one element");
                if !clause.get_local_context().is_empty()
                    && !Self::clause_references_local_vars(&clause)
                {
                    let simple_term = view.clausify_term_to_simple_term(&term)?;
                    let literal = Self::try_term_to_single_denormalized_literal(&simple_term)
                        .unwrap_or_else(|| Literal::positive(simple_term));
                    return Ok(CertificateStep::Claim(Claim {
                        clause: crate::kernel::clause::Clause::from_literals_unnormalized(
                            vec![literal],
                            &LocalContext::empty(),
                        ),
                        var_map: VariableMap::new(),
                    }));
                }
                Ok(CertificateStep::Claim(Claim {
                    clause,
                    var_map: VariableMap::new(),
                }))
            };

        match statement.statement {
            StatementInfo::VariableSatisfy(_) => Err(CodeGenError::GeneratedBadCode(
                "certificate `let ... satisfy` steps are no longer supported".to_string(),
            )),
            StatementInfo::Claim(claim) => claim_step_from_expr(&claim.claim),
            _ => Err(CodeGenError::GeneratedBadCode(format!(
                "Expected a claim or let...satisfy statement, got: {}",
                code
            ))),
        }
    }

    /// Serializes a claim in a clause-plus-arguments form.
    ///
    /// Example output:
    /// `function(x0: Nat) { bar(x0) }(a)`
    ///
    /// This is currently a standalone helper and is not wired into normal certificate
    /// serialization.
    pub fn serialize_claim_with_args(
        claim: &Claim,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        Self::serialize_claim_with_names(claim, kernel_context, bindings)
    }

    fn infer_in_scope_type_arg(kind: &AcornType, bindings: &BindingMap) -> Option<AcornType> {
        let mut candidates: Vec<(String, AcornType)> = vec![];
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

    fn expected_roundtrip_claim(claim: &Claim, type_var_map: &VariableMap) -> Claim {
        let local_context = claim.clause.get_local_context();
        let mut expected_var_map = VariableMap::new();

        for var_id in 0..local_context.len() {
            let var_id = var_id as AtomId;
            if let Some(term) = claim.var_map.get_mapping(var_id) {
                expected_var_map.set(var_id, apply_to_term(term.as_ref(), type_var_map));
                continue;
            }
            if let Some(type_term) = type_var_map.get_mapping(var_id) {
                expected_var_map.set(var_id, type_term.clone());
            }
        }

        Claim {
            clause: claim.clause.clone(),
            var_map: expected_var_map,
        }
    }

    fn serialize_claim_with_names(
        claim: &Claim,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        let local_context = claim.clause.get_local_context();
        let var_count = local_context.len();
        if var_count == 0 {
            return Err(CodeGenError::GeneratedBadCode(
                "cannot serialize claim-with-args for a clause with no local variables".to_string(),
            ));
        }

        let mut generator = CodeGenerator::new_for_certificate(bindings);
        let generic_value = kernel_context.denormalize(&claim.clause, None, None, false);
        let generic_code = generator.value_to_code(&generic_value)?;
        let body_code = if matches!(generic_value, AcornValue::ForAll(_, _)) {
            let generic_expr = Expression::parse_value_string(&generic_code)?;
            match generic_expr {
                Expression::Binder(token, _, body, _) if token.token_type == TokenType::ForAll => {
                    body.to_string()
                }
                _ => {
                    return Err(CodeGenError::GeneratedBadCode(
                        "expected denormalized generic claim to have forall shape".to_string(),
                    ));
                }
            }
        } else {
            generic_code
        };

        // Use the full local context rather than only variables appearing directly
        // in the clause literals. Claim argument terms can reference additional
        // in-scope variables (for example through nested lambdas).
        let used_var_count = local_context.len();

        let kernel_context = kernel_context;

        let mut type_param_decl_codes: Vec<String> = vec![];
        let mut type_arg_codes: Vec<String> = vec![];
        let mut roundtrip_type_param_names: Vec<String> = vec![];
        let mut roundtrip_type_param_constraints: Vec<
            Option<crate::elaborator::acorn_type::Typeclass>,
        > = vec![];
        let mut roundtrip_type_args: Vec<AcornType> = vec![];
        let mut resolved_type_var_map = VariableMap::new();
        let mut value_decl_codes: Vec<String> = vec![];
        let mut value_arg_codes: Vec<String> = vec![];
        let mut value_lambda_arg_types: Vec<AcornType> = vec![];
        let mut value_arg_values: Vec<AcornValue> = vec![];
        // Keep declaration names aligned with CodeGenerator's own naming strategy so the
        // lambda body and argument declarations use the same identifiers, even when
        // lower indices (e.g. x0, x1) are already occupied in bindings.
        let mut next_value_decl_id: u32 = 0;
        let mut value_decl_name_by_var: Vec<Option<String>> = vec![None; used_var_count];

        for var_id in 0..used_var_count {
            let var_type = local_context
                .get_var_type(var_id)
                .expect("local context should provide all variable types");
            if var_type.as_ref().is_type_param_kind() {
                continue;
            }
            if claim.var_map.get_mapping(var_id as AtomId).is_none() {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "missing claim var map entry for x{}",
                    var_id
                )));
            }
            let var_name = bindings.next_indexed_var('x', &mut next_value_decl_id);
            value_decl_name_by_var[var_id] = Some(var_name);
        }

        for var_id in 0..used_var_count {
            let var_type = local_context
                .get_var_type(var_id)
                .expect("local context should provide all variable types")
                .clone();

            let arg_term = claim.var_map.get_mapping(var_id as AtomId);

            if var_type.as_ref().is_type_param_kind() {
                let type_param_name = format!("T{}", var_id);
                let kind =
                    kernel_context.denormalize_type_with_context(var_type, local_context, false);
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
                    _ => {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "invalid type-parameter kind for x{}",
                            var_id
                        )));
                    }
                };
                type_param_decl_codes.push(decl_code);
                roundtrip_type_param_names.push(type_param_name.clone());
                roundtrip_type_param_constraints.push(roundtrip_constraint.clone());

                let mapped_type = arg_term.map(|term| {
                    kernel_context.denormalize_type_with_context(term.clone(), local_context, false)
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
                            // No concrete in-scope type to instantiate with. Keep this line
                            // self-contained by applying the type lambda to its own local type
                            // parameter (e.g. function[T0: C] { ... }[T0]).
                            (None, type_param_name.clone())
                        }
                    }
                };
                if let Some(selected_type) = selected_type {
                    let selected_term = kernel_context
                        .type_store
                        .to_type_term_with_vars(&selected_type, None);
                    resolved_type_var_map.set(var_id as AtomId, selected_term);
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
            let acorn_type =
                kernel_context.denormalize_type_with_context(var_type, local_context, false);
            value_lambda_arg_types.push(acorn_type.clone());
            let type_code = generator.type_to_expr(&acorn_type)?.to_string();
            value_decl_codes.push(format!("{}: {}", var_name, type_code));

            let substituted_arg_term = apply_to_term(arg_term.as_ref(), &resolved_type_var_map);
            let arg_value = kernel_context.denormalize_term_with_context(
                &substituted_arg_term,
                local_context,
                false,
            );
            let arg_value =
                Self::rebase_value_to_standalone(&arg_value, local_context.len() as AtomId)?;
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
                    .var_map
                    .specialize_clause(&claim.clause, kernel_context);
                let specialized_value = kernel_context.denormalize(&specialized, None, None, true);
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
            roundtrip_type_param_names,
            roundtrip_type_param_constraints,
            roundtrip_type_args,
        );
        let roundtrip_value = AcornValue::apply(roundtrip_function, value_arg_values);
        let mut roundtrip_kernel_context = kernel_context.clone();
        let expected_roundtrip_claim =
            Self::expected_roundtrip_claim(claim, &resolved_type_var_map);
        if Self::try_deserialize_claim_with_args_value(
            roundtrip_value,
            bindings,
            &mut roundtrip_kernel_context,
        )?
        .as_ref()
            != Some(&expected_roundtrip_claim)
        {
            return Err(CodeGenError::GeneratedBadCode(
                Self::claim_with_args_roundtrip_error().to_string(),
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

    /// Deserializes a claim produced by `serialize_claim_with_args`.
    ///
    /// This is currently a standalone helper and is not wired into normal certificate
    /// parsing.
    pub fn deserialize_claim_with_args(
        code: &str,
        project: &Project,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
    ) -> Result<Claim, CodeGenError> {
        let statement = Statement::parse_str_with_options(code, true)?;
        let StatementInfo::Claim(claim_statement) = statement.statement else {
            return Err(CodeGenError::GeneratedBadCode(
                "expected a claim expression".to_string(),
            ));
        };

        let mut evaluator = Evaluator::new_with_allow_choose(project, bindings, None, true);
        let evaluated = evaluator.evaluate_value(&claim_statement.claim, Some(&AcornType::Bool))?;
        let mut kernel_context_clone = kernel_context.clone();
        Self::try_deserialize_claim_with_args_value(evaluated, bindings, &mut kernel_context_clone)?
            .ok_or_else(|| {
                CodeGenError::GeneratedBadCode(
                    "expected a function(...) { ... }(...) claim shape".to_string(),
                )
            })
    }

    fn try_deserialize_claim_with_args_value(
        value: AcornValue,
        _bindings: &BindingMap,
        kernel_context: &mut KernelContext,
    ) -> Result<Option<Claim>, CodeGenError> {
        let mut type_param_names: Vec<String> = vec![];
        let mut type_param_constraints = vec![];
        let mut type_args = vec![];
        let (arg_types, body, args) = match value {
            AcornValue::Application(app) => match *app.function {
                AcornValue::Lambda(arg_types, body) => (arg_types, *body, app.args),
                AcornValue::TypeApplication(type_app) => match *type_app.function {
                    AcornValue::Lambda(arg_types, body) => {
                        type_param_names = type_app.type_param_names;
                        type_param_constraints = type_app.type_param_constraints;
                        type_args = type_app.type_args;
                        (arg_types, *body, app.args)
                    }
                    _ => return Ok(None),
                },
                _ => return Ok(None),
            },
            AcornValue::TypeApplication(type_app) => match *type_app.function {
                AcornValue::Lambda(arg_types, body) => {
                    type_param_names = type_app.type_param_names;
                    type_param_constraints = type_app.type_param_constraints;
                    type_args = type_app.type_args;
                    (arg_types, *body, vec![])
                }
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };

        if arg_types.is_empty() && type_param_names.is_empty() {
            return Ok(None);
        }
        if args.len() != arg_types.len() {
            return Err(CodeGenError::GeneratedBadCode(
                "argument count does not match function declaration".to_string(),
            ));
        }
        if !type_param_names.is_empty()
            && (type_param_names.len() != type_param_constraints.len()
                || type_param_names.len() != type_args.len())
        {
            return Err(CodeGenError::GeneratedBadCode(
                "type-argument metadata does not match type argument count".to_string(),
            ));
        }

        let mut kernel_context_clone = kernel_context.clone();
        let mut type_param_kinds = vec![];
        let type_var_map = if type_param_names.is_empty() {
            None
        } else {
            let mut map = HashMap::new();
            for (i, (name, constraint)) in type_param_names
                .iter()
                .zip(type_param_constraints.iter())
                .enumerate()
            {
                let var_type = if let Some(typeclass) = constraint {
                    let typeclass_id = kernel_context_clone.type_store.add_typeclass(typeclass);
                    Term::typeclass(typeclass_id)
                } else {
                    Term::type_sort()
                };
                type_param_kinds.push(var_type.clone());
                map.insert(name.clone(), (i as AtomId, var_type));
            }
            Some(map)
        };
        let generic_value = AcornValue::forall(arg_types, body);
        let generic_term = elaborate_value_to_term_existing(
            &mut kernel_context_clone,
            &generic_value,
            type_var_map.as_ref(),
        )?;
        if Self::term_has_inline_clause_shape(&generic_term, true) {
            let clause = Self::try_deserialize_inline_clause(&generic_term, &type_param_kinds)
                .expect("inline clause shape should deserialize");
            let var_map =
                Self::build_claim_var_map(type_args.as_slice(), args.as_slice(), kernel_context)?;
            return Ok(Some(Claim { clause, var_map }));
        }
        if Self::should_preserve_single_literal_claim(&generic_term) {
            if let Some(clause) =
                Self::try_deserialize_single_literal_clause(&generic_term, &type_param_kinds)
            {
                let var_map = Self::build_claim_var_map(
                    type_args.as_slice(),
                    args.as_slice(),
                    kernel_context,
                )?;
                return Ok(Some(Claim { clause, var_map }));
            }
        }

        let mut view = Clausifier::new_mut(&mut kernel_context_clone, type_var_map);
        let clauses = view.clausify_term_to_denormalized_clauses(&generic_term)?;
        if clauses.len() != 1 {
            if let Some(clause) =
                Self::try_deserialize_single_literal_clause(&generic_term, &type_param_kinds)
            {
                let var_map = Self::build_claim_var_map(
                    type_args.as_slice(),
                    args.as_slice(),
                    kernel_context,
                )?;
                return Ok(Some(Claim { clause, var_map }));
            }
            if let Some(clause) =
                Self::try_deserialize_single_formula_clause(&generic_term, &type_param_kinds)
            {
                let var_map = Self::build_claim_var_map(
                    type_args.as_slice(),
                    args.as_slice(),
                    kernel_context,
                )?;
                return Ok(Some(Claim { clause, var_map }));
            }
            // This lambda form only round-trips to `Claim { clause, var_map }` when
            // the body can be represented as a single inline clause. If it doesn't,
            // let callers fall back to plain claim parsing.
            return Ok(None);
        }
        let clause = clauses
            .into_iter()
            .next()
            .expect("clauses has exactly one element");

        let var_map =
            Self::build_claim_var_map(type_args.as_slice(), args.as_slice(), kernel_context)?;

        Ok(Some(Claim { clause, var_map }))
    }

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
            let term = {
                // Supported claim arguments can still mention selected-goal locals such
                // as `d` or `k`. Elaborate against the live context so those proof-scope locals
                // are interned before clausifying the argument term.
                let term = elaborate_value_to_term(
                    kernel_context,
                    arg,
                    NewConstantType::Local,
                    type_var_map.as_ref(),
                )?;
                let mut term_view = Clausifier::new_mut(kernel_context, None);
                term_view.clausify_term_for_claim_arg(&term)?
            };
            var_map.set((value_offset + var_id) as AtomId, term);
        }
        Ok(var_map)
    }

    fn split_symbol_application(term: &Term, symbol: Symbol, arity: usize) -> Option<Vec<Term>> {
        let (head, args) = term.as_ref().split_application_multi()?;
        if args.len() != arity {
            return None;
        }
        match head.get_head_atom() {
            crate::kernel::atom::Atom::Symbol(s) if *s == symbol => Some(args),
            _ => None,
        }
    }

    fn try_term_to_single_denormalized_literal(term: &Term) -> Option<Literal> {
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
        let literal = Self::try_term_to_single_denormalized_literal(&body)?;
        Some(Clause::from_literals_unnormalized(
            vec![literal],
            &local_context,
        ))
    }

    fn strip_foralls(term: &Term) -> Term {
        let mut body = term.clone();
        while let Some((_binder_type, binder_body)) = body.as_ref().split_forall() {
            body = binder_body.to_owned();
        }
        body
    }

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
    }

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
            if let Some(literal) = Self::try_term_to_single_denormalized_literal(term) {
                return Some(vec![literal]);
            }
            return Some(vec![Literal::positive(term.clone())]);
        }

        if let Some(args) = Self::split_symbol_application(term, Symbol::Eq, 3) {
            return Some(vec![Literal::not_equals(args[1].clone(), args[2].clone())]);
        }

        Some(vec![Literal::negative(term.clone())])
    }

    /// Check this certificate. It is expected that it has a proof.
    ///
    /// Consumes checker/bindings/kernel_context since checking mutates all three.
    pub fn check(
        &self,
        checker: Checker,
        project: &Project,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<Vec<CertificateLine>, CodeGenError> {
        Ok(self
            .check_with_usage(checker, project, bindings, kernel_context)?
            .lines)
    }

    /// Check this certificate and report how many proof lines were actually consumed.
    ///
    /// Consumes checker/bindings/kernel_context since checking mutates all three.
    pub fn check_with_usage(
        &self,
        mut checker: Checker,
        project: &Project,
        mut bindings: Cow<BindingMap>,
        mut kernel_context: Cow<KernelContext>,
    ) -> Result<CheckedCertificate, CodeGenError> {
        if checker.has_contradiction() {
            return Ok(CheckedCertificate {
                lines: Vec::new(),
                consumed_proof_steps: 0,
            });
        }
        let Some(proof) = &self.proof else {
            return Err(CodeGenError::NoProof);
        };
        let cert_steps =
            Self::parse_cert_steps(proof, project, &mut bindings, &mut kernel_context)?;
        let (checked_steps, consumed_proof_steps) =
            checker.check_cert_steps(&cert_steps, Some(proof), &kernel_context)?;
        let lines = checked_steps
            .into_iter()
            .map(|checked_step| {
                let value = kernel_context.denormalize(&checked_step.clause, None, None, false);
                let statement = value_to_code(&value, &bindings, checked_step.code_line.as_deref());
                CertificateLine {
                    value,
                    statement,
                    reason: checked_step.reason,
                }
            })
            .collect();
        Ok(CheckedCertificate {
            lines,
            consumed_proof_steps,
        })
    }

    /// Remove unneeded steps from this certificate.
    pub fn clean(
        self,
        checker: Checker,
        project: &Project,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<(Certificate, Vec<CertificateLine>), CodeGenError> {
        let mut good_cert = self;
        let mut keep_count = 0;

        loop {
            let Some(proof) = &good_cert.proof else {
                return Err(CodeGenError::NoProof);
            };

            if keep_count >= proof.len() {
                let steps = good_cert.check(checker, project, bindings, kernel_context)?;
                return Ok((good_cert, steps));
            }

            let mut test_cert = good_cert.clone();
            if let Some(test_proof) = &mut test_cert.proof {
                test_proof.remove(keep_count);
            }

            match test_cert.check(
                checker.clone(),
                project,
                bindings.clone(),
                kernel_context.clone(),
            ) {
                Ok(_) => {
                    good_cert = test_cert;
                }
                Err(_) => {
                    keep_count += 1;
                }
            }
        }
    }
}

/// A collection of certificates that can be saved to a file
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CertificateStore {
    pub certs: Vec<Certificate>,
}

impl CertificateStore {
    /// Load a certificate store from a file in JSONL format (one certificate per line)
    pub fn load(filename: &Path) -> Result<CertificateStore, Box<dyn Error>> {
        let file = File::open(filename)?;
        let reader = BufReader::new(file);
        let mut certs = Vec::new();

        for line in reader.lines() {
            let line = line?;
            if !line.trim().is_empty() {
                let cert: Certificate = serde_json::from_str(&line)?;
                certs.push(cert);
            }
        }

        Ok(CertificateStore { certs })
    }

    /// Save the certificate store to a file in JSONL format (one certificate per line)
    pub fn save(&self, filename: &Path) -> Result<(), Box<dyn Error>> {
        let file = File::create(filename)?;
        let mut writer = BufWriter::new(file);

        for cert in &self.certs {
            let json = serde_json::to_string(cert)?;
            writeln!(writer, "{}", json)?;
        }

        writer.flush()?;
        Ok(())
    }

    /// Loads a CertificateStore along with its descriptor.
    /// This expects certificate files to have .jsonl extensions.
    pub fn load_relative(
        root: &Path,
        full_filename: &Path,
    ) -> Option<(ModuleDescriptor, CertificateStore)> {
        let relative_filename = full_filename.strip_prefix(root).ok()?;
        let ext = relative_filename.extension()?;
        if ext != "jsonl" {
            return None;
        }
        let path_without_extension = relative_filename.with_extension("");
        let parts = path_without_extension
            .components()
            .map(|c| c.as_os_str().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        let descriptor = ModuleDescriptor::Name(parts);
        let cert_store = CertificateStore::load(full_filename).ok()?;
        Some((descriptor, cert_store))
    }

    /// Append all unused certificates from a worklist to this certificate store
    pub fn append(&mut self, worklist: &CertificateWorklist) {
        for cert in worklist.iter_unused() {
            self.certs.push(cert.clone());
        }
    }
}

/// A collection of certificates designed to be consumed, not necessarily in linear order.
pub struct CertificateWorklist {
    /// The underlying certificates. This doesn't change.
    store: CertificateStore,

    /// A mapping from goal name to the indices of all certificates with that goal name
    /// left in the store.
    indexes_for_goal: HashMap<String, Vec<usize>>,
}

impl CertificateWorklist {
    /// Create a new worklist from a certificate store
    pub fn new(store: CertificateStore) -> Self {
        let mut indexes_for_goal = HashMap::new();

        // Build the index mapping
        for (index, cert) in store.certs.iter().enumerate() {
            indexes_for_goal
                .entry(cert.goal.clone())
                .or_insert_with(Vec::new)
                .push(index);
        }

        CertificateWorklist {
            store,
            indexes_for_goal,
        }
    }

    /// Get the indices for all certificates with the given goal name
    pub fn get_indexes(&self, goal: &str) -> &Vec<usize> {
        static EMPTY: Vec<usize> = Vec::new();
        self.indexes_for_goal.get(goal).unwrap_or(&EMPTY)
    }

    /// Get a certificate by its index
    pub fn get_cert(&self, index: usize) -> Option<&Certificate> {
        self.store.certs.get(index)
    }

    /// Remove a specific index for a goal from the worklist
    pub fn remove(&mut self, goal: &str, index: usize) {
        if let Some(indexes) = self.indexes_for_goal.get_mut(goal) {
            indexes.retain(|&i| i != index);
            if indexes.is_empty() {
                self.indexes_for_goal.remove(goal);
            }
        }
    }

    /// Remove all certificates for a goal from the worklist.
    pub fn remove_goal(&mut self, goal: &str) {
        self.indexes_for_goal.remove(goal);
    }

    /// Get the number of unused certificates remaining in the worklist
    pub fn unused(&self) -> usize {
        self.indexes_for_goal.values().map(|v| v.len()).sum()
    }

    /// Iterator over unused certificates in the worklist
    pub fn iter_unused(&self) -> impl Iterator<Item = &Certificate> {
        self.indexes_for_goal
            .values()
            .flat_map(|indexes| indexes.iter())
            .filter_map(move |&index| self.store.certs.get(index))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::LoadState;
    use std::borrow::Cow;
    use tempfile::tempdir;

    #[test]
    fn test_save_load_cycle() {
        // Create a temporary directory for testing
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test_certs.jsonl");

        // Create some test certificates
        let cert1 = Certificate::new(
            "goal1".to_string(),
            vec!["step1".to_string(), "step2".to_string()],
        );
        let cert2 = Certificate::new(
            "goal2".to_string(),
            vec![
                "step3".to_string(),
                "step4".to_string(),
                "step5".to_string(),
            ],
        );
        let cert3 = Certificate::new(
            "goal3".to_string(),
            vec![], // Trivial proof with no steps
        );
        let cert4 = Certificate::placeholder(
            "goal4".to_string(), // No proof exists for this goal
        );

        // Create original certificate store
        let original = CertificateStore {
            certs: vec![cert1, cert2, cert3, cert4],
        };

        // Save to file
        original.save(&file_path).unwrap();

        // Load from file
        let loaded = CertificateStore::load(&file_path).unwrap();

        // Check that we got the same data back
        assert_eq!(original.certs.len(), loaded.certs.len());

        for (orig, load) in original.certs.iter().zip(loaded.certs.iter()) {
            assert_eq!(orig.goal, load.goal);
            assert_eq!(orig.proof, load.proof);
        }

        // Test has_proof() helper on loaded certificates
        assert!(loaded.certs[0].has_proof());
        assert!(loaded.certs[1].has_proof());
        assert!(loaded.certs[2].has_proof());
        assert!(!loaded.certs[3].has_proof());

        // Clean up is automatic when temp_dir goes out of scope
    }

    fn setup_claim_codec_env(code: &str) -> (Project, BindingMap, KernelContext) {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", code);

        let module_id = project
            .load_module_by_name("main")
            .expect("module should load");
        let (bindings, kernel_context) = {
            let env = match project.get_module_by_id(module_id) {
                LoadState::Ok(env) => env,
                LoadState::Error(e) => panic!("module loading error: {}", e),
                _ => panic!("unexpected module load state"),
            };
            let kernel_context = env
                .kernel_context
                .clone()
                .expect("environment should have a kernel context");
            (env.bindings.clone(), kernel_context)
        };

        (project, bindings, kernel_context)
    }

    fn setup_selected_goal_env(code: &str, line: u32) -> (Project, BindingMap, KernelContext) {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", code);

        let module_id = project
            .load_module_by_name("main")
            .expect("module should load");
        let (bindings, kernel_context) = {
            let env = match project.get_module_by_id(module_id) {
                LoadState::Ok(env) => env,
                LoadState::Error(e) => panic!("module loading error: {}", e),
                _ => panic!("unexpected module load state"),
            };
            let node_path = env
                .path_for_line(line - 1)
                .expect("selected line should resolve to a node path");
            let cursor = crate::elaborator::node::NodeCursor::from_path(env, &node_path);
            let goal_env = cursor.goal_env().expect("selected line should be a goal");
            let normalized_goal = cursor
                .normalized_goal()
                .expect("selected line should have a normalized goal");
            (
                goal_env.bindings.clone(),
                normalized_goal.kernel_context.clone(),
            )
        };

        (project, bindings, kernel_context)
    }

    #[test]
    fn test_claim_with_args_roundtrip_single_argument() {
        let code = r#"
            theorem goal {
                true = true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let clause = kernel.parse_clause("x0 = true", &["Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_true());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        assert_eq!(serialized, "function(x0: Bool) { x0 }(true)");

        let roundtrip = Certificate::deserialize_claim_with_args(
            &serialized,
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("deserialization should succeed");
        assert_eq!(roundtrip, claim);
    }

    #[test]
    fn test_claim_with_args_roundtrip_multiple_arguments() {
        let code = r#"
            theorem goal {
                true = false
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let clause = kernel.parse_clause("x0 = x1 or x0 = true", &["Bool", "Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_false());
        var_map.set(1, Term::new_true());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        let roundtrip = Certificate::deserialize_claim_with_args(
            &serialized,
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("deserialization should succeed");
        assert_eq!(roundtrip, claim);
    }

    #[test]
    fn test_claim_with_args_roundtrip_boolean_false_argument() {
        let code = r#"
            theorem goal {
                false = false
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let clause = kernel.parse_clause("x0", &["Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_false());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        let roundtrip = Certificate::deserialize_claim_with_args(
            &serialized,
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("deserialization should succeed");
        assert_eq!(roundtrip, claim);
    }

    #[test]
    fn test_claim_with_args_supports_type_parameter_locals() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let clause = kernel.parse_clause("x1 = x1", &["Type", "x0"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::bool_type());
        var_map.set(1, Term::new_true());
        let claim = Claim {
            clause: clause.clone(),
            var_map: var_map.clone(),
        };

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization with type locals should succeed");
        assert_eq!(serialized, "function[T0](x0: T0) { x0 = x0 }[Bool](true)");

        let parsed = Certificate::deserialize_claim_with_args(
            &serialized,
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("deserialization should succeed");
        assert_eq!(parsed, claim);
    }

    #[test]
    fn test_deserialize_claim_with_args_rejects_non_function_shape() {
        let code = r#"
            let bar: Bool -> Bool = axiom

            theorem goal {
                bar(true)
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let err = Certificate::deserialize_claim_with_args(
            "bar(true)",
            &project,
            &bindings,
            &kernel_context,
        )
        .expect_err("non-function claim should be rejected");
        let msg = err.to_string();
        assert!(msg.contains("function(...) { ... }(...)"));
    }

    #[test]
    fn test_parse_code_line_accepts_claim_with_args_shape() {
        let code = r#"
            theorem goal {
                false = false
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let mut expected_var_map = VariableMap::new();
        expected_var_map.set(0, Term::new_false());
        let expected = Claim {
            clause: kernel.parse_clause("x0", &["Bool"]),
            var_map: expected_var_map,
        };

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "function(x0: Bool) { x0 }(false)",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("claim-with-args parsing should succeed");

        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim, expected);
    }

    #[test]
    fn test_parse_code_line_preserves_higher_order_inequality_claim_with_args() {
        let code = r#"
            type Foo: axiom
            let a: Foo = axiom
            let f: Foo -> Foo = axiom
            let g: Foo -> (Foo -> Foo) = axiom

            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let line = "function(x0: Foo) { g(x0) != f }(a)";

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            line,
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("higher-order claim-with-args parsing should succeed");

        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim.var_map.len(), 1);

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should preserve higher-order inequality literal");
        assert_eq!(serialized, line);
    }

    #[test]
    fn test_deserialize_claim_with_args_preserves_single_not_if_literal() {
        let code = r#"
            type Nat: axiom
            let suc: Nat -> Nat = axiom
            let zero: Nat = axiom
            let a: Nat = axiom

            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let line = "function(x0: Nat) { not if a = zero { x0 = zero } else { suc(x0) = a } }(choose(k0: Nat) { a = suc(k0) })";

        let claim =
            Certificate::deserialize_claim_with_args(line, &project, &bindings, &kernel_context)
                .expect("deserialization should preserve a single not-if literal");

        assert_eq!(claim.clause.get_local_context().len(), 1);
        assert_eq!(claim.var_map.len(), 1);

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        assert_eq!(serialized, line);
    }

    #[test]
    fn test_parse_code_line_accepts_claim_with_type_args_shape() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let mut expected_var_map = VariableMap::new();
        expected_var_map.set(0, Term::bool_type());
        expected_var_map.set(1, Term::new_true());
        let expected = Claim {
            clause: kernel.parse_clause("x1 = x1", &["Type", "x0"]),
            var_map: expected_var_map,
        };

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "function[T0](x0: T0) { x0 = x0 }[Bool](true)",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("claim-with-type-args parsing should succeed");

        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim, expected);
    }

    #[test]
    fn test_parse_code_line_accepts_claim_with_type_args_only_shape() {
        let code = r#"
            let foo[T]: Bool = axiom

            theorem goal {
                foo[Bool]
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "function[T0] { foo[T0] }[Bool]",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("type-only claim-with-args parsing should succeed");

        let CertificateStep::Claim(claim) = step;
        assert!(claim.var_map.len() > 0);

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        let roundtrip = Certificate::deserialize_claim_with_args(
            &serialized,
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("deserialization should succeed");
        assert_eq!(roundtrip, claim);
    }

    #[test]
    fn test_serialize_claim_with_args_avoids_colliding_lambda_arg_names() {
        let code = r#"
            let x0: Bool = axiom
            let x1: Bool = axiom

            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;

        let clause = kernel.parse_clause("x0 or x1 or x2", &["Bool", "Bool", "Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_true());
        var_map.set(1, Term::new_false());
        var_map.set(2, Term::new_true());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        assert!(!serialized.contains("function(x0: Bool"));

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let parsed = Certificate::parse_code_line(
            &serialized,
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("serialized line should parse even when x0/x1 are already bound");

        let CertificateStep::Claim(roundtrip_claim) = parsed;
        assert_eq!(roundtrip_claim, claim);
    }

    #[test]
    fn test_parsed_claim_matches_definition_clause_under_iet() {
        use crate::kernel::checker::{Checker, StepReason};
        use crate::kernel::proof_step::Rule;

        let code = r#"
            type Nat: axiom
            let a: Nat = axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }

            theorem goal {
                true
            }
        "#;
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", code);

        let module_id = project
            .load_module_by_name("main")
            .expect("module should load");
        let env = match project.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("unexpected module load state"),
        };
        let cursor = env.get_node_by_goal_name("goal");
        let normalized_facts = cursor
            .visible_normalized_facts()
            .expect("normalized facts should be available");
        let bindings = cursor
            .goal_env()
            .expect("goal env should be available")
            .bindings
            .clone();
        let kernel_context = env
            .kernel_context
            .clone()
            .expect("environment should have a kernel context");

        let mut checker = Checker::new();
        for normalized in normalized_facts {
            for step in &normalized.steps {
                let Rule::Assumption(info) = &step.rule else {
                    panic!("expected normalized fact assumptions");
                };
                checker.insert_clause(
                    &step.clause,
                    StepReason::Assumption(info.source.clone()),
                    &normalized.kernel_context,
                );
            }
        }

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "function(x0: Nat) { f(x0) and (not g(x0) or not h(x0)) or fimp(x0) }(a)",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("claim-with-args parsing should succeed");

        let CertificateStep::Claim(claim) = step;
        let specialized = claim
            .var_map
            .specialize_clause(&claim.clause, kernel_context_cow.as_ref());
        assert!(
            checker
                .check_clause(&claim.clause, kernel_context_cow.as_ref())
                .or_else(|| checker.check_clause(&specialized, kernel_context_cow.as_ref()))
                .is_some(),
            "parsed claim should match one of the normalized definition clauses"
        );
    }

    #[test]
    fn test_parse_code_line_plain_claim_still_works() {
        let code = r#"
            let bar: Bool -> Bool = axiom

            theorem goal {
                bar(true)
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "bar(true)",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("plain claim parsing should succeed");

        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim.var_map.len(), 0);
    }

    #[test]
    fn test_parse_code_line_accepts_choose_claim_shape() {
        let code = r#"
            theorem goal {
                true = true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "choose(x0: Bool) { x0 } = true",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("choose claim parsing should succeed for certificate parsing");

        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim.var_map.len(), 0);
    }

    #[test]
    fn test_parse_code_line_keeps_closed_binder_claims_specialized() {
        let code = r#"
            let identity: Bool -> Bool = axiom

            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "identity(choose(k0: Bool) { forall(x0: Bool) { not identity(x0) = k0 } }) = choose(k1: Bool) { forall(x1: Bool) { not identity(x1) = k1 } }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("closed binder-heavy claim should parse");

        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim.var_map.len(), 0);
        assert!(claim.clause.get_local_context().is_empty());
    }

    #[test]
    fn test_checker_rejects_unjustified_choose_claim() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "choose(x0: Bool) { x0 } = true",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("choose claim parsing should succeed for certificate parsing");

        let mut checker = Checker::new();
        let err = checker
            .check_cert_steps(&[step], None, &kernel_context)
            .expect_err("arbitrary choose claim should not be accepted");
        assert!(
            err.to_string().contains("not obviously true"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn test_parse_code_line_rejects_trivial_witness_declaration() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let result = Certificate::parse_code_line(
            "let s0: Bool satisfy { true }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        );
        let err = match result {
            Err(err) => err,
            Ok(_) => panic!("trivial witness declaration should be disabled"),
        };

        assert!(
            err.to_string()
                .contains("certificate `let ... satisfy` steps are no longer supported"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn test_from_concrete_steps_uses_claim_with_args_serialization() {
        let code = r#"
            theorem goal {
                false = false
            }
        "#;
        let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause("x0", &["Bool"]);

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_false());
        let concrete_steps = vec![ConcreteStep {
            generic: generic.clone(),
            var_maps: vec![(var_map, generic.get_local_context().clone())],
        }];

        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "function(x0: Bool) { x0 }(false)");
    }

    #[test]
    fn test_from_concrete_steps_serializes_binder_claim_args() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause("x0", &["Bool"]);

        let mut var_map = VariableMap::new();
        var_map.set(
            0,
            Term::choose(
                Term::bool_type(),
                Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0))),
            ),
        );
        let concrete_steps = vec![ConcreteStep {
            generic: generic.clone(),
            var_maps: vec![(var_map, generic.get_local_context().clone())],
        }];

        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(
            proof[0],
            "function(x0: Bool) { x0 }(choose(k0: Bool) { k0 })"
        );
    }

    #[test]
    fn test_from_concrete_steps_serializes_plain_claim_when_no_local_context() {
        let code = r#"
            theorem goal {
                false
            }
        "#;
        let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause("false", &[]);

        let concrete_steps = vec![ConcreteStep {
            generic,
            var_maps: vec![(
                VariableMap::new(),
                crate::kernel::local_context::LocalContext::empty(),
            )],
        }];

        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "false");
    }

    #[test]
    fn test_from_concrete_steps_wraps_plain_claims_that_parse_as_statements() {
        use crate::kernel::atom::Atom;
        use crate::kernel::literal::Literal;

        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let generic = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::and(
                Term::forall(Term::bool_type(), Term::atom(Atom::BoundVariable(0))),
                Term::new_false(),
            ))],
            &LocalContext::empty(),
        );

        let concrete_steps = vec![ConcreteStep {
            generic,
            var_maps: vec![(
                VariableMap::new(),
                crate::kernel::local_context::LocalContext::empty(),
            )],
        }];

        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert!(
            proof[0].starts_with('('),
            "ambiguous binder-led claim should be parenthesized: {:?}",
            proof
        );

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            &proof[0],
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("parenthesized binder-led claim should parse");
        let CertificateStep::Claim(claim) = step;
        assert_eq!(claim.var_map.len(), 0);
    }

    #[test]
    fn test_from_concrete_steps_rejects_out_of_scope_claim_map() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause("x0 = x0", &["Bool"]);

        let mut bad_map = VariableMap::new();
        bad_map.set(0, Term::new_variable(1));
        let replacement_context =
            LocalContext::from_types(vec![Term::bool_type(), Term::type_sort()]);
        let concrete_steps = vec![ConcreteStep {
            generic,
            var_maps: vec![(bad_map, replacement_context)],
        }];

        let err = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect_err("out-of-scope var maps should fail certificate generation");
        assert!(
            err.to_string().contains("out-of-scope term"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn test_from_concrete_steps_infers_type_arg_from_value_mapping() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause("x1 = x1", &["Type", "x0"]);

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_variable(0));
        var_map.set(1, Term::new_true());
        let replacement_context =
            LocalContext::from_types(vec![Term::type_sort(), Term::bool_type()]);
        let concrete_steps = vec![ConcreteStep {
            generic: generic.clone(),
            var_maps: vec![(var_map, replacement_context)],
        }];

        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "function[T0](x0: T0) { x0 = x0 }[Bool](true)");
    }

    #[test]
    fn test_from_concrete_steps_falls_back_for_partial_logical_builtin_in_claim_map() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause("x1(x3, x2)", &["Type", "x0 -> x0 -> Bool", "x0", "x0"]);

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::bool_type());
        var_map.set(1, kernel.parse_term("eq(Bool)"));
        var_map.set(2, Term::new_false());
        var_map.set(3, Term::new_true());
        let concrete_steps = vec![ConcreteStep {
            generic,
            var_maps: vec![(var_map, LocalContext::empty())],
        }];

        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof, vec!["false = true"]);
    }

    #[test]
    fn test_claim_with_args_roundtrip_with_selected_goal_locals() {
        let code = "let f: Bool -> Bool = axiom\n\
let a: Bool = axiom\n\
\n\
theorem goal(k: Bool) {\n\
    k = k\n\
} by {\n\
    let (d: Bool) satisfy { d = d }\n\
    false\n\
}\n";
        let (project, bindings, kernel_context) = setup_selected_goal_env(code, 8);
        let line = "function(x0: Bool, x1: Bool) { f(x0) != f(x1) or (a = x1 and a = x0) }(d, k)";

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Owned(kernel_context);
        let step = Certificate::parse_code_line(
            line,
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("claim-with-args line should parse in a goal with local bindings");
        let CertificateStep::Claim(parsed) = step;
        assert_eq!(parsed.var_map.len(), 2);

        let serialized =
            Certificate::serialize_claim_with_args(&parsed, kernel_context_cow.as_ref(), &bindings)
                .expect("parsed claim should serialize again");
        assert_eq!(serialized, line);

        let mut checker = Checker::new();
        checker.insert_clause(
            &parsed.clause,
            StepReason::Testing,
            kernel_context_cow.as_ref(),
        );
        assert!(
            checker
                .check_clause(&parsed.clause, kernel_context_cow.as_ref())
                .is_some(),
            "generic claim should be accepted once inserted"
        );
    }
}
