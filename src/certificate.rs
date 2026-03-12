use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
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
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::elaborator::stack::Stack;
use crate::elaborator::to_term::elaborate_value_to_term;
use crate::elaborator::to_term::{elaborate_value_to_term_existing, TypeVarMap};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::{CertificateStep, Claim, SatisfyStep};
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::clause::Clause;
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::{Decomposition, Term};
use crate::kernel::term_normalization::normalize_term;
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::module::ModuleDescriptor;
use crate::project::Project;
use crate::prover::proof::ConcreteStep;
use crate::prover::synthetic::{
    witness_application, witness_signature, WitnessEntry, WitnessRegistry,
};
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

    /// Detect claim shapes that must stay as specialized expressions rather than generic claims.
    fn claim_requires_specialized_serialization(claim: &Claim) -> bool {
        let local_context = claim.clause().get_local_context();
        // `function(...) { ... }(...)` can only carry argument terms that are closed once the
        // generic clause's value locals are abstracted out.
        claim
            .var_map()
            .iter()
            .any(|(_, term)| Self::references_value_local(term.as_ref(), local_context))
    }

    /// Rebase a denormalized claim argument so it can stand alone outside the generic clause's
    /// local context. Type parameters stay in scope; value locals must disappear.
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
        Self::from_concrete_steps_with_witnesses(
            goal,
            concrete_steps,
            kernel_context,
            bindings,
            None,
        )
    }

    /// Serialize a proof while optionally emitting prover-generated named witnesses.
    pub fn from_concrete_steps_with_witnesses(
        goal: String,
        concrete_steps: &[ConcreteStep],
        kernel_context: &KernelContext,
        bindings: &BindingMap,
        witness_registry: Option<&WitnessRegistry>,
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
        let ordered_steps = if let Some(witness_registry) = witness_registry {
            Self::emit_named_witnesses(ordered_steps, witness_registry, &generation_kernel_context)?
        } else {
            ordered_steps
        };

        let mut answer = Vec::new();
        for step in &ordered_steps {
            answer.push(Self::serialize_certificate_step(
                step,
                &mut generator,
                &generation_kernel_context,
                bindings,
            )?);
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

    /// Replace eligible proof claims with named-witness steps and emit assumption-backed
    /// witnesses before their first use.
    fn emit_named_witnesses(
        ordered_steps: Vec<CertificateStep>,
        witness_registry: &WitnessRegistry,
        kernel_context: &KernelContext,
    ) -> Result<Vec<CertificateStep>, CodeGenError> {
        WitnessEmitter::new(ordered_steps, witness_registry, kernel_context)?.emit()
    }

    /// Convert prover witness metadata into a certificate `let ... satisfy` step.
    fn witness_entry_to_step(
        witness: &WitnessEntry,
        justification: Claim,
        kernel_context: &KernelContext,
    ) -> Result<SatisfyStep, CodeGenError> {
        let (type_params, arguments, _generic_type) = witness_signature(
            kernel_context,
            &witness.ambient_context,
            &witness.return_type,
        );
        let return_type = kernel_context.denormalize_type_with_context(
            witness.return_type.clone(),
            &witness.ambient_context,
            false,
        );

        let mut local_context = witness.ambient_context.clone();
        local_context.push_type(witness.return_type.clone());
        let opened_body = witness
            .body
            .substitute_bound(
                0,
                &Term::new_variable(witness.ambient_context.len() as AtomId),
            )
            .shift_bound(0, -1);
        let general_condition =
            kernel_context.denormalize_term_with_context(&opened_body, &local_context, false);

        let (condition, return_name) = if arguments.is_empty() {
            let specialized_body = witness
                .body
                .substitute_bound(
                    0,
                    &witness_application(witness.symbol, &witness.ambient_context),
                )
                .shift_bound(0, -1);
            (
                kernel_context.denormalize_term_with_context(
                    &specialized_body,
                    &witness.ambient_context,
                    false,
                ),
                None,
            )
        } else {
            (general_condition, Some("r".to_string()))
        };

        Ok(SatisfyStep {
            name: witness.name.to_string(),
            type_params,
            arguments,
            return_name,
            return_type,
            condition,
            justification,
            witness_clauses: vec![witness.specialized_clause.clone()],
        })
    }

    /// Normalize a certificate claim to the single clause used for witness matching.
    fn claim_clause(
        step: &CertificateStep,
        kernel_context: &KernelContext,
    ) -> Result<Option<Clause>, CodeGenError> {
        match step {
            CertificateStep::Claim(claim) => Ok(Some(
                claim
                    .normalized_specialized_clause(kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?,
            )),
            CertificateStep::Satisfy(_) => Ok(None),
        }
    }

    /// Collect named witness ids referenced by a displayed claim step.
    fn collect_claim_witness_ids(
        step: &CertificateStep,
        kernel_context: &KernelContext,
    ) -> Result<Vec<AtomId>, CodeGenError> {
        let mut ids = vec![];
        if let CertificateStep::Claim(claim) = step {
            let clause = claim
                .specialized_clause_for_display(kernel_context)
                .map_err(CodeGenError::GeneratedBadCode)?;
            for atom in clause.iter_atoms() {
                if let Atom::Symbol(Symbol::ScopedConstant(local_id)) = atom {
                    ids.push(*local_id);
                }
            }
        }
        ids.sort();
        ids.dedup();
        Ok(ids)
    }

    /// Convert one structured certificate step back into source code.
    fn serialize_certificate_step(
        step: &CertificateStep,
        generator: &mut CodeGenerator,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        let line = match step {
            CertificateStep::Claim(claim)
                if !claim.clause().get_local_context().is_empty()
                    && !Self::claim_requires_specialized_serialization(claim) =>
            {
                Self::serialize_claim_step(claim, kernel_context, bindings)?
            }
            _ => generator
                .certificate_step_to_code(step, kernel_context)
                .map_err(|err| {
                    CodeGenError::GeneratedBadCode(format!(
                        "{} [while serializing certificate step]",
                        err
                    ))
                })?,
        };

        match step {
            CertificateStep::Claim(_) => Self::ensure_claim_code_parses_as_claim(line),
            CertificateStep::Satisfy(_) => Ok(line),
        }
    }

    /// Serialize a claim in named form and fail if that form does not round-trip.
    fn serialize_claim_step(
        claim: &Claim,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        let specialized_clause = claim
            .normalized_specialized_clause(kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        Self::serialize_claim_with_names(claim, kernel_context, bindings).map_err(|err| {
            CodeGenError::GeneratedBadCode(format!(
                "{} [while serializing certificate claim step {}]",
                err, specialized_clause
            ))
        })
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
                let term = normalize_term(&term);
                Ok(CertificateStep::Claim(Self::claim_from_plain_term(
                    &term,
                    kernel_context.to_mut(),
                )?))
            };

        match statement.statement {
            StatementInfo::VariableSatisfy(vss) => {
                Self::parse_variable_satisfy_step(code, project, vss, bindings, kernel_context)
            }
            StatementInfo::FunctionSatisfy(fss) => {
                Self::parse_function_satisfy_step(code, project, fss, bindings, kernel_context)
            }
            StatementInfo::Claim(claim) => claim_step_from_expr(&claim.claim),
            _ => Err(CodeGenError::GeneratedBadCode(format!(
                "Expected a claim or let...satisfy statement, got: {}",
                code
            ))),
        }
    }

    /// Build the elaboration-time type-variable environment for certificate-local type parameters.
    fn type_var_map_for_params(
        kernel_context: &mut KernelContext,
        type_params: &[TypeParam],
    ) -> Option<HashMap<String, (AtomId, Term)>> {
        if type_params.is_empty() {
            return None;
        }

        let mut map = HashMap::new();
        for (i, param) in type_params.iter().enumerate() {
            let kind = if let Some(typeclass) = &param.typeclass {
                let tc_id = kernel_context.type_store.add_typeclass(typeclass);
                Term::typeclass(tc_id)
            } else {
                Term::type_sort()
            };
            map.insert(param.name.clone(), (i as AtomId, kind));
        }
        Some(map)
    }

    /// Lower a parsed certificate proposition to the single implicit claim used by `satisfy`.
    fn claim_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Claim, CodeGenError> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        let term = elaborate_value_to_term_existing(kernel_context, value, type_var_map.as_ref())?;
        let term = normalize_term(&term);
        Self::claim_from_plain_term(&term, kernel_context)
    }

    /// Lower a parsed certificate proposition to the checker clauses introduced by `satisfy`.
    fn checker_clauses_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Vec<Clause>, CodeGenError> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        let term = elaborate_value_to_term_existing(kernel_context, value, type_var_map.as_ref())?;
        let term = normalize_term(&term);
        kernel_context
            .term_to_checker_clauses(&term, type_var_map)
            .map_err(CodeGenError::GeneratedBadCode)
    }

    /// Register a local constant introduced by a certificate `let ... satisfy` declaration.
    fn register_certificate_local_constant(
        bindings: &mut BindingMap,
        kernel_context: &mut KernelContext,
        name: &str,
        type_params: &[TypeParam],
        constant_type: &AcornType,
        definition_string: &str,
    ) -> Result<ConstantName, CodeGenError> {
        let defined_name = DefinedName::unqualified(bindings.module_id(), name);
        if bindings.constant_name_in_use(&defined_name) {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "certificate name '{}' is already in use",
                name
            )));
        }

        bindings.add_defined_name(
            &defined_name,
            type_params.to_vec(),
            constant_type.clone(),
            None,
            None,
            vec![],
            None,
            Some(definition_string.to_string()),
        );

        let constant_name = ConstantName::unqualified(bindings.module_id(), name);
        kernel_context.type_store.add_type(constant_type);
        let type_args: Vec<AcornType> = type_params
            .iter()
            .map(|param| AcornType::Variable(param.clone()))
            .collect();
        let mut symbol_type = if type_params.is_empty() {
            kernel_context.type_store.to_type_term(constant_type)
        } else {
            kernel_context
                .type_store
                .to_polymorphic_type_term(constant_type, &type_args)
        };
        for param in type_params.iter().rev() {
            let input_type = if let Some(typeclass) = &param.typeclass {
                let tc_id = kernel_context.type_store.add_typeclass(typeclass);
                Term::typeclass(tc_id)
            } else {
                Term::type_sort()
            };
            symbol_type = Term::pi(input_type, symbol_type);
        }
        kernel_context.symbol_table.add_constant(
            constant_name.clone(),
            NewConstantType::Local,
            symbol_type,
        );
        if !type_params.is_empty() {
            kernel_context.symbol_table.set_polymorphic_info(
                constant_name.clone(),
                constant_type.clone(),
                type_params.iter().map(|param| param.name.clone()).collect(),
            );
        }
        Ok(constant_name)
    }

    /// Parse a certificate variable witness declaration into checker-ready clauses.
    fn parse_variable_satisfy_step(
        code: &str,
        project: &Project,
        vss: crate::syntax::statement::VariableSatisfyStatement,
        bindings: &mut Cow<BindingMap>,
        kernel_context: &mut Cow<KernelContext>,
    ) -> Result<CertificateStep, CodeGenError> {
        if vss.declarations.len() != 1 {
            return Err(CodeGenError::GeneratedBadCode(
                "certificate let-satisfy only supports a single declaration".to_string(),
            ));
        }

        let bindings = bindings.to_mut();
        let kernel_context = kernel_context.to_mut();
        let mut evaluator = Evaluator::new_with_allow_choose(project, bindings, None, true);
        let type_params = evaluator.evaluate_type_params(&vss.type_params)?;
        for param in &type_params {
            bindings.add_arbitrary_type(param.clone());
            kernel_context.register_arbitrary_type(param);
        }

        let mut stack = Stack::new();
        let mut general_evaluator = Evaluator::new_with_allow_choose(project, bindings, None, true);
        let (quant_names, quant_types) =
            general_evaluator.bind_args_may_shadow(&mut stack, &vss.declarations, None)?;
        let Some(return_type) = quant_types.first().cloned() else {
            return Err(CodeGenError::GeneratedBadCode(
                "certificate let-satisfy is missing a declaration".to_string(),
            ));
        };
        let general_condition = general_evaluator.evaluate_value_with_stack(
            &mut stack,
            &vss.condition,
            Some(&AcornType::Bool),
        )?;
        let name = quant_names
            .first()
            .cloned()
            .expect("single declaration has a single name");
        Self::register_certificate_local_constant(
            bindings,
            kernel_context,
            &name,
            &type_params,
            &return_type,
            code,
        )?;

        let mut specific_evaluator =
            Evaluator::new_with_allow_choose(project, bindings, None, true);
        let specific_condition =
            specific_evaluator.evaluate_value(&vss.condition, Some(&AcornType::Bool))?;

        let general_claim = AcornValue::Exists(quant_types, Box::new(general_condition));
        let justification =
            Self::claim_for_proposition(kernel_context, &general_claim, &type_params)?;
        let witness_clauses = Self::checker_clauses_for_proposition(
            kernel_context,
            &specific_condition,
            &type_params,
        )?;

        for param in type_params.iter().rev() {
            bindings.remove_type(&param.name);
        }

        Ok(CertificateStep::Satisfy(SatisfyStep {
            name,
            type_params,
            arguments: vec![],
            return_name: None,
            return_type,
            condition: specific_condition,
            justification,
            witness_clauses,
        }))
    }

    /// Parse a certificate function witness declaration into checker-ready clauses.
    fn parse_function_satisfy_step(
        code: &str,
        project: &Project,
        fss: crate::syntax::statement::FunctionSatisfyStatement,
        bindings: &mut Cow<BindingMap>,
        kernel_context: &mut Cow<KernelContext>,
    ) -> Result<CertificateStep, CodeGenError> {
        if fss.body.is_some() {
            return Err(CodeGenError::GeneratedBadCode(
                "certificate function-satisfy declarations cannot include a proof block"
                    .to_string(),
            ));
        }

        let bindings = bindings.to_mut();
        let kernel_context = kernel_context.to_mut();
        let (type_params, mut arg_names, mut arg_types, condition, _condition_type) = bindings
            .evaluate_scoped_value(
                &fss.type_params,
                &fss.declarations,
                None,
                &fss.condition,
                None,
                None,
                None,
                None,
                project,
                None,
            )?;
        let condition = condition.ok_or_else(|| {
            CodeGenError::GeneratedBadCode("missing function-satisfy condition".to_string())
        })?;
        let Some(return_name) = arg_names.pop() else {
            return Err(CodeGenError::GeneratedBadCode(
                "function-satisfy declaration is missing a return value".to_string(),
            ));
        };
        let Some(return_type) = arg_types.pop() else {
            return Err(CodeGenError::GeneratedBadCode(
                "function-satisfy declaration is missing a return type".to_string(),
            ));
        };
        let function_type = AcornType::functional(arg_types.clone(), return_type.clone());
        let name = fss.name_token.text().to_string();
        let constant_name = Self::register_certificate_local_constant(
            bindings,
            kernel_context,
            &name,
            &type_params,
            &function_type,
            code,
        )?;
        let function_constant = AcornValue::constant(
            constant_name,
            vec![],
            function_type.clone(),
            function_type,
            type_params.iter().map(|param| param.name.clone()).collect(),
        );
        let function_term = AcornValue::apply(
            function_constant,
            arg_types
                .iter()
                .enumerate()
                .map(|(i, arg_type)| AcornValue::Variable(i as AtomId, arg_type.clone()))
                .collect(),
        );
        let num_args = arg_types.len() as AtomId;
        let specialized_condition =
            condition
                .clone()
                .bind_values(num_args, num_args, &[function_term]);
        let general_claim = AcornValue::ForAll(
            arg_types.clone(),
            Box::new(AcornValue::Exists(
                vec![return_type.clone()],
                Box::new(condition.clone()),
            )),
        );
        let specialized_claim =
            AcornValue::ForAll(arg_types.clone(), Box::new(specialized_condition.clone()));
        let justification =
            Self::claim_for_proposition(kernel_context, &general_claim, &type_params)?;
        let witness_clauses = Self::checker_clauses_for_proposition(
            kernel_context,
            &specialized_claim,
            &type_params,
        )?;

        Ok(CertificateStep::Satisfy(SatisfyStep {
            name,
            type_params,
            arguments: arg_names.into_iter().zip(arg_types).collect(),
            return_name: Some(return_name),
            return_type,
            condition,
            justification,
            witness_clauses,
        }))
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
        let local_context = claim.clause().get_local_context();
        let mut expected_var_map = VariableMap::new();

        for var_id in 0..local_context.len() {
            let var_id = var_id as AtomId;
            if let Some(term) = claim.var_map().get_mapping(var_id) {
                expected_var_map.set(var_id, apply_to_term(term.as_ref(), type_var_map));
                continue;
            }
            if let Some(type_term) = type_var_map.get_mapping(var_id) {
                expected_var_map.set(var_id, type_term.clone());
            }
        }

        Claim::new(claim.clause().clone(), expected_var_map)
            .expect("roundtrip claim should normalize")
    }

    fn roundtrip_clause_formula(clause: &Clause, kernel_context: &KernelContext) -> Option<Term> {
        let literal = clause.literals.first()?;
        if clause.literals.len() != 1 {
            return None;
        }
        if literal.is_signed_term() {
            return Some(if literal.positive {
                literal.left.clone()
            } else {
                Term::not(literal.left.clone())
            });
        }

        let equality = Term::eq(
            literal
                .left
                .get_type_with_context(clause.get_local_context(), kernel_context),
            literal.left.clone(),
            literal.right.clone(),
        );
        Some(if literal.positive {
            equality
        } else {
            Term::not(equality)
        })
    }

    /// Treat single-literal equality clauses and their inline `eq(...)` forms as equivalent.
    fn clauses_roundtrip_equivalent(
        expected: &Clause,
        actual: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        if expected == actual {
            return true;
        }
        if expected.get_local_context() != actual.get_local_context() {
            return false;
        }
        Self::roundtrip_clause_formula(expected, kernel_context)
            == Self::roundtrip_clause_formula(actual, kernel_context)
    }

    fn claims_roundtrip_equivalent(
        expected: &Claim,
        actual: &Claim,
        kernel_context: &KernelContext,
    ) -> bool {
        if expected == actual {
            return true;
        }
        if expected.clause().get_local_context() != actual.clause().get_local_context() {
            return false;
        }
        // Partial logical builtins and typeclass members can canonicalize to a different generic
        // clause shape when parsed back, so the real invariant is the immediate specialized
        // clause before checker simplification.
        match (
            expected.specialized_clause_for_display(kernel_context).ok(),
            actual.specialized_clause_for_display(kernel_context).ok(),
        ) {
            (Some(expected_clause), Some(actual_clause)) => {
                if Self::clauses_roundtrip_equivalent(
                    &expected_clause,
                    &actual_clause,
                    kernel_context,
                ) {
                    return true;
                }
                match (
                    expected.normalized_specialized_clause(kernel_context).ok(),
                    actual.normalized_specialized_clause(kernel_context).ok(),
                ) {
                    (Some(expected_clause), Some(actual_clause)) => {
                        Self::clauses_roundtrip_equivalent(
                            &expected_clause,
                            &actual_clause,
                            kernel_context,
                        )
                    }
                    (None, None) => true,
                    _ => false,
                }
            }
            (None, None) => true,
            _ => false,
        }
    }

    fn claim_from_clause(clause: Clause) -> Result<Claim, CodeGenError> {
        Claim::new(clause, VariableMap::new()).map_err(CodeGenError::GeneratedBadCode)
    }

    fn claim_with_var_map(clause: Clause, var_map: VariableMap) -> Result<Claim, CodeGenError> {
        Claim::new(clause, var_map).map_err(CodeGenError::GeneratedBadCode)
    }

    fn claim_with_args_from_clause(
        clause: Clause,
        type_args: &[AcornType],
        args: &[AcornValue],
        kernel_context: &mut KernelContext,
    ) -> Result<Claim, CodeGenError> {
        let var_map = Self::build_claim_var_map(type_args, args, kernel_context)?;
        Self::claim_with_var_map(clause, var_map)
    }

    fn claim_from_plain_term(
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
            // A claim line may intentionally keep a boolean connective inline
            // as a single signed literal term (for example, `a and b`) rather
            // than expanding it into multiple CNF clauses.
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

    fn serialize_claim_with_names(
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
        let generic_value = kernel_context.denormalize(claim.clause(), None, None, false);
        let generic_code = generator.value_to_code(&generic_value)?;
        // Claim arguments are serialized outside the clause's local scope, so only the leading
        // type parameters stay available while we denormalize them.
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
            if claim.var_map().get_mapping(var_id as AtomId).is_none() {
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

            let arg_term = claim.var_map().get_mapping(var_id as AtomId);

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
            let (arg_context, scope_len) = if substituted_arg_term.max_variable().is_none() {
                (LocalContext::empty(), 0)
            } else {
                (
                    standalone_arg_context.clone(),
                    standalone_arg_context.len() as AtomId,
                )
            };
            let arg_value = kernel_context.denormalize_term_with_context(
                &substituted_arg_term,
                &arg_context,
                true,
            );
            let arg_value =
                Self::rebase_value_to_standalone(&arg_value, scope_len).map_err(|err| {
                    CodeGenError::GeneratedBadCode(format!(
                        "{} [claim arg term: {}; denormalized: {}]",
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
        let actual_roundtrip = Self::try_deserialize_claim_with_args_value(
            roundtrip_value,
            bindings,
            &mut roundtrip_kernel_context,
        )?;
        if !actual_roundtrip.as_ref().is_some_and(|actual| {
            Self::claims_roundtrip_equivalent(&expected_roundtrip_claim, actual, kernel_context)
        }) {
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
        let generic_term = normalize_term(&generic_term);
        Self::try_claim_with_args_from_generic_term(
            &generic_term,
            &type_param_kinds,
            type_args.as_slice(),
            args.as_slice(),
            kernel_context,
            &mut kernel_context_clone,
            type_var_map,
        )
    }

    fn try_claim_with_args_from_generic_term(
        generic_term: &Term,
        type_param_kinds: &[Term],
        type_args: &[AcornType],
        args: &[AcornValue],
        kernel_context: &mut KernelContext,
        clausify_kernel_context: &mut KernelContext,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Option<Claim>, CodeGenError> {
        if Self::term_has_inline_clause_shape(generic_term, true) {
            let clause = Self::try_deserialize_inline_clause(generic_term, type_param_kinds)
                .expect("inline clause shape should deserialize");
            return Self::claim_with_args_from_clause(clause, type_args, args, kernel_context)
                .map(Some);
        }
        if Self::should_preserve_single_literal_claim(generic_term) {
            if let Some(clause) =
                Self::try_deserialize_single_literal_clause(generic_term, type_param_kinds)
            {
                return Self::claim_with_args_from_clause(clause, type_args, args, kernel_context)
                    .map(Some);
            }
        }

        let clauses =
            clausify_kernel_context.term_to_checker_clauses(generic_term, type_var_map)?;
        if clauses.len() != 1 {
            if let Some(clause) =
                Self::try_deserialize_single_literal_clause(generic_term, type_param_kinds)
            {
                return Self::claim_with_args_from_clause(clause, type_args, args, kernel_context)
                    .map(Some);
            }
            if let Some(clause) =
                Self::try_deserialize_single_formula_clause(generic_term, type_param_kinds)
            {
                return Self::claim_with_args_from_clause(clause, type_args, args, kernel_context)
                    .map(Some);
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
        Self::claim_with_args_from_clause(clause, type_args, args, kernel_context).map(Some)
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
                let term = normalize_term(&term);
                kernel_context.term_to_claim_arg(&term)?
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
            || args[0]
                .iter_atoms()
                .any(|atom| matches!(atom, Atom::FreeVariable(_) | Atom::BoundVariable(_)))
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
                let statement = if checked_step.prefer_code_line {
                    checked_step
                        .code_line
                        .clone()
                        .unwrap_or_else(|| value_to_code(&value, &bindings, None))
                } else {
                    value_to_code(&value, &bindings, checked_step.code_line.as_deref())
                };
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

/// Emits named witness steps directly in the certificate stream.
struct WitnessEmitter<'a> {
    ordered_steps: Vec<CertificateStep>,
    claim_clauses: Vec<Option<Clause>>,
    referenced_ids: Vec<Vec<AtomId>>,
    witness_registry: &'a WitnessRegistry,
    witness_steps: HashMap<AtomId, SatisfyStep>,
    claim_replacements: HashMap<usize, AtomId>,
    replacement_indices: HashMap<AtomId, usize>,
    declared: HashSet<AtomId>,
    buffered: Vec<usize>,
    emitted: Vec<bool>,
    in_progress: HashSet<AtomId>,
    output: Vec<CertificateStep>,
}

impl<'a> WitnessEmitter<'a> {
    /// Precompute the witness steps and the claim positions they should replace.
    fn new(
        ordered_steps: Vec<CertificateStep>,
        witness_registry: &'a WitnessRegistry,
        kernel_context: &KernelContext,
    ) -> Result<Self, CodeGenError> {
        let num_steps = ordered_steps.len();
        let claim_clauses: Vec<Option<Clause>> = ordered_steps
            .iter()
            .map(|step| Certificate::claim_clause(step, kernel_context))
            .collect::<Result<_, _>>()?;
        let referenced_ids: Vec<Vec<AtomId>> = ordered_steps
            .iter()
            .map(|step| Certificate::collect_claim_witness_ids(step, kernel_context))
            .collect::<Result<_, _>>()?;

        let mut emitter = Self {
            ordered_steps,
            claim_clauses,
            referenced_ids,
            witness_registry,
            witness_steps: HashMap::new(),
            claim_replacements: HashMap::new(),
            replacement_indices: HashMap::new(),
            declared: HashSet::new(),
            buffered: Vec::new(),
            emitted: vec![false; num_steps],
            in_progress: HashSet::new(),
            output: Vec::new(),
        };
        for ids in emitter.referenced_ids.clone() {
            for local_id in ids {
                emitter.prepare_witness(local_id, kernel_context)?;
            }
        }
        Ok(emitter)
    }

    /// Emit the final certificate steps with named witnesses substituted in.
    fn emit(mut self) -> Result<Vec<CertificateStep>, CodeGenError> {
        for index in 0..self.ordered_steps.len() {
            self.schedule_step(index, index)?;
            self.flush_buffered(index)?;
        }
        Ok(self.output)
    }

    /// Delay any step whose first witness use depends on a later replacement claim.
    fn step_needs_future_witness(&self, index: usize, current_index: usize) -> bool {
        self.referenced_ids[index].iter().any(|local_id| {
            !self.declared.contains(local_id)
                && self
                    .replacement_indices
                    .get(local_id)
                    .is_some_and(|replacement_index| *replacement_index > current_index)
        })
    }

    /// Schedule one proof step, buffering it if a later claim still needs to introduce a witness.
    fn schedule_step(&mut self, index: usize, current_index: usize) -> Result<(), CodeGenError> {
        if self.emitted[index] {
            return Ok(());
        }

        if let Some(local_id) = self.claim_replacements.get(&index).copied() {
            self.emit_witness(local_id)?;
            self.emitted[index] = true;
            return Ok(());
        }

        if self.step_needs_future_witness(index, current_index) {
            self.buffered.push(index);
            return Ok(());
        }

        self.emit_ready_step(index, current_index)
    }

    /// Emit a step once every witness it references can already be declared.
    fn emit_ready_step(&mut self, index: usize, current_index: usize) -> Result<(), CodeGenError> {
        if self.emitted[index] {
            return Ok(());
        }

        let step = self.ordered_steps[index].clone();
        if self.claim_clauses[index].is_none() {
            self.output.push(step);
            self.emitted[index] = true;
            return Ok(());
        }

        for local_id in self.referenced_ids[index].clone() {
            self.ensure_declared(local_id, current_index)?;
        }
        self.output.push(step);
        self.emitted[index] = true;
        Ok(())
    }

    /// Revisit buffered steps after later justification claims have been emitted.
    fn flush_buffered(&mut self, current_index: usize) -> Result<(), CodeGenError> {
        let mut next_buffered = Vec::new();
        let mut made_progress = true;

        while made_progress {
            made_progress = false;
            let pending = if next_buffered.is_empty() {
                std::mem::take(&mut self.buffered)
            } else {
                std::mem::take(&mut next_buffered)
            };

            for index in pending {
                if self.emitted[index] {
                    continue;
                }
                if self.step_needs_future_witness(index, current_index) {
                    next_buffered.push(index);
                    continue;
                }
                self.emit_ready_step(index, current_index)?;
                made_progress = true;
            }
        }

        self.buffered = next_buffered;
        Ok(())
    }

    /// Prepare one witness step and remember which claim it should replace, if any.
    fn prepare_witness(
        &mut self,
        local_id: AtomId,
        kernel_context: &KernelContext,
    ) -> Result<(), CodeGenError> {
        if self.witness_steps.contains_key(&local_id) {
            return Ok(());
        }
        let Some(witness) = self.witness_registry.get(local_id) else {
            return Ok(());
        };

        for dependency_id in witness.referenced_scoped_constants() {
            self.prepare_witness(dependency_id, kernel_context)?;
        }

        let general_clause = witness.general_clause.clone();
        let matching_claims: Vec<usize> = self
            .claim_clauses
            .iter()
            .enumerate()
            .filter_map(|(index, clause)| {
                (clause.as_ref() == Some(&general_clause)).then_some(index)
            })
            .collect();
        if matching_claims.len() > 1 {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "named witness '{}' matches multiple certificate claims",
                witness.name
            )));
        }
        let justification = if let Some(index) = matching_claims.first().copied() {
            let CertificateStep::Claim(claim) = &self.ordered_steps[index] else {
                panic!("claim_clauses only records claim steps");
            };
            claim.clone()
        } else {
            Certificate::claim_from_clause(general_clause.clone())?
        };
        if let Some(index) = matching_claims.first().copied() {
            if let Some(existing) = self.claim_replacements.insert(index, local_id) {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "certificate claim {} would introduce both witness x{} and witness x{}",
                    index + 1,
                    existing,
                    local_id
                )));
            }
            self.replacement_indices.insert(local_id, index);
        }
        let step = Certificate::witness_entry_to_step(witness, justification, kernel_context)?;
        self.witness_steps.insert(local_id, step);
        Ok(())
    }

    /// Make sure a witness has been emitted before a claim that references it.
    fn ensure_declared(
        &mut self,
        local_id: AtomId,
        current_index: usize,
    ) -> Result<(), CodeGenError> {
        if self.declared.contains(&local_id) || !self.witness_steps.contains_key(&local_id) {
            return Ok(());
        }

        if let Some(index) = self.replacement_indices.get(&local_id).copied() {
            if index > current_index {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "named witness x{} was used before its justification claim",
                    local_id
                )));
            }
            return self.schedule_step(index, current_index);
        }

        self.emit_witness(local_id)
    }

    /// Emit the named-witness step itself after recursively materializing dependencies.
    fn emit_witness(&mut self, local_id: AtomId) -> Result<(), CodeGenError> {
        if self.declared.contains(&local_id) || !self.witness_steps.contains_key(&local_id) {
            return Ok(());
        }

        let Some(witness) = self.witness_registry.get(local_id) else {
            return Ok(());
        };
        if !self.in_progress.insert(local_id) {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "cyclic named witness dependency involving '{}'",
                witness.name
            )));
        }

        for dependency_id in witness.referenced_scoped_constants() {
            self.ensure_declared(dependency_id, usize::MAX)?;
        }

        let step = self
            .witness_steps
            .get(&local_id)
            .expect("prepared witness step should exist")
            .clone();
        self.output.push(CertificateStep::Satisfy(step));
        self.declared.insert(local_id);
        self.in_progress.remove(&local_id);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::LoadState;
    use crate::processor::Processor;
    use std::borrow::Cow;
    use tempfile::tempdir;

    /// Unwrap a parsed test step that is expected to be a claim.
    fn expect_claim(step: CertificateStep) -> Claim {
        let CertificateStep::Claim(claim) = step else {
            panic!("expected certificate claim step");
        };
        claim
    }

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
                .lowered_goal()
                .expect("selected line should have a lowered goal");
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
        let claim = Claim::new(clause, var_map).expect("claim should normalize");

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
        let claim = Claim::new(clause, var_map).expect("claim should normalize");

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
        let claim = Claim::new(clause, var_map).expect("claim should normalize");

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
        let claim = Claim::new(clause.clone(), var_map.clone()).expect("claim should normalize");

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
        let expected = Claim::new(kernel.parse_clause("x0", &["Bool"]), expected_var_map)
            .expect("claim should normalize");

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "function(x0: Bool) { x0 }(false)",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("claim-with-args parsing should succeed");

        let claim = expect_claim(step);
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

        let claim = expect_claim(step);
        assert_eq!(claim.var_map().len(), 1);

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

        assert_eq!(claim.clause().get_local_context().len(), 1);
        assert_eq!(claim.var_map().len(), 1);

        let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
            .expect("serialization should succeed");
        assert!(serialized.contains("not if"));
        let reparsed = Certificate::deserialize_claim_with_args(
            &serialized,
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("serialized claim should deserialize again");
        assert_eq!(reparsed, claim);
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
        let expected = Claim::new(
            kernel.parse_clause("x1 = x1", &["Type", "x0"]),
            expected_var_map,
        )
        .expect("claim should normalize");

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "function[T0](x0: T0) { x0 = x0 }[Bool](true)",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("claim-with-type-args parsing should succeed");

        let claim = expect_claim(step);
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

        let claim = expect_claim(step);
        assert!(claim.var_map().len() > 0);

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
        let claim = Claim::new(clause, var_map).expect("claim should normalize");

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

        let roundtrip_claim = expect_claim(parsed);
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
            .visible_lowered_facts()
            .expect("lowered facts should be available");
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
                    panic!("expected lowered fact assumptions");
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

        let claim = expect_claim(step);
        let specialized = claim
            .normalized_specialized_clause(kernel_context_cow.as_ref())
            .expect("claim specialization should succeed");
        assert!(
            checker
                .check_clause(claim.clause(), kernel_context_cow.as_ref())
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

        let claim = expect_claim(step);
        assert_eq!(claim.var_map().len(), 0);
    }

    #[test]
    fn test_parse_code_line_canonicalizes_plain_claim_equality() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut lhs_bindings = Cow::Borrowed(&bindings);
        let mut lhs_kernel_context = Cow::Borrowed(&kernel_context);
        let lhs = Certificate::parse_code_line(
            "true = false",
            &project,
            &mut lhs_bindings,
            &mut lhs_kernel_context,
        )
        .expect("left equality should parse");

        let mut rhs_bindings = Cow::Borrowed(&bindings);
        let mut rhs_kernel_context = Cow::Borrowed(&kernel_context);
        let rhs = Certificate::parse_code_line(
            "false = true",
            &project,
            &mut rhs_bindings,
            &mut rhs_kernel_context,
        )
        .expect("right equality should parse");

        let lhs_claim = expect_claim(lhs);
        let rhs_claim = expect_claim(rhs);
        assert_eq!(lhs_claim, rhs_claim);
    }

    #[test]
    fn test_deserialize_claim_with_args_normalizes_value_argument_term() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let claim = Certificate::deserialize_claim_with_args(
            "function(x0: Bool) { x0 }(not not false)",
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("claim-with-args deserialization should succeed");

        assert_eq!(claim.var_map().get_mapping(0), Some(&Term::new_false()));
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

        let claim = expect_claim(step);
        assert_eq!(claim.var_map().len(), 0);
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

        let claim = expect_claim(step);
        assert_eq!(claim.var_map().len(), 0);
        assert!(claim.clause().get_local_context().is_empty());
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
    fn test_check_cert_accepts_lambda_valued_claim_argument() {
        use crate::prover::{Outcome, ProverMode};

        let code = r#"
            type Nat: axiom
            let rel: (Nat, Nat) -> Bool = axiom

            define is_transitive[T](f: (T, T) -> Bool) -> Bool {
                forall(x: T, y: T, z: T) {
                    f(x, y) and f(y, z) implies f(x, z)
                }
            }

            axiom rel_trans(x: Nat, y: Nat, z: Nat) {
                rel(x, y) and rel(y, z) implies rel(x, z)
            }

            theorem goal {
                is_transitive(function(a: Nat, b: Nat) { rel(a, b) })
            } by {
                forall(x: Nat, y: Nat, z: Nat) {
                    rel_trans(x, y, z)
                }
            }
        "#;

        let (mut processor, bindings, normalized_goal) = Processor::test_goal(code);
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", code);

        let outcome = processor.search(
            ProverMode::Interactive {
                timeout_secs: 5.0,
                activation_limit: 100_000,
            },
            &normalized_goal.kernel_context,
        );
        assert_eq!(outcome, Outcome::Success);

        let cert = processor
            .prover()
            .make_cert(&bindings, &normalized_goal.kernel_context, false)
            .expect("lambda-valued cert should be generated");
        let proof = cert.proof.as_ref().expect("proof should exist");
        assert!(
            proof.iter().any(|line| {
                line.contains("is_transitive") && line.contains("}[Nat](function(")
            }),
            "expected a proof step to preserve the lambda-valued claim argument: {proof:?}"
        );

        processor
            .check_cert(
                &cert,
                Some(&normalized_goal),
                &normalized_goal.kernel_context,
                &project,
                &bindings,
            )
            .expect("lambda-valued claim argument should verify");
    }

    #[test]
    fn test_parse_code_line_accepts_variable_witness_declaration() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let step = Certificate::parse_code_line(
            "let w0: Bool satisfy { true }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("trivial witness declaration should parse");

        let CertificateStep::Satisfy(step) = step else {
            panic!("expected satisfy step");
        };
        assert_eq!(step.name, "w0");
        assert_eq!(step.arguments.len(), 0);
        assert!(step.return_name.is_none());
        let justification_clause = step
            .justification
            .normalized_specialized_clause(&kernel_context)
            .expect("witness justification should normalize");
        assert_eq!(justification_clause.literals.len(), 1);
        assert!(justification_clause.literals[0]
            .left
            .as_ref()
            .split_exists()
            .is_some());
        assert!(step.witness_clauses.is_empty());
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
        let claim = expect_claim(step);
        assert_eq!(claim.var_map().len(), 0);
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
    fn test_from_concrete_steps_serializes_partial_logical_builtin_in_claim_map() {
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
        assert_eq!(
            proof,
            vec![
                "function[T0](x0: (T0, T0) -> Bool, x1: T0, x2: T0) { x0(x1, x2) }[Bool](function(x3: Bool, x4: Bool) { x3 = x4 }, false, true)"
            ]
        );
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
        let parsed = expect_claim(step);
        assert_eq!(parsed.var_map().len(), 2);

        let serialized =
            Certificate::serialize_claim_with_args(&parsed, kernel_context_cow.as_ref(), &bindings)
                .expect("parsed claim should serialize again");
        let reparsed = Certificate::parse_code_line(
            &serialized,
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("serialized claim should parse again");
        let reparsed = expect_claim(reparsed);
        assert_eq!(reparsed, parsed);

        let mut checker = Checker::new();
        checker.insert_clause(
            parsed.clause(),
            StepReason::Testing,
            kernel_context_cow.as_ref(),
        );
        assert!(
            checker
                .check_clause(parsed.clause(), kernel_context_cow.as_ref())
                .is_some(),
            "generic claim should be accepted once inserted"
        );
    }
}
