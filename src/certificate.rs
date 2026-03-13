use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use std::borrow::Cow;

use crate::claim_codec::ClaimCodec;
use crate::code_generator::{CodeGenerator, Error as CodeGenError};
use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::elaborator::stack::Stack;
use crate::elaborator::to_term::lower_value_to_term_existing;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::{CertificateStep, Claim, SatisfyStep};
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::clause::Clause;
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_term;
use crate::kernel::variable_map::VariableMap;
use crate::module::ModuleDescriptor;
use crate::project::Project;
use crate::prover::proof::ConcreteStep;
use crate::prover::synthetic::{
    witness_application, witness_signature, WitnessEntry, WitnessRegistry,
};
use crate::syntax::expression::Expression;
use crate::syntax::statement::{Statement, StatementInfo};

/// Information about a single line in a checked certificate proof.
#[derive(Debug, Clone)]
pub struct CertificateLine {
    /// The structured clause value after quoting the checked kernel clause.
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
    /// Named-witness mode rejects legacy `choose(...)` certificate syntax.
    fn certificate_allows_choose() -> bool {
        !cfg!(feature = "nwit")
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
    /// Requires the kernel_context (to quote clauses)
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
    /// Requires the kernel_context (to quote clauses)
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
        let return_type = kernel_context.quote_type_with_context(
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
            kernel_context.quote_term_with_context(&opened_body, &local_context, false);

        let (condition, return_name) = if arguments.is_empty() {
            let specialized_body = witness
                .body
                .substitute_bound(
                    0,
                    &witness_application(witness.symbol, &witness.ambient_context),
                )
                .shift_bound(0, -1);
            (
                kernel_context.quote_term_with_context(
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
            CertificateStep::Claim(_) => ClaimCodec::ensure_claim_code_parses_as_claim(line),
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
        ClaimCodec::serialize_claim_with_args(claim, kernel_context, bindings).map_err(|err| {
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
        let mut evaluator = Evaluator::new_with_allow_choose(
            project,
            bindings,
            None,
            Self::certificate_allows_choose(),
        );
        let mut claim_step_from_expr =
            |expr: &Expression| -> Result<CertificateStep, CodeGenError> {
                if let Some(claim) = ClaimCodec::try_deserialize_claim_expression(
                    expr,
                    project,
                    bindings.as_ref(),
                    kernel_context.to_mut(),
                    Self::certificate_allows_choose(),
                )? {
                    return Ok(CertificateStep::Claim(claim));
                }
                let value = evaluator.evaluate_value(expr, Some(&AcornType::Bool))?;
                let term = lower_value_to_term_existing(kernel_context.to_mut(), &value, None)?;
                let term = normalize_term(&term);
                Ok(CertificateStep::Claim(ClaimCodec::claim_from_plain_term(
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
        let term = lower_value_to_term_existing(kernel_context, value, type_var_map.as_ref())?;
        let term = normalize_term(&term);
        ClaimCodec::claim_from_plain_term(&term, kernel_context)
    }

    /// Lower a parsed certificate proposition to the checker clauses introduced by `satisfy`.
    fn checker_clauses_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Vec<Clause>, CodeGenError> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        let term = lower_value_to_term_existing(kernel_context, value, type_var_map.as_ref())?;
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
        let mut evaluator = Evaluator::new_with_allow_choose(
            project,
            bindings,
            None,
            Self::certificate_allows_choose(),
        );
        let type_params = evaluator.evaluate_type_params(&vss.type_params)?;
        for param in &type_params {
            bindings.add_arbitrary_type(param.clone());
            kernel_context.register_arbitrary_type(param);
        }

        let mut stack = Stack::new();
        let mut general_evaluator = Evaluator::new_with_allow_choose(
            project,
            bindings,
            None,
            Self::certificate_allows_choose(),
        );
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

        let mut specific_evaluator = Evaluator::new_with_allow_choose(
            project,
            bindings,
            None,
            Self::certificate_allows_choose(),
        );
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
        ClaimCodec::serialize_claim_with_args(claim, kernel_context, bindings)
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
        ClaimCodec::deserialize_claim_with_args(
            code,
            project,
            bindings,
            kernel_context,
            Self::certificate_allows_choose(),
        )
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
                let value = kernel_context.quote_clause(&checked_step.clause, None, None, false);
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
            Claim::new(general_clause.clone(), VariableMap::new())
                .map_err(CodeGenError::GeneratedBadCode)?
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

        if cfg!(feature = "nwit") {
            let err = Certificate::deserialize_claim_with_args(
                line,
                &project,
                &bindings,
                &kernel_context,
            )
            .expect_err("nwit should reject choose in claim-with-args deserialization");
            assert!(
                err.to_string()
                    .contains("choose expressions are not allowed here"),
                "unexpected error: {}",
                err
            );
            return;
        }

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
    fn test_parse_code_line_handles_choose_claim_shape() {
        let code = r#"
            theorem goal {
                true = true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let result = Certificate::parse_code_line(
            "choose(x0: Bool) { x0 } = true",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        );

        if cfg!(feature = "nwit") {
            let err = match result {
                Ok(_) => panic!("nwit should reject choose claims"),
                Err(err) => err,
            };
            assert!(
                err.to_string()
                    .contains("choose expressions are not allowed here"),
                "unexpected error: {}",
                err
            );
            return;
        }

        let step = result.expect("choose claim parsing should succeed for certificate parsing");

        let claim = expect_claim(step);
        assert_eq!(claim.var_map().len(), 0);
    }

    #[test]
    fn test_parse_code_line_handles_closed_binder_claims_with_choose() {
        let code = r#"
            let identity: Bool -> Bool = axiom

            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
        let result = Certificate::parse_code_line(
            "identity(choose(k0: Bool) { forall(x0: Bool) { not identity(x0) = k0 } }) = choose(k1: Bool) { forall(x1: Bool) { not identity(x1) = k1 } }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        );

        if cfg!(feature = "nwit") {
            let err = match result {
                Ok(_) => panic!("nwit should reject choose in closed binder-heavy claims"),
                Err(err) => err,
            };
            assert!(
                err.to_string()
                    .contains("choose expressions are not allowed here"),
                "unexpected error: {}",
                err
            );
            return;
        }

        let step = result.expect("closed binder-heavy claim should parse");

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
        let result = Certificate::parse_code_line(
            "choose(x0: Bool) { x0 } = true",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        );

        if cfg!(feature = "nwit") {
            let err = match result {
                Ok(_) => panic!("nwit should reject choose claims before checking"),
                Err(err) => err,
            };
            assert!(
                err.to_string()
                    .contains("choose expressions are not allowed here"),
                "unexpected error: {}",
                err
            );
            return;
        }

        let step = result.expect("choose claim parsing should succeed for certificate parsing");

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
    fn test_from_concrete_steps_handles_binder_claim_args() {
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

        let result = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            &kernel_context,
            &bindings,
        );

        if cfg!(feature = "nwit") {
            let err = result.expect_err("nwit should reject choose during certificate generation");
            assert!(
                err.to_string()
                    .contains("choose expressions are not supported with feature \"nwit\""),
                "unexpected error: {}",
                err
            );
            return;
        }

        let cert = result.expect("certificate generation should succeed");
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
                "function[T0](x0: (T0, T0) -> Bool, x1: T0, x2: T0) { x0(x1, x2) }[Bool]((=), false, true)"
            ]
        );
    }

    #[test]
    fn test_from_concrete_steps_roundtrips_partial_builtin_used_as_value() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, kernel_context) = setup_claim_codec_env(code);
        let kernel = &kernel_context;
        let generic = kernel.parse_clause(
            "x0(x1) = x1(false, true)",
            &["(Bool -> Bool -> Bool) -> Bool", "Bool -> Bool -> Bool"],
        );

        let mut var_map = VariableMap::new();
        let predicate_type = kernel.type_store.to_type_term_with_vars(
            &crate::elaborator::acorn_type::AcornType::functional(
                vec![
                    crate::elaborator::acorn_type::AcornType::Bool,
                    crate::elaborator::acorn_type::AcornType::Bool,
                ],
                crate::elaborator::acorn_type::AcornType::Bool,
            ),
            None,
        );
        let predicate = Term::atom(Atom::BoundVariable(0));
        let predicate_application = predicate.apply(&[Term::new_false(), Term::new_true()]);
        var_map.set(0, Term::lambda(predicate_type, predicate_application));
        var_map.set(1, kernel.parse_term("eq(Bool)"));

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
        assert_eq!(proof.len(), 1);
        assert!(
            proof[0].contains("(=)"),
            "expected partial eq to serialize as an operator ref, got: {}",
            proof[0]
        );

        let reparsed = Certificate::deserialize_claim_with_args(
            &proof[0],
            &project,
            &bindings,
            &kernel_context,
        )
        .expect("serialized claim should parse back");
        let expected_claim = Claim::new(
            concrete_steps[0].generic.clone(),
            concrete_steps[0].var_maps[0].0.clone(),
        )
        .expect("expected claim should normalize");
        let expected_clause = expected_claim
            .normalized_specialized_clause(&kernel_context)
            .expect("expected claim should specialize");
        let reparsed_clause = reparsed
            .normalized_specialized_clause(&kernel_context)
            .expect("reparsed claim should specialize");
        assert_eq!(reparsed_clause, expected_clause);
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
