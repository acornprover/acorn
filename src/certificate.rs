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
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::elaborator::stack::Stack;
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
use crate::kernel::variable_map::VariableMap;
use crate::module::{ModuleDescriptor, ModuleId};
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
        let (ordered_steps, generation_kernel_context) =
            if let Some(witness_registry) = witness_registry {
                Self::emit_named_witnesses_with_context(
                    ordered_steps,
                    witness_registry,
                    generation_kernel_context,
                    bindings.module_id(),
                )?
            } else {
                (ordered_steps, generation_kernel_context)
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
        Self::parse_cert_steps_internal(proof, project, bindings, kernel_context, false)
    }

    fn parse_cert_steps_internal(
        proof: &[String],
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        kernel_context: &mut Cow<KernelContext>,
        #[cfg_attr(not(feature = "validate"), allow(unused_variables))] validate_generated: bool,
    ) -> Result<Vec<CertificateStep>, CodeGenError> {
        let mut steps = Vec::with_capacity(proof.len());
        for code in proof {
            #[cfg(feature = "validate")]
            let pre_bindings = validate_generated.then(|| bindings.as_ref().clone());
            #[cfg(feature = "validate")]
            let pre_kernel_context = validate_generated.then(|| kernel_context.as_ref().clone());

            let step = Self::parse_code_line(code, project, bindings, kernel_context)?;

            #[cfg(feature = "validate")]
            if validate_generated {
                Self::validate_certificate_step_roundtrip(
                    &step,
                    code,
                    project,
                    pre_bindings
                        .as_ref()
                        .expect("generated cert validation should capture pre-bindings"),
                    pre_kernel_context
                        .as_ref()
                        .expect("generated cert validation should capture pre-kernel-context"),
                    bindings.as_ref(),
                    kernel_context.as_ref(),
                )?;
            }

            steps.push(step);
        }
        Ok(steps)
    }

    /// Replace eligible proof claims with named-witness steps and emit assumption-backed
    /// witnesses before their first use.
    #[cfg(test)]
    fn emit_named_witnesses(
        ordered_steps: Vec<CertificateStep>,
        witness_registry: &WitnessRegistry,
        kernel_context: &KernelContext,
    ) -> Result<Vec<CertificateStep>, CodeGenError> {
        Ok(Self::emit_named_witnesses_with_context(
            ordered_steps,
            witness_registry,
            kernel_context.clone(),
            ModuleId::default(),
        )?
        .0)
    }

    /// Emit named witnesses and return the updated kernel context.
    ///
    /// Synthetic witness steps may introduce fresh scoped constants, so callers must serialize
    /// later steps against the returned context rather than the original prover context.
    fn emit_named_witnesses_with_context(
        ordered_steps: Vec<CertificateStep>,
        witness_registry: &WitnessRegistry,
        kernel_context: KernelContext,
        module_id: ModuleId,
    ) -> Result<(Vec<CertificateStep>, KernelContext), CodeGenError> {
        WitnessEmitter::new(ordered_steps, witness_registry, kernel_context, module_id)?.emit()
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
        let arguments: Vec<(String, AcornType)> = arguments
            .into_iter()
            .enumerate()
            .map(|(i, (_, arg_type))| (format!("arg{}", i), arg_type))
            .collect();
        let return_type = kernel_context.quote_type_with_context(
            witness.return_type.clone(),
            &witness.ambient_context,
            false,
        );
        let type_param_placeholders = vec![AcornValue::Bool(true); type_params.len()];

        let mut local_context = witness.ambient_context.clone();
        local_context.push_type(witness.return_type.clone());
        let opened_body = witness
            .body
            .substitute_bound(
                0,
                &Term::new_variable(witness.ambient_context.len() as AtomId),
            )
            .shift_bound(0, -1);
        let general_condition = kernel_context
            .quote_term_with_context(&opened_body, &local_context, false)
            .bind_values(0, local_context.len() as AtomId, &type_param_placeholders);
        let specialized_body = witness
            .body
            .substitute_bound(
                0,
                &witness_application(witness.symbol, &witness.ambient_context),
            )
            .shift_bound(0, -1);
        let specialized_condition = kernel_context
            .quote_term_with_context(&specialized_body, &witness.ambient_context, false)
            .bind_values(
                0,
                witness.ambient_context.len() as AtomId,
                &type_param_placeholders,
            );
        let mut checker_kernel_context = kernel_context.clone();

        let (condition, return_name, specialized_clause, witness_clauses) = if arguments.is_empty()
        {
            let specialized_clause = Self::maybe_specialized_clause_for_proposition(
                &mut checker_kernel_context,
                &specialized_condition,
                &type_params,
            )?;
            let witness_clauses = Self::exact_witness_clauses_for_proposition(
                &mut checker_kernel_context,
                &specialized_condition,
                &type_params,
            )?
            .into_iter()
            .filter(|clause| specialized_clause.as_ref() != Some(clause))
            .collect();
            (
                specialized_condition,
                None,
                specialized_clause,
                witness_clauses,
            )
        } else {
            let arg_types: Vec<AcornType> = arguments
                .iter()
                .map(|(_, arg_type)| arg_type.clone())
                .collect();
            let specialized_value = AcornValue::ForAll(arg_types, Box::new(specialized_condition));
            let specialized_clause = Self::maybe_specialized_clause_for_proposition(
                &mut checker_kernel_context,
                &specialized_value,
                &type_params,
            )?;
            let witness_clauses = Self::exact_witness_clauses_for_proposition(
                &mut checker_kernel_context,
                &specialized_value,
                &type_params,
            )?;
            (
                general_condition,
                Some(format!("{}_result", witness.name)),
                specialized_clause,
                witness_clauses,
            )
        };
        let witness_clauses = witness_clauses
            .into_iter()
            .map(|clause| clause.normalized())
            .collect();

        Ok(SatisfyStep {
            name: witness.name.to_string(),
            type_params,
            arguments,
            return_name,
            return_type,
            condition,
            justification,
            specialized_clause,
            witness_clauses,
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

    #[cfg(feature = "validate")]
    fn validate_certificate_step_roundtrip(
        step: &CertificateStep,
        original_code: &str,
        project: &Project,
        pre_bindings: &BindingMap,
        pre_kernel_context: &KernelContext,
        post_bindings: &BindingMap,
        post_kernel_context: &KernelContext,
    ) -> Result<(), CodeGenError> {
        step.validate_roundtrip_shape(post_kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;

        let mut generator = CodeGenerator::new_for_certificate(post_bindings);
        let serialized = Self::serialize_certificate_step(
            step,
            &mut generator,
            post_kernel_context,
            post_bindings,
        )?;

        let mut roundtrip_bindings = Cow::Owned(pre_bindings.clone());
        let mut roundtrip_kernel_context = Cow::Owned(pre_kernel_context.clone());
        let reparsed = Self::parse_code_line(
            &serialized,
            project,
            &mut roundtrip_bindings,
            &mut roundtrip_kernel_context,
        )?;

        if &reparsed != step {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "certificate step did not roundtrip in validate mode: original {:?}, serialized {:?}, reparsed {:?}",
                original_code, serialized, reparsed
            )));
        }

        Ok(())
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

    #[cfg(test)]
    pub(crate) fn serialize_claim_step_for_test(
        claim: &Claim,
        kernel_context: &KernelContext,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        Self::serialize_claim_step(claim, kernel_context, bindings)
    }

    /// Parse a single code line, updating bindings/kernel_context, and return structured result.
    pub fn parse_code_line(
        code: &str,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        kernel_context: &mut Cow<KernelContext>,
    ) -> Result<CertificateStep, CodeGenError> {
        let statement = Statement::parse_str_with_options(&code, true)?;
        let mut evaluator = Evaluator::new(project, bindings, None);
        let mut claim_step_from_expr =
            |expr: &Expression| -> Result<CertificateStep, CodeGenError> {
                if let Some(claim) = ClaimCodec::try_deserialize_claim_expression(
                    expr,
                    project,
                    bindings.as_ref(),
                    kernel_context.to_mut(),
                )? {
                    return Ok(CertificateStep::Claim(claim));
                }
                let value = evaluator.evaluate_value(expr, Some(&AcornType::Bool))?;
                Ok(CertificateStep::Claim(Self::claim_from_clause_value(
                    kernel_context.to_mut(),
                    &value,
                    None,
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

    /// Lower a clause-shaped certificate value to the canonical empty-map claim form.
    fn claim_from_clause_value(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Claim, CodeGenError> {
        let clause = kernel_context
            .lower_clause(value, NewConstantType::Local, type_var_map)
            .map_err(CodeGenError::GeneratedBadCode)?;
        Claim::new(clause, VariableMap::new()).map_err(CodeGenError::GeneratedBadCode)
    }

    /// Wrap a certificate-local boolean value as a proposition so it can use proposition lowering.
    fn local_certificate_proposition(value: &AcornValue, type_params: &[TypeParam]) -> Proposition {
        Proposition::new(
            value.clone(),
            type_params.to_vec(),
            Source::anonymous(ModuleId::default(), Default::default(), 1),
        )
    }

    /// Lower a parsed certificate proposition to the single implicit claim used by `satisfy`.
    fn claim_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Claim, CodeGenError> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        Self::claim_from_clause_value(kernel_context, value, type_var_map)
    }

    /// Lower a witness proposition to the exact clause shape inserted when the witness opens.
    ///
    /// This opens only the leading `forall`s and keeps the remaining proposition as one initial
    /// clause, which matches the clause introduced by proof-time witness opening.
    fn exact_witness_clauses_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Vec<Clause>, CodeGenError> {
        let proposition = Self::local_certificate_proposition(value, type_params);
        Ok(kernel_context
            .lower_proposition_to_clauses(&proposition)
            .map_err(CodeGenError::GeneratedBadCode)?
            .into_iter()
            .map(|clause| clause.normalized())
            .collect())
    }

    /// Lower a parsed certificate proposition to a single closed checker clause.
    fn maybe_specialized_clause_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Option<Clause>, CodeGenError> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        let term =
            kernel_context.lower_term(value, NewConstantType::Local, type_var_map.as_ref())?;
        let term = normalize_term(&term);
        let checker_term = match kernel_context.term_to_checker_term(&term, type_var_map) {
            Ok(term) => term,
            Err(_) => return Ok(None),
        };
        Ok(Some(
            Clause::from_literals_unnormalized(
                vec![Literal::positive(checker_term)],
                &LocalContext::empty(),
            )
            .normalized(),
        ))
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
        let mut evaluator = Evaluator::new(project, bindings, None);
        let type_params = evaluator.evaluate_type_params(&vss.type_params)?;
        for param in &type_params {
            bindings.add_arbitrary_type(param.clone());
            kernel_context.register_arbitrary_type(param);
        }

        let mut stack = Stack::new();
        let mut general_evaluator = Evaluator::new(project, bindings, None);
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

        let mut specific_evaluator = Evaluator::new(project, bindings, None);
        let specific_condition =
            specific_evaluator.evaluate_value(&vss.condition, Some(&AcornType::Bool))?;

        let general_claim = AcornValue::Exists(quant_types, Box::new(general_condition));
        let justification =
            Self::claim_for_proposition(kernel_context, &general_claim, &type_params)?;
        let specialized_clause = Self::maybe_specialized_clause_for_proposition(
            kernel_context,
            &specific_condition,
            &type_params,
        )?;
        let witness_clauses = Self::exact_witness_clauses_for_proposition(
            kernel_context,
            &specific_condition,
            &type_params,
        )?
        .into_iter()
        .filter(|clause| specialized_clause.as_ref() != Some(clause))
        .collect();

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
            specialized_clause,
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
        let witness_clauses = Self::exact_witness_clauses_for_proposition(
            kernel_context,
            &specialized_claim,
            &type_params,
        )?;
        let specialized_clause = Self::maybe_specialized_clause_for_proposition(
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
            specialized_clause,
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
        ClaimCodec::deserialize_claim_with_args(code, project, bindings, kernel_context)
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
        checker: Checker,
        project: &Project,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<CheckedCertificate, CodeGenError> {
        self.check_with_usage_internal(checker, project, bindings, kernel_context, false)
    }

    fn check_with_usage_internal(
        &self,
        mut checker: Checker,
        project: &Project,
        mut bindings: Cow<BindingMap>,
        mut kernel_context: Cow<KernelContext>,
        validate_generated: bool,
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
        let cert_steps = Self::parse_cert_steps_internal(
            proof,
            project,
            &mut bindings,
            &mut kernel_context,
            validate_generated,
        )?;
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

    #[cfg(feature = "validate")]
    pub fn check_generated_with_usage(
        &self,
        checker: Checker,
        project: &Project,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<CheckedCertificate, CodeGenError> {
        self.check_with_usage_internal(checker, project, bindings, kernel_context, true)
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
///
/// The emitter runs in three phases:
/// 1. Precompute where prover-generated witnesses should be anchored or substituted.
/// 2. Walk the ordered proof steps, materializing witnesses before their first use.
/// 3. When a specialized claim still has a top-level positive `exists`, open a certificate-local
///    witness for it and replay any unary witness clauses at the fresh witness.
struct WitnessEmitter<'a> {
    ordered_steps: Vec<CertificateStep>,
    claim_generic_clauses: Vec<Option<Clause>>,
    claim_clauses: Vec<Option<Clause>>,
    referenced_ids: Vec<Vec<AtomId>>,
    kernel_context: KernelContext,
    module_id: ModuleId,
    synthetic_witness_registry: WitnessRegistry,
    witness_registry: &'a WitnessRegistry,
    witness_steps: HashMap<AtomId, SatisfyStep>,
    claim_replacements: HashMap<usize, AtomId>,
    replacement_indices: HashMap<AtomId, usize>,
    claim_anchors: HashMap<usize, Vec<AtomId>>,
    anchor_indices: HashMap<AtomId, usize>,
    declared: HashSet<AtomId>,
    buffered: Vec<usize>,
    emitted: Vec<bool>,
    in_progress: HashSet<AtomId>,
    output: Vec<CertificateStep>,
}

#[derive(Clone, Copy)]
enum WitnessPlacement {
    Standalone,
    Anchor(usize),
    Replace(usize),
}

impl<'a> WitnessEmitter<'a> {
    /// Precompute the witness steps and the claim positions they should replace.
    fn new(
        ordered_steps: Vec<CertificateStep>,
        witness_registry: &'a WitnessRegistry,
        kernel_context: KernelContext,
        module_id: ModuleId,
    ) -> Result<Self, CodeGenError> {
        let num_steps = ordered_steps.len();
        let claim_generic_clauses: Vec<Option<Clause>> = ordered_steps
            .iter()
            .map(|step| match step {
                CertificateStep::Claim(claim) => Some(claim.normalized_generic_clause()),
                CertificateStep::Satisfy(_) => None,
            })
            .collect();
        let claim_clauses: Vec<Option<Clause>> = ordered_steps
            .iter()
            .map(|step| Certificate::claim_clause(step, &kernel_context))
            .collect::<Result<_, _>>()?;
        let referenced_ids: Vec<Vec<AtomId>> = ordered_steps
            .iter()
            .map(|step| Certificate::collect_claim_witness_ids(step, &kernel_context))
            .collect::<Result<_, _>>()?;

        let mut emitter = Self {
            ordered_steps,
            claim_generic_clauses,
            claim_clauses,
            referenced_ids,
            kernel_context,
            module_id,
            synthetic_witness_registry: WitnessRegistry::new(),
            witness_registry,
            witness_steps: HashMap::new(),
            claim_replacements: HashMap::new(),
            replacement_indices: HashMap::new(),
            claim_anchors: HashMap::new(),
            anchor_indices: HashMap::new(),
            declared: HashSet::new(),
            buffered: Vec::new(),
            emitted: vec![false; num_steps],
            in_progress: HashSet::new(),
            output: Vec::new(),
        };
        for ids in emitter.referenced_ids.clone() {
            for local_id in ids {
                emitter.prepare_witness(local_id)?;
            }
        }
        for (&local_id, _) in witness_registry.iter() {
            emitter.prepare_witness(local_id)?;
        }
        Ok(emitter)
    }

    /// Emit the final certificate steps with named witnesses substituted in.
    fn emit(mut self) -> Result<(Vec<CertificateStep>, KernelContext), CodeGenError> {
        for index in 0..self.ordered_steps.len() {
            self.schedule_step(index, index)?;
            self.flush_buffered(index)?;
        }
        Ok((self.output, self.kernel_context))
    }

    fn declaration_index(&self, local_id: AtomId) -> Option<usize> {
        self.replacement_indices
            .get(&local_id)
            .copied()
            .or_else(|| self.anchor_indices.get(&local_id).copied())
    }

    /// Delay any step whose first witness use depends on a later replacement claim.
    fn step_needs_future_witness(&self, index: usize, current_index: usize) -> bool {
        self.referenced_ids[index].iter().any(|local_id| {
            !self.declared.contains(local_id)
                && self
                    .declaration_index(*local_id)
                    .is_some_and(|declaration_index| declaration_index > current_index)
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

        self.emit_ready_step(index, current_index)?;

        self.emit_anchors_for_step(index)?;

        Ok(())
    }

    /// Emit a step once every witness it references can already be declared.
    fn emit_ready_step(&mut self, index: usize, current_index: usize) -> Result<(), CodeGenError> {
        if self.emitted[index] {
            return Ok(());
        }

        let step = self.ordered_steps[index].clone();
        if self.claim_clauses[index].is_none() {
            self.push_output_step(step)?;
            self.emitted[index] = true;
            return Ok(());
        }

        for local_id in self.referenced_ids[index].clone() {
            self.ensure_declared(local_id, current_index)?;
        }
        if let CertificateStep::Claim(claim) = &step {
            if let Some((local_id, parent_local_id, rewritten_step)) =
                self.specialized_positive_exists_step(claim)?
            {
                self.ensure_declared(local_id, current_index)?;
                self.push_output_step(step.clone())?;
                self.emit_witness_step(
                    local_id,
                    CertificateStep::Satisfy(rewritten_step),
                    Some(parent_local_id),
                )?;
                self.emitted[index] = true;
                return Ok(());
            }
        }
        self.push_output_step(step)?;
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
                self.emit_anchors_for_step(index)?;
                made_progress = true;
            }
        }

        self.buffered = next_buffered;
        Ok(())
    }

    /// Prepare one witness step and remember which claim it should replace, if any.
    fn prepare_witness(&mut self, local_id: AtomId) -> Result<(), CodeGenError> {
        if self.witness_steps.contains_key(&local_id) {
            return Ok(());
        }
        let Some(witness) = self.witness_registry.get(local_id) else {
            return Ok(());
        };

        for dependency_id in witness.referenced_scoped_constants() {
            self.prepare_witness(dependency_id)?;
        }

        let general_clause = witness.general_clause.clone();
        let placement = self.find_witness_placement(&general_clause, &witness.name)?;
        let justification = match placement {
            WitnessPlacement::Anchor(index) => {
                let CertificateStep::Claim(claim) = &self.ordered_steps[index] else {
                    panic!("claim_clauses only records claim steps");
                };
                claim.clone()
            }
            WitnessPlacement::Standalone | WitnessPlacement::Replace(_) => {
                Claim::new(general_clause.clone(), VariableMap::new())
                    .map_err(CodeGenError::GeneratedBadCode)?
            }
        };
        match placement {
            WitnessPlacement::Standalone => {}
            WitnessPlacement::Replace(index) => {
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
            WitnessPlacement::Anchor(index) => {
                self.claim_anchors.entry(index).or_default().push(local_id);
                self.anchor_indices.insert(local_id, index);
            }
        }
        let step =
            Certificate::witness_entry_to_step(witness, justification, &self.kernel_context)?;
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

        if let Some(index) = self.declaration_index(local_id) {
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
        self.emit_witness_step(local_id, CertificateStep::Satisfy(step), None)?;
        self.in_progress.remove(&local_id);
        Ok(())
    }

    /// Emit one `let ... satisfy` witness declaration and record any follow-on clauses it enables.
    fn emit_witness_step(
        &mut self,
        local_id: AtomId,
        step: CertificateStep,
        parent_local_id: Option<AtomId>,
    ) -> Result<(), CodeGenError> {
        assert!(matches!(step, CertificateStep::Satisfy(_)));
        self.push_output_step(step)?;
        self.declared.insert(local_id);
        let _ = parent_local_id;
        Ok(())
    }

    fn claim_specialization_source_local_id(claim: &Claim) -> Option<AtomId> {
        if claim.clause().get_local_context().len() != 1 {
            return None;
        }
        let term = claim.var_map().get_mapping(0)?;
        match term.as_ref().decompose() {
            Decomposition::Atom(Atom::Symbol(Symbol::ScopedConstant(local_id))) => Some(*local_id),
            _ => None,
        }
    }

    fn witness_module_id(&self, parent_local_id: AtomId) -> ModuleId {
        self.witness_registry
            .get(parent_local_id)
            .map(|witness| witness.name.module_id())
            .or_else(|| {
                self.synthetic_witness_registry
                    .get(parent_local_id)
                    .map(|witness| witness.name.module_id())
            })
            .unwrap_or(self.module_id)
    }

    fn push_output_step(&mut self, step: CertificateStep) -> Result<(), CodeGenError> {
        self.output.push(step);
        Ok(())
    }

    fn emit_anchors_for_step(&mut self, index: usize) -> Result<(), CodeGenError> {
        if let Some(local_ids) = self.claim_anchors.get(&index).cloned() {
            for local_id in local_ids {
                self.emit_witness(local_id)?;
            }
        }
        Ok(())
    }

    /// Open a specialized top-level positive existential into a fresh synthetic witness step.
    fn specialized_positive_exists_step(
        &mut self,
        claim: &Claim,
    ) -> Result<Option<(AtomId, AtomId, SatisfyStep)>, CodeGenError> {
        let Some(parent_local_id) = Self::claim_specialization_source_local_id(claim) else {
            return Ok(None);
        };
        let specialized_clause = claim
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let Some(reduction) = specialized_clause.positive_exists_reduction(&self.kernel_context)
        else {
            return Ok(None);
        };
        let module_id = self.witness_module_id(parent_local_id);
        let opening = self.synthetic_witness_registry.open_positive_exists(
            &mut self.kernel_context,
            module_id,
            &specialized_clause,
            &reduction,
        );
        let synthetic_local_id = opening
            .term
            .iter_atoms()
            .find_map(|atom| match atom {
                Atom::Symbol(Symbol::ScopedConstant(local_id)) => Some(*local_id),
                _ => None,
            })
            .expect("synthetic witness term should reference its scoped constant");
        let synthetic_witness = self
            .synthetic_witness_registry
            .get(synthetic_local_id)
            .expect("synthetic witness should be registered");
        let step = Certificate::witness_entry_to_step(
            synthetic_witness,
            claim.clone(),
            &self.kernel_context,
        )?;
        Ok(Some((synthetic_local_id, parent_local_id, step)))
    }

    fn find_witness_placement(
        &self,
        general_clause: &Clause,
        _witness_name: &impl std::fmt::Display,
    ) -> Result<WitnessPlacement, CodeGenError> {
        let matching_claims: Vec<usize> = self
            .claim_generic_clauses
            .iter()
            .enumerate()
            .filter_map(|(index, clause)| {
                if self.claim_replacements.contains_key(&index) {
                    return None;
                }
                if clause.as_ref() == Some(general_clause)
                    || self.claim_clauses[index].as_ref() == Some(general_clause)
                {
                    Some(index)
                } else {
                    None
                }
            })
            .collect();
        if let Some(index) = matching_claims.first().copied() {
            // Exact matching claims can legitimately repeat in the displayed proof.
            // Anchoring at the earliest surviving claim keeps the witness declaration
            // close to the original justification without requiring uniqueness.
            return Ok(WitnessPlacement::Anchor(index));
        }

        let implying_claims: Vec<usize> = self
            .claim_clauses
            .iter()
            .enumerate()
            .filter_map(|(index, clause)| {
                if self.claim_replacements.contains_key(&index) {
                    return None;
                }
                let clause = clause.as_ref()?;
                let mut checker = Checker::new();
                checker.insert_clause(clause, StepReason::Testing, &self.kernel_context);
                checker
                    .check_clause(general_clause, &self.kernel_context)
                    .is_some()
                    .then_some(index)
            })
            .collect();
        Ok(if implying_claims.len() == 1 {
            WitnessPlacement::Replace(implying_claims[0])
        } else {
            WitnessPlacement::Standalone
        })
    }
}

#[cfg(test)]
mod tests;
