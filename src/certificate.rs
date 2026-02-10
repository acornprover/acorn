use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use std::borrow::Cow;

use crate::code_generator::{CodeGenerator, Error as CodeGenError, SyntheticNameSet};
use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::stack::Stack;
use crate::elaborator::unresolved_constant::UnresolvedConstant;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::{CertificateStep, Claim};
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::term::Term;
use crate::kernel::variable_map::VariableMap;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::normalizer::{NormalizationContext, Normalizer};
use crate::project::Project;
use crate::prover::proof::ConcreteStep;
use crate::syntax::expression::{Declaration, Expression};
use crate::syntax::statement::{Statement, StatementInfo};
use crate::syntax::token::TokenType;

#[cfg(all(test, feature = "bigcert"))]
use crate::kernel::local_context::LocalContext;

/// Information about a single line in a checked certificate proof.
#[derive(Debug, Clone)]
pub struct CertificateLine {
    /// The statement from the certificate (the code line).
    pub statement: String,

    /// The reason this step was accepted.
    pub reason: StepReason,
}

fn clause_to_code(
    clause: &crate::kernel::clause::Clause,
    normalizer: &Normalizer,
    bindings: &Cow<BindingMap>,
) -> String {
    let value = normalizer.denormalize(clause, None, None, false);
    let mut code_gen = CodeGenerator::new(bindings);
    code_gen
        .value_to_code(&value)
        .unwrap_or_else(|_| format!("{} (internal)", clause))
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
    fn dequalify_synthetic_name_refs(
        code: String,
        synthetic_names: Option<&HashMap<(ModuleId, AtomId), String>>,
    ) -> String {
        let Some(synthetic_names) = synthetic_names else {
            return code;
        };
        let mut normalized = code;
        for synthetic_name in synthetic_names.values() {
            let pattern = format!(
                r"(?:lib\([^)]+\)|[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\.{}\b",
                regex::escape(synthetic_name)
            );
            let re = Regex::new(&pattern).expect("synthetic dequalification regex should compile");
            normalized = re
                .replace_all(&normalized, synthetic_name.as_str())
                .into_owned();
        }
        normalized
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

    /// Check if this certificate has a proof
    pub fn has_proof(&self) -> bool {
        self.proof.is_some()
    }

    /// Convert a ConcreteProof to a Certificate (string format).
    ///
    /// This is the serialization boundary where resolved IDs are converted back to names.
    /// Requires the normalizer (to denormalize clauses and look up synthetic definitions)
    /// and the bindings (to generate readable names).
    pub fn from_concrete_steps(
        goal: String,
        concrete_steps: &[ConcreteStep],
        normalizer: &Normalizer,
        bindings: &BindingMap,
    ) -> Result<Certificate, CodeGenError> {
        let mut generator = CodeGenerator::new(bindings);
        let mut generation_normalizer = normalizer.clone();
        let mut names = SyntheticNameSet::new();
        let mut ordered_steps: Vec<CertificateStep> = Vec::new();

        for step in concrete_steps {
            let cert_steps = generator.concrete_step_to_certificate_steps(
                &mut names,
                step,
                &mut generation_normalizer,
            )?;
            for cert_step in cert_steps {
                if !ordered_steps.contains(&cert_step) {
                    ordered_steps.push(cert_step);
                }
            }
        }

        let mut answer = Vec::new();
        for step in &ordered_steps {
            #[cfg(feature = "bigcert")]
            let line = match step {
                CertificateStep::Claim(claim) => {
                    if claim.clause.get_local_context().is_empty() || claim.var_map.len() == 0 {
                        generator.certificate_step_to_code(&names, step, &generation_normalizer)?
                    } else {
                        Self::serialize_claim_with_names(
                            claim,
                            &generation_normalizer,
                            bindings,
                            Some(&names.synthetic_names),
                        )?
                    }
                }
                _ => generator.certificate_step_to_code(&names, step, &generation_normalizer)?,
            };

            #[cfg(not(feature = "bigcert"))]
            let line = generator.certificate_step_to_code(&names, step, &generation_normalizer)?;

            answer.push(line);
        }

        Ok(Certificate::new(goal, answer))
    }

    /// Convert a ConcreteProof to a Certificate (string format).
    ///
    /// This is the serialization boundary where resolved IDs are converted back to names.
    /// Requires the normalizer (to denormalize clauses and look up synthetic definitions)
    /// and the bindings (to generate readable names).
    pub fn from_concrete_proof(
        concrete_proof: &ConcreteProof,
        normalizer: &Normalizer,
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
            normalizer,
            bindings,
        )
    }

    /// Parse all certificate proof lines into kernel-level certificate steps.
    ///
    /// Parsing may update bindings/normalizer (for let...satisfy declarations), so callers
    /// should pass mutable views and then use the updated state for subsequent checking.
    pub fn parse_cert_steps(
        proof: &[String],
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
    ) -> Result<Vec<CertificateStep>, CodeGenError> {
        let mut steps = Vec::with_capacity(proof.len());
        for code in proof {
            steps.push(Self::parse_code_line(code, project, bindings, normalizer)?);
        }
        Ok(steps)
    }

    /// Parse a single code line, updating bindings/normalizer, and return structured result.
    pub fn parse_code_line(
        code: &str,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
    ) -> Result<CertificateStep, CodeGenError> {
        let statement = Statement::parse_str_with_options(&code, true)?;
        let mut evaluator = Evaluator::new(project, bindings, None);

        match statement.statement {
            StatementInfo::VariableSatisfy(vss) => {
                // Bind type parameters first
                let type_params = evaluator.evaluate_type_params(&vss.type_params)?;
                let type_param_names: Vec<String> =
                    type_params.iter().map(|p| p.name.clone()).collect();
                for param in &type_params {
                    bindings.to_mut().add_arbitrary_type(param.clone());
                    normalizer.to_mut().register_arbitrary_type(param);
                }
                let result = (|| -> Result<CertificateStep, CodeGenError> {
                    // Re-create evaluator with updated bindings
                    let mut evaluator = Evaluator::new(project, bindings, None);

                    // Parse declarations
                    let mut decls = vec![];
                    for decl in &vss.declarations {
                        match decl {
                            Declaration::Typed(name_token, type_expr) => {
                                let name = name_token.text().to_string();
                                let acorn_type = evaluator.evaluate_type(type_expr)?;
                                decls.push((name, acorn_type));
                            }
                            Declaration::SelfToken(_) => {
                                return Err(CodeGenError::GeneratedBadCode(
                                    "Unexpected 'self' in let...satisfy statement".to_string(),
                                ));
                            }
                        }
                    }

                    // Evaluate the condition
                    let mut stack = Stack::new();
                    evaluator.bind_args(&mut stack, &vss.declarations, None)?;
                    let condition_value = evaluator.evaluate_value_with_stack(
                        &mut stack,
                        &vss.condition,
                        Some(&AcornType::Bool),
                    )?;

                    // Look up synthetic definition
                    let types: Vec<_> = decls.iter().map(|(_, ty)| ty.clone()).collect();
                    let exists_value = AcornValue::exists(types.clone(), condition_value.clone());

                    // Build type_var_map from type parameters
                    let type_var_map: Option<HashMap<String, (AtomId, Term)>> =
                        if type_params.is_empty() {
                            None
                        } else {
                            Some(
                                type_params
                                    .iter()
                                    .enumerate()
                                    .map(|(i, p)| {
                                        let var_type = if let Some(tc) = &p.typeclass {
                                            let tc_id = normalizer
                                                .to_mut()
                                                .kernel_context_mut()
                                                .type_store
                                                .add_typeclass(tc);
                                            Term::typeclass(tc_id)
                                        } else {
                                            Term::type_sort()
                                        };
                                        (p.name.clone(), (i as AtomId, var_type))
                                    })
                                    .collect(),
                            )
                        };

                    let synthetic_definition = match normalizer
                        .to_mut()
                        .get_synthetic_definition(&exists_value, type_var_map.as_ref())
                    {
                        Some(def) => Some(def.clone()),
                        None => {
                            if condition_value != AcornValue::Bool(true) {
                                return Err(CodeGenError::GeneratedBadCode(format!(
                                    "statement '{}' does not match any synthetic definition",
                                    code
                                )));
                            }
                            // Trivial condition requires the type to be inhabited
                            let kernel_context = normalizer.kernel_context();
                            for (name, acorn_type) in &decls {
                                let type_term = kernel_context
                                    .type_store
                                    .get_type_term(acorn_type)
                                    .map_err(|e| {
                                        CodeGenError::GeneratedBadCode(format!(
                                            "cannot convert type '{}' to term: {}",
                                            acorn_type, e
                                        ))
                                    })?;
                                if !kernel_context.provably_inhabited(&type_term, None) {
                                    return Err(CodeGenError::GeneratedBadCode(format!(
                                        "cannot create witness '{}' of type '{}' with trivial condition: \
                                     type is not provably inhabited",
                                        name, acorn_type
                                    )));
                                }
                            }
                            if decls.len() != 1 {
                                return Err(CodeGenError::GeneratedBadCode(
                                    "let ... satisfy with trivial condition may declare exactly one arbitrary witness"
                                        .to_string(),
                                ));
                            }
                            None
                        }
                    };

                    if let Some(def) = &synthetic_definition {
                        let atoms = &def.atoms;
                        if atoms.len() != decls.len() {
                            return Err(CodeGenError::GeneratedBadCode(
                                "let ... satisfy declaration count does not match synthetic definition"
                                    .to_string(),
                            ));
                        }
                        for (i, (name, acorn_type)) in decls.iter().enumerate() {
                            let (module_id, local_id) = atoms[i];
                            let synthetic_cname = ConstantName::Synthetic(module_id, local_id);

                            let (param_names, generic_type) = if !type_params.is_empty() {
                                let names: Vec<String> =
                                    type_params.iter().map(|p| p.name.clone()).collect();
                                (names, acorn_type.genericize(&type_params))
                            } else {
                                (vec![], acorn_type.clone())
                            };

                            let user_cname = ConstantName::unqualified(bindings.module_id(), name);
                            let type_args: Vec<_> = type_params
                                .iter()
                                .map(|p| AcornType::Variable(p.clone()))
                                .collect();

                            let resolved_value = AcornValue::constant(
                                synthetic_cname.clone(),
                                type_args,
                                acorn_type.clone(),
                                generic_type.clone(),
                                param_names.clone(),
                            );

                            let potential_value = if !type_params.is_empty() {
                                PotentialValue::Unresolved(UnresolvedConstant {
                                    name: synthetic_cname.clone(),
                                    params: type_params.clone(),
                                    generic_type: generic_type.clone(),
                                    args: vec![],
                                })
                            } else {
                                PotentialValue::Resolved(resolved_value)
                            };

                            bindings.to_mut().add_constant_alias(
                                user_cname,
                                synthetic_cname,
                                potential_value,
                                vec![],
                                None,
                            );
                        }
                        Ok(CertificateStep::DefineSynthetic {
                            atoms: def.atoms.clone(),
                            type_vars: def.type_vars.clone(),
                            clauses: def.clauses.clone(),
                        })
                    } else {
                        let (name, acorn_type) = decls
                            .first()
                            .expect("decls should have exactly one element for trivial let");
                        let cname = ConstantName::unqualified(bindings.module_id(), name);
                        bindings.to_mut().add_unqualified_constant(
                            name,
                            vec![],
                            acorn_type.clone(),
                            None,
                            None,
                            vec![],
                            None,
                            String::new(),
                        );
                        let atom = normalizer.to_mut().add_scoped_constant(
                            cname.clone(),
                            acorn_type,
                            type_var_map.as_ref(),
                        );
                        let Atom::Symbol(symbol) = atom else {
                            return Err(CodeGenError::GeneratedBadCode(
                                "internal error: add_scoped_constant returned non-symbol atom"
                                    .to_string(),
                            ));
                        };
                        Ok(CertificateStep::DefineArbitrary { symbol })
                    }
                })();

                // Type parameters in certificate lines are local to that line.
                for name in type_param_names {
                    bindings.to_mut().remove_type(&name);
                }

                result
            }
            StatementInfo::Claim(claim) => {
                let value = evaluator.evaluate_value(&claim.claim, Some(&AcornType::Bool))?;
                if let Some(claim) = Self::try_deserialize_claim_with_args_value(
                    value.clone(),
                    bindings.as_ref(),
                    normalizer.as_ref(),
                )? {
                    return Ok(CertificateStep::Claim(claim));
                }
                let module_id = bindings.module_id();
                let mut view = NormalizationContext::new_mut(normalizer.to_mut(), None, module_id);
                let clauses = view.value_to_denormalized_clauses(&value)?;
                if clauses.len() != 1 {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "claim must normalize to exactly one clause, got {}",
                        clauses.len()
                    )));
                }
                Ok(CertificateStep::Claim(Claim {
                    clause: clauses
                        .into_iter()
                        .next()
                        .expect("clauses has exactly one element"),
                    var_map: VariableMap::new(),
                }))
            }
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
        normalizer: &Normalizer,
        bindings: &BindingMap,
    ) -> Result<String, CodeGenError> {
        Self::serialize_claim_with_names(claim, normalizer, bindings, None)
    }

    fn serialize_claim_with_names(
        claim: &Claim,
        normalizer: &Normalizer,
        bindings: &BindingMap,
        synthetic_names: Option<&HashMap<(ModuleId, AtomId), String>>,
    ) -> Result<String, CodeGenError> {
        let local_context = claim.clause.get_local_context();
        let var_count = local_context.len();
        if var_count == 0 {
            return Err(CodeGenError::GeneratedBadCode(
                "cannot serialize claim-with-args for a clause with no local variables".to_string(),
            ));
        }

        let mut generator = CodeGenerator::new(bindings);
        let generic_value = normalizer.denormalize(&claim.clause, None, None, false);
        let generic_code = if let Some(synthetic_names) = synthetic_names {
            generator.value_to_code_with_synthetic_names(&generic_value, synthetic_names)?
        } else {
            generator.value_to_code(&generic_value)?
        };
        let generic_code = Self::dequalify_synthetic_name_refs(generic_code, synthetic_names);
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

        let used_var_count = claim
            .clause
            .literals
            .iter()
            .filter_map(|lit| {
                let left_max = lit.left.max_variable();
                let right_max = lit.right.max_variable();
                match (left_max, right_max) {
                    (Some(l), Some(r)) => Some(l.max(r)),
                    (Some(l), None) => Some(l),
                    (None, Some(r)) => Some(r),
                    (None, None) => None,
                }
            })
            .max()
            .map(|max| (max + 1) as usize)
            .unwrap_or(0);

        let kernel_context = normalizer.kernel_context();

        let mut type_param_decl_codes: Vec<String> = vec![];
        let mut type_arg_codes: Vec<String> = vec![];
        let mut value_decl_codes: Vec<String> = vec![];
        let mut value_arg_codes: Vec<String> = vec![];
        // Keep declaration names aligned with CodeGenerator's own naming strategy so the
        // lambda body and argument declarations use the same identifiers, even when
        // lower indices (e.g. x0, x1) are already occupied in bindings.
        let mut next_value_decl_id: u32 = 0;

        for var_id in 0..used_var_count {
            let var_type = local_context
                .get_var_type(var_id)
                .expect("local context should provide all variable types")
                .clone();

            let arg_term = claim.var_map.get_mapping(var_id as AtomId).ok_or_else(|| {
                CodeGenError::GeneratedBadCode(format!(
                    "missing claim var map entry for x{}",
                    var_id
                ))
            })?;

            if var_type.as_ref().is_type_param_kind() {
                let type_param_name = format!("T{}", var_id);
                let kind = normalizer.denormalize_type_with_context(var_type, local_context, false);
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

                let concrete_type = normalizer.denormalize_type_with_context(
                    arg_term.clone(),
                    local_context,
                    false,
                );
                type_arg_codes.push(generator.type_to_expr(&concrete_type)?.to_string());
                continue;
            }

            let var_name = bindings.next_indexed_var('x', &mut next_value_decl_id);
            let acorn_type =
                normalizer.denormalize_type_with_context(var_type, local_context, false);
            let type_code = generator.type_to_expr(&acorn_type)?.to_string();
            value_decl_codes.push(format!("{}: {}", var_name, type_code));

            let arg_value =
                normalizer.denormalize_term_with_context(arg_term, local_context, false);
            let arg_code = if let Some(synthetic_names) = synthetic_names {
                generator.value_to_code_with_synthetic_names(&arg_value, synthetic_names)?
            } else {
                generator.value_to_code(&arg_value)?
            };
            value_arg_codes.push(Self::dequalify_synthetic_name_refs(
                arg_code,
                synthetic_names,
            ));
        }

        if value_decl_codes.is_empty() {
            if type_param_decl_codes.is_empty() {
                let specialized = claim
                    .var_map
                    .specialize_clause(&claim.clause, kernel_context);
                let specialized_value = normalizer.denormalize(&specialized, None, None, true);
                return if let Some(synthetic_names) = synthetic_names {
                    generator
                        .value_to_code_with_synthetic_names(&specialized_value, synthetic_names)
                        .map(|code| {
                            Self::dequalify_synthetic_name_refs(code, Some(synthetic_names))
                        })
                } else {
                    generator.value_to_code(&specialized_value)
                };
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

    /// Deserializes a claim produced by `serialize_claim_with_args`.
    ///
    /// This is currently a standalone helper and is not wired into normal certificate
    /// parsing.
    pub fn deserialize_claim_with_args(
        code: &str,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) -> Result<Claim, CodeGenError> {
        let statement = Statement::parse_str_with_options(code, true)?;
        let StatementInfo::Claim(claim_statement) = statement.statement else {
            return Err(CodeGenError::GeneratedBadCode(
                "expected a claim expression".to_string(),
            ));
        };

        let mut evaluator = Evaluator::new(project, bindings, None);
        let evaluated = evaluator.evaluate_value(&claim_statement.claim, Some(&AcornType::Bool))?;
        Self::try_deserialize_claim_with_args_value(evaluated, bindings, normalizer)?.ok_or_else(
            || {
                CodeGenError::GeneratedBadCode(
                    "expected a function(...) { ... }(...) claim shape".to_string(),
                )
            },
        )
    }

    fn try_deserialize_claim_with_args_value(
        value: AcornValue,
        bindings: &BindingMap,
        normalizer: &Normalizer,
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

        let mut normalizer_clone = normalizer.clone();
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
                    let typeclass_id = normalizer_clone
                        .kernel_context_mut()
                        .type_store
                        .add_typeclass(typeclass);
                    Term::typeclass(typeclass_id)
                } else {
                    Term::type_sort()
                };
                map.insert(name.clone(), (i as AtomId, var_type));
            }
            Some(map)
        };
        let mut view = NormalizationContext::new_mut(
            &mut normalizer_clone,
            type_var_map,
            bindings.module_id(),
        );
        let generic_value = AcornValue::forall(arg_types, body);
        let clauses = view.value_to_denormalized_clauses(&generic_value)?;
        if clauses.len() != 1 {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "claim-with-args body normalized to {} clauses (expected 1)",
                clauses.len()
            )));
        }
        let clause = clauses
            .into_iter()
            .next()
            .expect("clauses has exactly one element");

        let term_view = NormalizationContext::new_ref(normalizer, None);
        let mut var_map = VariableMap::new();
        for (var_id, acorn_type) in type_args.iter().enumerate() {
            let type_term = normalizer
                .kernel_context()
                .type_store
                .to_type_term_with_vars(acorn_type, None);
            var_map.set(var_id as AtomId, type_term);
        }
        let value_offset = var_map.len();
        for (var_id, arg) in args.iter().enumerate() {
            let term = term_view.value_to_simple_term(arg)?;
            var_map.set((value_offset + var_id) as AtomId, term);
        }

        Ok(Some(Claim { clause, var_map }))
    }

    /// Check this certificate. It is expected that it has a proof.
    ///
    /// Consumes checker/bindings/normalizer since checking mutates all three.
    pub fn check(
        &self,
        mut checker: Checker,
        project: &Project,
        mut bindings: Cow<BindingMap>,
        mut normalizer: Cow<Normalizer>,
    ) -> Result<Vec<CertificateLine>, CodeGenError> {
        if checker.has_contradiction() {
            return Ok(Vec::new());
        }
        let Some(proof) = &self.proof else {
            return Err(CodeGenError::NoProof);
        };
        let cert_steps = Self::parse_cert_steps(proof, project, &mut bindings, &mut normalizer)?;
        let checked_steps = checker.check_cert_steps(&cert_steps, Some(proof), &normalizer)?;
        Ok(checked_steps
            .into_iter()
            .map(|checked_step| CertificateLine {
                statement: clause_to_code(&checked_step.clause, &normalizer, &bindings),
                reason: checked_step.reason,
            })
            .collect())
    }

    /// Remove unneeded steps from this certificate.
    pub fn clean(
        self,
        checker: Checker,
        project: &Project,
        bindings: Cow<BindingMap>,
        normalizer: Cow<Normalizer>,
    ) -> Result<(Certificate, Vec<CertificateLine>), CodeGenError> {
        let mut good_cert = self;
        let mut keep_count = 0;

        loop {
            let Some(proof) = &good_cert.proof else {
                return Err(CodeGenError::NoProof);
            };

            if keep_count >= proof.len() {
                let steps = good_cert.check(checker, project, bindings, normalizer)?;
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
                normalizer.clone(),
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

    fn setup_claim_codec_env(code: &str) -> (Project, BindingMap, Normalizer) {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", code);

        let module_id = project
            .load_module_by_name("main")
            .expect("module should load");
        let (bindings, normalizer) = {
            let env = match project.get_module_by_id(module_id) {
                LoadState::Ok(env) => env,
                LoadState::Error(e) => panic!("module loading error: {}", e),
                _ => panic!("unexpected module load state"),
            };
            let normalizer = env
                .normalizer
                .clone()
                .expect("environment should have a normalizer");
            (env.bindings.clone(), normalizer)
        };

        (project, bindings, normalizer)
    }

    #[test]
    fn test_claim_with_args_roundtrip_single_argument() {
        let code = r#"
            theorem goal {
                true = true
            }
        "#;
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let clause = kernel.parse_clause("x0 = true", &["Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_true());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect("serialization should succeed");
        assert_eq!(serialized, "function(x0: Bool) { x0 }(true)");

        let roundtrip =
            Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &normalizer)
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
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let clause = kernel.parse_clause("x0 = x1 or x0 = true", &["Bool", "Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_false());
        var_map.set(1, Term::new_true());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect("serialization should succeed");
        let roundtrip =
            Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &normalizer)
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
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let clause = kernel.parse_clause("x0", &["Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_false());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect("serialization should succeed");
        let roundtrip =
            Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &normalizer)
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
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let clause = kernel.parse_clause("x1 = x1", &["Type", "x0"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::bool_type());
        var_map.set(1, Term::new_true());
        let claim = Claim {
            clause: clause.clone(),
            var_map: var_map.clone(),
        };

        let serialized = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect("serialization with type locals should succeed");
        assert_eq!(serialized, "function[T0](x0: T0) { x0 = x0 }[Bool](true)");

        let parsed =
            Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &normalizer)
                .expect("deserialization should succeed");
        assert_eq!(parsed, claim);
    }

    #[test]
    fn test_serialize_claim_with_args_rejects_missing_mapping() {
        let code = r#"
            theorem goal {
                true = false
            }
        "#;
        let (_project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let clause = kernel.parse_clause("x0 = x1", &["Bool", "Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_true());
        let claim = Claim { clause, var_map };

        let err = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect_err("missing mapping should be rejected");
        let msg = err.to_string();
        assert!(msg.contains("missing claim var map entry"));
    }

    #[test]
    fn test_deserialize_claim_with_args_rejects_non_function_shape() {
        let code = r#"
            let bar: Bool -> Bool = axiom

            theorem goal {
                bar(true)
            }
        "#;
        let (project, bindings, normalizer) = setup_claim_codec_env(code);

        let err =
            Certificate::deserialize_claim_with_args("bar(true)", &project, &bindings, &normalizer)
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
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let mut expected_var_map = VariableMap::new();
        expected_var_map.set(0, Term::new_false());
        let expected = Claim {
            clause: kernel.parse_clause("x0", &["Bool"]),
            var_map: expected_var_map,
        };

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut normalizer_cow = Cow::Borrowed(&normalizer);
        let step = Certificate::parse_code_line(
            "function(x0: Bool) { x0 }(false)",
            &project,
            &mut bindings_cow,
            &mut normalizer_cow,
        )
        .expect("claim-with-args parsing should succeed");

        match step {
            CertificateStep::Claim(claim) => assert_eq!(claim, expected),
            _ => panic!("expected claim step"),
        }
    }

    #[test]
    fn test_parse_code_line_accepts_claim_with_type_args_shape() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let mut expected_var_map = VariableMap::new();
        expected_var_map.set(0, Term::bool_type());
        expected_var_map.set(1, Term::new_true());
        let expected = Claim {
            clause: kernel.parse_clause("x1 = x1", &["Type", "x0"]),
            var_map: expected_var_map,
        };

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut normalizer_cow = Cow::Borrowed(&normalizer);
        let step = Certificate::parse_code_line(
            "function[T0](x0: T0) { x0 = x0 }[Bool](true)",
            &project,
            &mut bindings_cow,
            &mut normalizer_cow,
        )
        .expect("claim-with-type-args parsing should succeed");

        match step {
            CertificateStep::Claim(claim) => assert_eq!(claim, expected),
            _ => panic!("expected claim step"),
        }
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_parse_code_line_accepts_claim_with_type_args_only_shape() {
        let code = r#"
            let foo[T]: Bool = axiom

            theorem goal {
                foo[Bool]
            }
        "#;
        let (project, bindings, normalizer) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut normalizer_cow = Cow::Borrowed(&normalizer);
        let step = Certificate::parse_code_line(
            "function[T0] { foo[T0] }[Bool]",
            &project,
            &mut bindings_cow,
            &mut normalizer_cow,
        )
        .expect("type-only claim-with-args parsing should succeed");

        let claim = match step {
            CertificateStep::Claim(claim) => claim,
            _ => panic!("expected claim step"),
        };
        assert!(claim.var_map.len() > 0);

        let serialized = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect("serialization should succeed");
        let roundtrip =
            Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &normalizer)
                .expect("deserialization should succeed");
        assert_eq!(roundtrip, claim);
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_serialize_claim_with_args_avoids_colliding_lambda_arg_names() {
        let code = r#"
            let x0: Bool = axiom
            let x1: Bool = axiom

            theorem goal {
                true
            }
        "#;
        let (project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();

        let clause = kernel.parse_clause("x0 or x1 or x2", &["Bool", "Bool", "Bool"]);
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_true());
        var_map.set(1, Term::new_false());
        var_map.set(2, Term::new_true());
        let claim = Claim { clause, var_map };

        let serialized = Certificate::serialize_claim_with_args(&claim, &normalizer, &bindings)
            .expect("serialization should succeed");
        assert!(!serialized.contains("function(x0: Bool"));

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut normalizer_cow = Cow::Borrowed(&normalizer);
        let parsed = Certificate::parse_code_line(
            &serialized,
            &project,
            &mut bindings_cow,
            &mut normalizer_cow,
        )
        .expect("serialized line should parse even when x0/x1 are already bound");

        match parsed {
            CertificateStep::Claim(roundtrip_claim) => assert_eq!(roundtrip_claim, claim),
            _ => panic!("expected claim step"),
        }
    }

    #[test]
    fn test_parse_code_line_plain_claim_still_works() {
        let code = r#"
            let bar: Bool -> Bool = axiom

            theorem goal {
                bar(true)
            }
        "#;
        let (project, bindings, normalizer) = setup_claim_codec_env(code);

        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut normalizer_cow = Cow::Borrowed(&normalizer);
        let step = Certificate::parse_code_line(
            "bar(true)",
            &project,
            &mut bindings_cow,
            &mut normalizer_cow,
        )
        .expect("plain claim parsing should succeed");

        match step {
            CertificateStep::Claim(claim) => assert_eq!(claim.var_map.len(), 0),
            _ => panic!("expected claim step"),
        }
    }

    #[cfg(not(feature = "bigcert"))]
    #[test]
    fn test_from_concrete_steps_uses_legacy_claim_serialization_without_bigcert() {
        let code = r#"
            theorem goal {
                false = false
            }
        "#;
        let (_project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();
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
            &normalizer,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "false");
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_from_concrete_steps_uses_bigcert_claim_serialization() {
        let code = r#"
            theorem goal {
                false = false
            }
        "#;
        let (_project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();
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
            &normalizer,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "function(x0: Bool) { x0 }(false)");
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_from_concrete_steps_bigcert_falls_back_to_plain_claim_when_no_args() {
        let code = r#"
            theorem goal {
                false
            }
        "#;
        let (_project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();
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
            &normalizer,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "false");
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_from_concrete_steps_bigcert_infers_type_arg_from_value_mapping() {
        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (_project, bindings, normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();
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
            &normalizer,
            &bindings,
        )
        .expect("certificate generation should succeed");
        let proof = cert.proof.expect("proof should exist");
        assert_eq!(proof.len(), 1);
        assert_eq!(proof[0], "function[T0](x0: T0) { x0 = x0 }[Bool](true)");
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_serialize_claim_with_names_uses_local_name_for_replaced_synthetic_args() {
        use crate::kernel::atom::Atom;
        use crate::module::ModuleId;

        let code = r#"
            theorem goal {
                true
            }
        "#;
        let (_project, bindings, mut normalizer) = setup_claim_codec_env(code);
        let kernel = normalizer.kernel_context();
        let clause = kernel.parse_clause("x0", &["Bool"]);

        let synthetic_symbol = normalizer
            .kernel_context_mut()
            .symbol_table
            .declare_synthetic(ModuleId(7), Term::bool_type());
        let synthetic_term = Term::atom(Atom::Symbol(synthetic_symbol));

        let mut var_map = VariableMap::new();
        var_map.set(0, synthetic_term);
        let claim = Claim { clause, var_map };

        let mut synthetic_names = HashMap::new();
        synthetic_names.insert((ModuleId(7), 0), "s0".to_string());

        let serialized = Certificate::serialize_claim_with_names(
            &claim,
            &normalizer,
            &bindings,
            Some(&synthetic_names),
        )
        .expect("serialization should succeed");

        assert_eq!(serialized, "function(x0: Bool) { x0 }(s0)");

        // Ensure the replacement name itself does not need to resolve through lib(module).
        assert!(!serialized.contains("lib("));
    }

    #[test]
    fn test_dequalify_synthetic_name_refs_rewrites_module_qualified_calls() {
        use crate::module::ModuleId;

        let mut synthetic_names = HashMap::new();
        synthetic_names.insert((ModuleId(7), 0), "s0".to_string());
        let code =
            "function(x0: Nat) { not f(x0) or f(x0.suc) }(lib(nat.nat_base).s0(f))".to_string();

        let normalized = Certificate::dequalify_synthetic_name_refs(code, Some(&synthetic_names));

        assert_eq!(
            normalized,
            "function(x0: Nat) { not f(x0) or f(x0.suc) }(s0(f))"
        );
        assert!(!normalized.contains("lib(nat.nat_base).s0"));
    }
}
