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
use crate::kernel::certificate_step::CertificateStep;
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::term::Term;
use crate::kernel::variable_map::VariableMap;
use crate::module::ModuleDescriptor;
use crate::normalizer::{NormalizationContext, Normalizer};
use crate::project::Project;
use crate::prover::proof::ConcreteStep;
use crate::syntax::expression::Declaration;
use crate::syntax::statement::{Statement, StatementInfo};

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
        let mut ordered_steps = Vec::new();

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
            answer.push(generator.certificate_step_to_code(
                &names,
                step,
                &generation_normalizer,
            )?);
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
                let module_id = bindings.module_id();
                let mut view = NormalizationContext::new_mut(normalizer.to_mut(), None, module_id);
                let clauses = view.value_to_denormalized_clauses(&value)?;
                if clauses.len() != 1 {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "claim must normalize to exactly one clause, got {}",
                        clauses.len()
                    )));
                }
                Ok(CertificateStep::Claim(
                    clauses
                        .into_iter()
                        .next()
                        .expect("clauses has exactly one element"),
                ))
            }
            _ => Err(CodeGenError::GeneratedBadCode(format!(
                "Expected a claim or let...satisfy statement, got: {}",
                code
            ))),
        }
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
        let checked_steps = checker.check_cert_steps(&cert_steps, &normalizer)?;
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
}
