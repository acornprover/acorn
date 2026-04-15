use std::borrow::Cow;
use std::collections::HashSet;

use crate::builder::BuildError;
use crate::certificate::{Certificate, CertificateLine, CheckedCertificate};
use crate::code_generator::Error;
use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::lowering::{LoweredFact, LoweredGoal};
use crate::elaborator::node::NodeCursor;
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::proof_step::Rule;
use crate::module::ModuleId;
use crate::project::Project;
use crate::prover::{Outcome, Prover, ProverMode};
use tokio_util::sync::CancellationToken;

/// The processor represents what we do with a stream of facts.
#[derive(Clone)]
pub struct Processor {
    prover: Option<Prover>,
    checker: Checker,
    imported_modules: HashSet<ModuleId>,
}

impl Processor {
    fn new_with_optional_prover(
        cancellation_token: Option<CancellationToken>,
        prover: bool,
    ) -> Processor {
        Processor {
            prover: prover.then(|| match cancellation_token {
                Some(token) => Prover::new(vec![token]),
                None => Prover::new(vec![]),
            }),
            checker: Checker::new(),
            imported_modules: HashSet::new(),
        }
    }

    pub(crate) fn bindings_with_type_params<'a>(
        bindings: &'a BindingMap,
        type_params: &[TypeParam],
    ) -> Cow<'a, BindingMap> {
        if type_params.is_empty() {
            return Cow::Borrowed(bindings);
        }

        let missing_params: Vec<TypeParam> = type_params
            .iter()
            .filter(|param| !bindings.has_typename(&param.name))
            .cloned()
            .collect();
        if missing_params.is_empty() {
            return Cow::Borrowed(bindings);
        }

        let mut extended = bindings.clone();
        for param in missing_params {
            extended.add_arbitrary_type(param);
        }
        Cow::Owned(extended)
    }

    pub fn new() -> Processor {
        Self::new_with_optional_prover(None, true)
    }

    pub fn with_token(cancellation_token: CancellationToken) -> Processor {
        Self::new_with_optional_prover(Some(cancellation_token), true)
    }

    /// Creates a new Processor with the imports visible through these bindings.
    pub fn with_imports(
        cancellation_token: Option<CancellationToken>,
        bindings: &BindingMap,
        project: &Project,
    ) -> Result<Processor, BuildError> {
        let mut processor = Self::new_with_optional_prover(cancellation_token, true);
        processor.add_imports_from_bindings(bindings, project)?;
        Ok(processor)
    }

    /// Creates a new Processor for certificate checking only.
    pub fn with_imports_for_checking(
        cancellation_token: Option<CancellationToken>,
        bindings: &BindingMap,
        project: &Project,
    ) -> Result<Processor, BuildError> {
        let mut processor = Self::new_with_optional_prover(cancellation_token, false);
        processor.add_imports_from_bindings(bindings, project)?;
        Ok(processor)
    }

    pub fn add_imports_from_bindings(
        &mut self,
        bindings: &BindingMap,
        project: &Project,
    ) -> Result<(), BuildError> {
        if self.has_imports_for_bindings(bindings) {
            return Ok(());
        }

        for dep_id in bindings.direct_dependencies() {
            for module_id in project
                .all_dependencies(dep_id)
                .into_iter()
                .chain(std::iter::once(dep_id))
            {
                self.add_imported_module(project, module_id)?;
            }
        }
        Ok(())
    }

    pub fn has_imports_for_bindings(&self, bindings: &BindingMap) -> bool {
        bindings
            .direct_dependencies()
            .into_iter()
            .all(|dep_id| self.imported_modules.contains(&dep_id))
    }

    fn add_imported_module(
        &mut self,
        project: &Project,
        module_id: ModuleId,
    ) -> Result<(), BuildError> {
        if !self.imported_modules.insert(module_id) {
            return Ok(());
        }
        let dep_env = project.get_env_by_id(module_id).ok_or_else(|| {
            BuildError::new(
                Default::default(),
                format!("missing dependency {}", module_id.0),
            )
        })?;
        for normalized in &dep_env.lowered_module_facts {
            self.add_lowered_fact(normalized)?;
        }
        Ok(())
    }

    /// Adds all module-local facts that are usable at the given cursor position.
    pub fn add_module_facts(&mut self, cursor: &NodeCursor) -> Result<(), BuildError> {
        let facts = cursor
            .visible_lowered_facts()
            .map_err(|message| BuildError::new(Default::default(), message))?;
        for normalized in facts {
            self.add_lowered_fact(normalized)?;
        }
        Ok(())
    }

    pub fn prover(&self) -> &Prover {
        self.prover
            .as_ref()
            .expect("processor was created without prover support")
    }
    pub fn checker(&self) -> &Checker {
        &self.checker
    }

    /// Adds a lowered fact to the prover.
    pub fn add_lowered_fact(&mut self, normalized: &LoweredFact) -> Result<(), BuildError> {
        let kernel_context = &normalized.kernel_context;
        for step in &normalized.steps {
            // Extract the source from the step's rule.
            let step_source = match &step.rule {
                Rule::Assumption(info) => info.source.clone(),
                _ => {
                    return Err(BuildError::new(
                        Default::default(),
                        format!(
                            "Expected assumption step from lower_fact, got: {:?}",
                            step.rule
                        ),
                    ));
                }
            };
            self.checker.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source),
                kernel_context,
            );
        }
        if let Some(prover) = self.prover.as_mut() {
            prover.add_steps(normalized.steps.clone(), kernel_context);
        }
        Ok(())
    }

    /// Sets a lowered goal as the prover's goal.
    pub fn set_lowered_goal(&mut self, normalized: &LoweredGoal) {
        let source = &normalized.goal.proposition.source;
        let kernel_context = &normalized.kernel_context;
        for step in &normalized.steps {
            // Use the step's own source if it's an assumption (which includes negated goals),
            // otherwise use the goal's source
            let step_source = if let Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.checker.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source.clone()),
                kernel_context,
            );
        }
        if let Some(prover) = self.prover.as_mut() {
            prover.set_goal(
                normalized.goal.clone(),
                normalized.steps.clone(),
                kernel_context,
            );
        }
    }

    /// Forwards a search request to the underlying prover.
    pub fn search(&mut self, mode: ProverMode, kernel_context: &KernelContext) -> Outcome {
        self.prover
            .as_mut()
            .expect("processor was created without prover support")
            .search(mode, kernel_context)
    }

    /// Creates a certificate from the current proof state.
    pub fn make_cert(
        &self,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
        print: bool,
    ) -> Result<Certificate, Error> {
        self.prover
            .as_ref()
            .expect("processor was created without prover support")
            .make_cert(bindings, kernel_context, print)
    }

    /// Checks a certificate.
    /// Clones the checker and kernel_context, because the checking process despoils them.
    /// If the goal is provided, it is added to the checker before checking the certificate.
    /// Returns a list of CertificateLines showing how each line was verified.
    pub fn check_cert(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<Vec<CertificateLine>, Error> {
        Ok(self
            .check_cert_with_usage(cert, normalized_goal, kernel_context, project, bindings)?
            .lines)
    }

    #[cfg(feature = "validate")]
    pub fn check_generated_cert(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<Vec<CertificateLine>, Error> {
        Ok(self
            .check_generated_cert_with_usage(
                cert,
                normalized_goal,
                kernel_context,
                project,
                bindings,
            )?
            .lines)
    }

    /// Checks a certificate and reports how many proof lines were consumed.
    pub fn check_cert_with_usage(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<CheckedCertificate, Error> {
        self.check_cert_with_usage_internal(
            cert,
            normalized_goal,
            kernel_context,
            project,
            bindings,
            false,
        )
    }

    fn check_cert_with_usage_internal(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: &Project,
        bindings: &BindingMap,
        #[cfg_attr(not(feature = "validate"), allow(unused_variables))] validate_generated: bool,
    ) -> Result<CheckedCertificate, Error> {
        let mut checker = self.checker.clone();
        let mut cert_bindings = Cow::Borrowed(bindings);
        let effective_kernel_context: &KernelContext;

        if let Some(normalized_goal) = normalized_goal {
            checker.insert_lowered_goal(normalized_goal)?;
            cert_bindings =
                Self::bindings_with_type_params(bindings, &normalized_goal.goal.proposition.params);
            effective_kernel_context = &normalized_goal.kernel_context;
        } else if let Some(type_params) = self
            .prover
            .as_ref()
            .and_then(|prover| prover.goal_type_params())
        {
            cert_bindings = Self::bindings_with_type_params(bindings, type_params);
            effective_kernel_context = kernel_context;
        } else {
            effective_kernel_context = kernel_context;
        }

        let kernel_context = Cow::Owned(effective_kernel_context.clone());
        #[cfg(feature = "validate")]
        if validate_generated {
            return cert.check_generated_with_usage(
                checker,
                project,
                cert_bindings,
                kernel_context,
            );
        }

        cert.check_with_usage(checker, project, cert_bindings, kernel_context)
    }

    #[cfg(feature = "validate")]
    pub fn check_generated_cert_with_usage(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<CheckedCertificate, Error> {
        self.check_cert_with_usage_internal(
            cert,
            normalized_goal,
            kernel_context,
            project,
            bindings,
            true,
        )
    }

    /// Cleans a certificate by removing unnecessary steps.
    /// Similar to check_cert but returns the cleaned certificate along with the steps.
    pub fn clean_cert(
        &self,
        cert: Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<(Certificate, Vec<CertificateLine>), Error> {
        let mut checker = self.checker.clone();
        let mut cert_bindings = Cow::Borrowed(bindings);
        let effective_kernel_context: &KernelContext;

        if let Some(normalized_goal) = normalized_goal {
            checker.insert_lowered_goal(normalized_goal)?;
            cert_bindings =
                Self::bindings_with_type_params(bindings, &normalized_goal.goal.proposition.params);
            effective_kernel_context = &normalized_goal.kernel_context;
        } else if let Some(type_params) = self
            .prover
            .as_ref()
            .and_then(|prover| prover.goal_type_params())
        {
            cert_bindings = Self::bindings_with_type_params(bindings, type_params);
            effective_kernel_context = kernel_context;
        } else {
            effective_kernel_context = kernel_context;
        }

        let kernel_context = Cow::Owned(effective_kernel_context.clone());
        cert.clean(checker, project, cert_bindings, kernel_context)
    }

    /// Creates a test Processor from code containing a theorem named "goal".
    /// Loads facts and sets up the goal, which triggers normalization.
    /// Returns the Processor and the goal-level BindingMap.
    #[cfg(test)]
    pub fn test_goal(code: &str) -> (Processor, BindingMap, LoweredGoal) {
        use crate::module::LoadState;

        let mut p = Project::new_mock();
        p.mock("/mock/main.ac", code);

        let module_id = p.load_module_by_name("main").expect("load failed");
        let env = match p.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("error: {}", e),
            _ => panic!("no module"),
        };

        let cursor = env.get_node_by_goal_name("goal");
        let mut processor = Processor::with_imports(None, cursor.bindings(), &p).unwrap();
        processor.add_module_facts(&cursor).unwrap();
        let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
        processor.set_lowered_goal(normalized_goal);

        (
            processor,
            cursor.bindings().clone(),
            normalized_goal.clone(),
        )
    }

    /// Test helper: verify a line of certificate code can be parsed.
    /// Panics if parsing fails.
    #[cfg(test)]
    pub fn test_parse_code(
        &self,
        code: &str,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
    ) {
        use std::borrow::Cow;

        let mut kernel_context_cow = Cow::Owned(kernel_context.clone());
        let mut bindings_cow = Cow::Borrowed(bindings);
        let project = Project::new_mock();

        Certificate::parse_code_line(code, &project, &mut bindings_cow, &mut kernel_context_cow)
            .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::LoadState;

    #[test]
    fn check_only_processor_can_verify_a_generated_certificate() {
        let mut project = Project::new_mock();
        project.mock(
            "/mock/main.ac",
            r#"
            theorem goal {
                true
            }
            "#,
        );

        let module_id = project.load_module_by_name("main").expect("load failed");
        let env = match project.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("error: {}", e),
            _ => panic!("no module"),
        };

        let cursor = env.get_node_by_goal_name("goal");
        let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
        let goal_kernel_context = &normalized_goal.kernel_context;

        let mut proving = Processor::with_imports(None, cursor.bindings(), &project)
            .expect("proving processor creation failed");
        proving.add_module_facts(&cursor).unwrap();
        proving.set_lowered_goal(normalized_goal);
        let outcome = proving.search(ProverMode::Test, goal_kernel_context);
        assert_eq!(outcome, Outcome::Success);
        let cert = proving
            .make_cert(cursor.bindings(), goal_kernel_context, false)
            .expect("certificate generation failed");

        let mut checking = Processor::with_imports_for_checking(None, cursor.bindings(), &project)
            .expect("checking processor creation failed");
        checking.add_module_facts(&cursor).unwrap();
        checking
            .check_cert(
                &cert,
                Some(normalized_goal),
                goal_kernel_context,
                &project,
                cursor.bindings(),
            )
            .expect("certificate verification failed");
    }
}
