use std::borrow::Cow;
use std::collections::HashSet;

use crate::builder::BuildError;
use crate::certificate::{Certificate, CertificateLine, CheckedCertificate};
use crate::code_generator::Error;
use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::lowered_module::{
    CheckExportFact, ExportedFact, LoweredGoalId, LoweredModule,
};
use crate::elaborator::lowering::{LoweredFact, LoweredGoal};
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::proof_step::Rule;
use crate::module::ModuleId;
use crate::project::ProjectView;
use crate::prover::trace::{TraceActivatedStepRecord, TraceSearchMeta};
use crate::prover::{Outcome, Prover, ProverMode, ScoringConfig, ScoringPolicy, SearchStats};
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
        scoring_config: ScoringConfig,
    ) -> Processor {
        Processor {
            prover: prover.then(|| match cancellation_token {
                Some(token) => Prover::with_config(vec![token], scoring_config),
                None => Prover::with_config(vec![], scoring_config),
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
        Self::new_with_optional_prover(None, true, ScoringConfig::default())
    }

    pub fn with_token(cancellation_token: CancellationToken) -> Processor {
        Self::new_with_optional_prover(Some(cancellation_token), true, ScoringConfig::default())
    }

    /// Creates a new Processor with the imports visible through these bindings.
    pub fn with_imports(
        cancellation_token: Option<CancellationToken>,
        bindings: &BindingMap,
        project: impl Into<ProjectView>,
    ) -> Result<Processor, BuildError> {
        Self::with_imports_and_scoring_config(
            cancellation_token,
            bindings,
            project,
            ScoringConfig::default(),
        )
    }

    pub fn with_imports_and_policy(
        cancellation_token: Option<CancellationToken>,
        bindings: &BindingMap,
        project: impl Into<ProjectView>,
        scoring_policy: ScoringPolicy,
    ) -> Result<Processor, BuildError> {
        Self::with_imports_and_scoring_config(
            cancellation_token,
            bindings,
            project,
            ScoringConfig::new(scoring_policy),
        )
    }

    pub fn with_imports_and_scoring_config(
        cancellation_token: Option<CancellationToken>,
        bindings: &BindingMap,
        project: impl Into<ProjectView>,
        scoring_config: ScoringConfig,
    ) -> Result<Processor, BuildError> {
        let mut processor =
            Self::new_with_optional_prover(cancellation_token, true, scoring_config);
        processor.checker.set_eager_boolean_reductions(false);
        processor.add_imports_from_bindings(bindings, project)?;
        Ok(processor)
    }

    /// Creates a new Processor for certificate checking only.
    pub fn with_imports_for_checking(
        cancellation_token: Option<CancellationToken>,
        bindings: &BindingMap,
        project: impl Into<ProjectView>,
    ) -> Result<Processor, BuildError> {
        let mut processor =
            Self::new_with_optional_prover(cancellation_token, false, ScoringConfig::default());
        processor.checker.set_eager_boolean_reductions(false);
        processor.add_imports_from_bindings(bindings, project)?;
        Ok(processor)
    }

    pub fn add_imports_from_bindings(
        &mut self,
        bindings: &BindingMap,
        project: impl Into<ProjectView>,
    ) -> Result<(), BuildError> {
        let project = project.into();
        if self.has_imports_for_bindings(bindings) {
            return Ok(());
        }

        for dep_id in bindings.direct_dependencies() {
            for module_id in project
                .all_dependencies(dep_id)
                .into_iter()
                .chain(std::iter::once(dep_id))
            {
                self.add_imported_module(&project, module_id)?;
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
        project: &ProjectView,
        module_id: ModuleId,
    ) -> Result<(), BuildError> {
        if !self.imported_modules.insert(module_id) {
            return Ok(());
        }
        let export = project.get_module_export(module_id).ok_or_else(|| {
            BuildError::new(
                Default::default(),
                format!("missing dependency {}", module_id.0),
            )
        })?;
        for fact in export.facts() {
            self.add_exported_fact(fact)?;
        }
        Ok(())
    }

    /// Adds all module-local facts that are usable at the given lowered goal.
    pub fn add_visible_module_facts(
        &mut self,
        lowered: &LoweredModule,
        goal: LoweredGoalId,
    ) -> Result<(), BuildError> {
        let facts = lowered.visible_facts_for_goal(goal).ok_or_else(|| {
            BuildError::new(Default::default(), "lowered goal not found".to_string())
        })?;
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

    fn add_check_export_fact(&mut self, fact: &CheckExportFact) -> Result<(), BuildError> {
        if self.prover.is_some() {
            return Err(BuildError::new(
                Default::default(),
                "check-only module export cannot be used by a prover".to_string(),
            ));
        }
        for assumption in &fact.assumptions {
            self.checker.insert_normalized_clause(
                &assumption.clause,
                StepReason::Assumption(assumption.source.clone()),
                &fact.kernel_context,
            );
        }
        Ok(())
    }

    pub fn add_exported_fact(&mut self, fact: &ExportedFact) -> Result<(), BuildError> {
        match fact {
            ExportedFact::Check(fact) => self.add_check_export_fact(fact),
            ExportedFact::Prove(fact) => self.add_lowered_fact(fact),
        }
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

    pub fn last_search_stats(&self) -> Option<&SearchStats> {
        self.prover.as_ref()?.last_search_stats()
    }

    pub fn set_search_trace_enabled(&mut self, enabled: bool) {
        if let Some(prover) = self.prover.as_mut() {
            prover.set_trace_enabled(enabled);
        }
    }

    pub fn search_trace_records(
        &self,
        meta: TraceSearchMeta,
        outcome: Outcome,
    ) -> Option<Vec<TraceActivatedStepRecord>> {
        self.prover.as_ref()?.trace_records(meta, outcome)
    }

    /// Creates a certificate from the current proof state.
    pub fn make_cert(
        &self,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
        project: impl Into<ProjectView>,
        normalized_goal: Option<&LoweredGoal>,
        print: bool,
    ) -> Result<Certificate, Error> {
        let project = project.into();
        let checker = self.checker.clone();
        let mut cert_bindings = Cow::Borrowed(bindings);

        if let Some(normalized_goal) = normalized_goal {
            cert_bindings =
                Self::bindings_with_type_params(bindings, &normalized_goal.goal.proposition.params);
        } else if let Some(prover_type_params) = self
            .prover
            .as_ref()
            .and_then(|prover| prover.goal_type_params())
        {
            cert_bindings = Self::bindings_with_type_params(bindings, prover_type_params);
        }

        self.prover
            .as_ref()
            .expect("processor was created without prover support")
            .make_certificate(
                bindings,
                kernel_context,
                print,
                checker,
                &project,
                cert_bindings,
            )
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
        project: impl Into<ProjectView>,
        bindings: &BindingMap,
    ) -> Result<Vec<CertificateLine>, Error> {
        Ok(self
            .check_cert_with_usage_internal(
                cert,
                normalized_goal,
                kernel_context,
                project,
                bindings,
                true,
            )?
            .lines)
    }

    /// Checks a certificate and reports how many proof steps were consumed.
    ///
    /// This hot path does not materialize display-oriented `CertificateLine`s.
    pub fn check_cert_with_usage(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&LoweredGoal>,
        kernel_context: &KernelContext,
        project: impl Into<ProjectView>,
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
        project: impl Into<ProjectView>,
        bindings: &BindingMap,
        collect_lines: bool,
    ) -> Result<CheckedCertificate, Error> {
        let project = project.into();
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
        if collect_lines {
            cert.check_with_usage(checker, &project, cert_bindings, kernel_context)
        } else {
            cert.check_usage_only(checker, &project, cert_bindings, kernel_context)
        }
    }

    /// Creates a test Processor from code containing a theorem named "goal".
    /// Loads facts and sets up the goal, which triggers normalization.
    /// Returns the Processor and the goal-level BindingMap.
    #[cfg(test)]
    pub fn test_goal(code: &str) -> (Processor, BindingMap, LoweredGoal) {
        let mut p = crate::project::Project::new_mock();
        p.mock("/mock/main.ac", code);

        let module_id = p.load_module_by_name("main").expect("load failed");
        let lowered = p
            .get_lowered_module(module_id)
            .expect("missing lowered module");
        let (goal_id, entry) = lowered.goal_by_name("goal").expect("missing lowered goal");
        let mut processor = Processor::with_imports(None, &entry.bindings, &p).unwrap();
        processor
            .add_visible_module_facts(lowered, goal_id)
            .unwrap();
        processor.set_lowered_goal(&entry.lowered_goal);

        (
            processor,
            entry.bindings.clone(),
            entry.lowered_goal.clone(),
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
        let project = crate::project::Project::new_mock();

        Certificate::parse_code_line(code, &project, &mut bindings_cow, &mut kernel_context_cow)
            .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::Project;

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
        let lowered = project
            .get_lowered_module(module_id)
            .expect("missing lowered module");
        let (goal_id, entry) = lowered.goal_by_name("goal").expect("missing lowered goal");
        let normalized_goal = &entry.lowered_goal;
        let bindings = &entry.bindings;
        let goal_kernel_context = &normalized_goal.kernel_context;

        let mut proving = Processor::with_imports(None, bindings, &project)
            .expect("proving processor creation failed");
        proving.add_visible_module_facts(lowered, goal_id).unwrap();
        proving.set_lowered_goal(normalized_goal);
        let outcome = proving.search(ProverMode::Test, goal_kernel_context);
        assert_eq!(outcome, Outcome::Success);
        let cert = proving
            .make_cert(
                bindings,
                goal_kernel_context,
                &project,
                Some(normalized_goal),
                false,
            )
            .expect("certificate generation failed");

        let mut checking = Processor::with_imports_for_checking(None, bindings, &project)
            .expect("checking processor creation failed");
        checking.add_visible_module_facts(lowered, goal_id).unwrap();
        checking
            .check_cert(
                &cert,
                Some(normalized_goal),
                goal_kernel_context,
                &project,
                bindings,
            )
            .expect("certificate verification failed");
    }
}
