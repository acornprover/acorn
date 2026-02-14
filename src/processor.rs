use std::borrow::Cow;

use crate::builder::BuildError;
use crate::certificate::{Certificate, CertificateLine};
use crate::code_generator::Error;
use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::node::NodeCursor;
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::proof_step::Rule;
use crate::normalizer::{NormalizedFact, NormalizedGoal, Normalizer};
use crate::project::Project;
use crate::prover::{Outcome, Prover, ProverMode};
use tokio_util::sync::CancellationToken;

/// The processor represents what we do with a stream of facts.
#[derive(Clone)]
pub struct Processor {
    prover: Prover,
    checker: Checker,
}

impl Processor {
    fn bindings_with_type_params<'a>(
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
        Processor {
            prover: Prover::new(vec![]),
            checker: Checker::new(),
        }
    }

    pub fn with_token(cancellation_token: CancellationToken) -> Processor {
        Processor {
            prover: Prover::new(vec![cancellation_token]),
            checker: Checker::new(),
        }
    }

    /// Creates a new Processor with imports already added from normalized state.
    /// This uses pre-normalized facts directly (no normalization in phase three).
    pub fn with_imports(
        cancellation_token: Option<CancellationToken>,
        env: &crate::elaborator::environment::Environment,
    ) -> Result<Processor, BuildError> {
        let mut processor = Processor {
            prover: match cancellation_token {
                Some(token) => Prover::new(vec![token]),
                None => Prover::new(vec![]),
            },
            checker: Checker::new(),
        };
        // Add pre-normalized import facts
        for normalized in &env.normalized_imports {
            processor.add_normalized_fact(normalized)?;
        }
        Ok(processor)
    }

    /// Adds all module-local facts that are usable at the given cursor position.
    pub fn add_module_facts(&mut self, cursor: &NodeCursor) -> Result<(), BuildError> {
        let facts = cursor
            .visible_normalized_facts()
            .map_err(|message| BuildError::new(Default::default(), message))?;
        for normalized in facts {
            self.add_normalized_fact(normalized)?;
        }
        Ok(())
    }

    pub fn prover(&self) -> &Prover {
        &self.prover
    }
    pub fn checker(&self) -> &Checker {
        &self.checker
    }

    /// Adds a normalized fact to the prover.
    pub fn add_normalized_fact(&mut self, normalized: &NormalizedFact) -> Result<(), BuildError> {
        let kernel_context = normalized.normalizer.kernel_context();
        for step in &normalized.steps {
            // Extract the source from the step's rule.
            let step_source = match &step.rule {
                Rule::Assumption(info) => info.source.clone(),
                _ => {
                    return Err(BuildError::new(
                        Default::default(),
                        format!(
                            "Expected assumption step from normalize_fact, got: {:?}",
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
        self.prover
            .add_steps(normalized.steps.clone(), kernel_context);
        Ok(())
    }

    /// Sets a normalized goal as the prover's goal.
    pub fn set_normalized_goal(&mut self, normalized: &NormalizedGoal) {
        let source = &normalized.goal.proposition.source;
        let kernel_context = normalized.normalizer.kernel_context();
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
        self.prover.set_goal(
            normalized.goal.clone(),
            normalized.steps.clone(),
            kernel_context,
        );
    }

    /// Forwards a search request to the underlying prover.
    pub fn search(&mut self, mode: ProverMode, normalizer: &Normalizer) -> Outcome {
        self.prover.search(mode, normalizer)
    }

    /// Creates a certificate from the current proof state.
    pub fn make_cert(
        &self,
        bindings: &BindingMap,
        normalizer: &Normalizer,
        print: bool,
    ) -> Result<Certificate, Error> {
        self.prover.make_cert(bindings, normalizer, print)
    }

    /// Checks a certificate.
    /// Clones the checker and normalizer, because the checking process despoils them.
    /// If the goal is provided, it is added to the checker before checking the certificate.
    /// Returns a list of CertificateLines showing how each line was verified.
    pub fn check_cert(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&NormalizedGoal>,
        normalizer: &Normalizer,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<Vec<CertificateLine>, Error> {
        let mut checker = self.checker.clone();
        let mut normalizer = normalizer.clone();
        let mut cert_bindings = Cow::Borrowed(bindings);

        if let Some(normalized_goal) = normalized_goal {
            checker.insert_normalized_goal(normalized_goal, &mut normalizer)?;
            cert_bindings =
                Self::bindings_with_type_params(bindings, &normalized_goal.goal.proposition.params);
        } else if let Some(type_params) = self.prover.goal_type_params() {
            cert_bindings = Self::bindings_with_type_params(bindings, type_params);
        }

        let normalizer = Cow::Owned(normalizer);
        cert.check(checker, project, cert_bindings, normalizer)
    }

    /// Cleans a certificate by removing unnecessary steps.
    /// Similar to check_cert but returns the cleaned certificate along with the steps.
    pub fn clean_cert(
        &self,
        cert: Certificate,
        normalized_goal: Option<&NormalizedGoal>,
        normalizer: &Normalizer,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<(Certificate, Vec<CertificateLine>), Error> {
        let mut checker = self.checker.clone();
        let mut normalizer = normalizer.clone();
        let mut cert_bindings = Cow::Borrowed(bindings);

        if let Some(normalized_goal) = normalized_goal {
            checker.insert_normalized_goal(normalized_goal, &mut normalizer)?;
            cert_bindings =
                Self::bindings_with_type_params(bindings, &normalized_goal.goal.proposition.params);
        } else if let Some(type_params) = self.prover.goal_type_params() {
            cert_bindings = Self::bindings_with_type_params(bindings, type_params);
        }

        let normalizer = Cow::Owned(normalizer);
        cert.clean(checker, project, cert_bindings, normalizer)
    }

    /// Creates a test Processor from code containing a theorem named "goal".
    /// Loads facts and sets up the goal, which triggers normalization.
    /// Returns the Processor and the goal-level BindingMap.
    #[cfg(test)]
    pub fn test_goal(code: &str) -> (Processor, BindingMap, NormalizedGoal) {
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
        let goal_env = cursor.goal_env().unwrap();

        let mut processor = Processor::with_imports(None, env).unwrap();
        processor.add_module_facts(&cursor).unwrap();
        let normalized_goal = cursor.normalized_goal().expect("missing normalized goal");
        processor.set_normalized_goal(normalized_goal);

        (
            processor,
            goal_env.bindings.clone(),
            normalized_goal.clone(),
        )
    }

    /// Test helper: verify a line of certificate code can be parsed.
    /// Panics if parsing fails.
    #[cfg(test)]
    pub fn test_parse_code(&self, code: &str, bindings: &BindingMap, normalizer: &Normalizer) {
        use std::borrow::Cow;

        let mut normalizer_cow = Cow::Owned(normalizer.clone());
        let mut bindings_cow = Cow::Borrowed(bindings);
        let project = Project::new_mock();

        Certificate::parse_code_line(code, &project, &mut bindings_cow, &mut normalizer_cow)
            .unwrap();
    }
}
