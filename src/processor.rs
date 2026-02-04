use std::borrow::Cow;

use crate::builder::BuildError;
use crate::certificate::Certificate;
use crate::checker::{CertificateStep, Checker, StepReason};
use crate::code_generator::Error;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::node::NodeCursor;
use crate::normalizer::{NormalizedFact, NormalizedGoal, Normalizer};
use crate::project::Project;
use crate::proof_step::Rule;
use crate::prover::{Outcome, Prover, ProverMode};
use tokio_util::sync::CancellationToken;
use tracing::debug;

/// The processor represents what we do with a stream of facts.
#[derive(Clone)]
pub struct Processor {
    prover: Prover,
    normalizer: Normalizer,
    checker: Checker,
}

impl Processor {
    pub fn new() -> Processor {
        Processor {
            prover: Prover::new(vec![]),
            normalizer: Normalizer::new(),
            checker: Checker::new(),
        }
    }

    pub fn with_token(cancellation_token: CancellationToken) -> Processor {
        Processor {
            prover: Prover::new(vec![cancellation_token]),
            normalizer: Normalizer::new(),
            checker: Checker::new(),
        }
    }

    /// Creates a new Processor with imports already added from prenormalized state.
    /// This clones the import_normalizer and adds pre-normalized facts directly.
    pub fn with_imports(
        cancellation_token: Option<CancellationToken>,
        env: &crate::elaborator::environment::Environment,
    ) -> Result<Processor, BuildError> {
        let import_normalizer = env
            .import_normalizer
            .as_ref()
            .expect("import_normalizer should be set by prenormalize()");
        let mut processor = Processor {
            prover: match cancellation_token {
                Some(token) => Prover::new(vec![token]),
                None => Prover::new(vec![]),
            },
            normalizer: import_normalizer.clone(),
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
            self.add_normalized_fact_with_normalizer(normalized)?;
        }
        Ok(())
    }

    pub fn prover(&self) -> &Prover {
        &self.prover
    }
    pub fn normalizer(&self) -> &Normalizer {
        &self.normalizer
    }
    pub fn checker(&self) -> &Checker {
        &self.checker
    }

    /// Adds a normalized fact to the prover.
    pub fn add_normalized_fact(&mut self, normalized: &NormalizedFact) -> Result<(), BuildError> {
        let kernel_context = self.normalizer.kernel_context();
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

    /// Adds a normalized fact and updates the normalizer to the fact's state.
    pub fn add_normalized_fact_with_normalizer(
        &mut self,
        normalized: &NormalizedFact,
    ) -> Result<(), BuildError> {
        self.normalizer = normalized.normalizer.clone();
        self.add_normalized_fact(normalized)
    }

    /// Normalizes a fact and adds the resulting proof steps to the prover.
    pub fn add_fact(&mut self, fact: &Fact) -> Result<(), BuildError> {
        match fact {
            Fact::Proposition(prop) => debug!(value = %prop.value, "adding proposition"),
            Fact::Definition(c, val, _) => debug!(constant = %c, value = %val, "adding definition"),
            _ => debug!("adding other fact"),
        }
        let normalized = self.normalizer.normalize_fact(fact)?;
        self.add_normalized_fact(&normalized)
    }

    /// Sets a normalized goal as the prover's goal.
    /// Also sets the normalizer to the state from the NormalizedGoal.
    pub fn set_normalized_goal(&mut self, normalized: &NormalizedGoal) {
        // Use the pre-normalized normalizer state (which includes the negated goal)
        self.normalizer = normalized.normalizer.clone();

        let source = &normalized.goal.proposition.source;
        let kernel_context = self.normalizer.kernel_context();
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

    /// Normalizes a goal and sets it as the prover's goal.
    /// Prefer set_normalized_goal when pre-normalized data is available.
    pub fn set_goal(&mut self, goal: &Goal) -> Result<(), BuildError> {
        let normalized = self.normalizer.normalize_goal(goal)?;
        self.set_normalized_goal(&normalized);
        Ok(())
    }

    /// Forwards a search request to the underlying prover.
    pub fn search(&mut self, mode: ProverMode) -> Outcome {
        self.prover.search(mode, &self.normalizer)
    }

    /// Creates a certificate from the current proof state.
    pub fn make_cert(&self, bindings: &BindingMap, print: bool) -> Result<Certificate, Error> {
        self.prover.make_cert(bindings, &self.normalizer, print)
    }

    /// Checks a certificate.
    /// Clones the checker and normalizer, because the checking process despoils them.
    /// If the goal is provided, it is added to the checker before checking the certificate.
    /// Returns a list of CertificateSteps showing how each step was verified.
    pub fn check_cert(
        &self,
        cert: &Certificate,
        normalized_goal: Option<&NormalizedGoal>,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<Vec<CertificateStep>, Error> {
        let mut checker = self.checker.clone();
        let mut normalizer = self.normalizer.clone();

        if let Some(normalized_goal) = normalized_goal {
            checker.insert_normalized_goal(normalized_goal, &mut normalizer)?;
        }

        let bindings = Cow::Borrowed(bindings);
        let normalizer = Cow::Owned(normalizer);
        checker.check_cert(cert, project, bindings, normalizer)
    }

    /// Cleans a certificate by removing unnecessary steps.
    /// Similar to check_cert but returns the cleaned certificate along with the steps.
    pub fn clean_cert(
        &self,
        cert: Certificate,
        normalized_goal: Option<&NormalizedGoal>,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<(Certificate, Vec<CertificateStep>), Error> {
        let mut checker = self.checker.clone();
        let mut normalizer = self.normalizer.clone();

        if let Some(normalized_goal) = normalized_goal {
            checker.insert_normalized_goal(normalized_goal, &mut normalizer)?;
        }

        let bindings = Cow::Borrowed(bindings);
        let normalizer = Cow::Owned(normalizer);
        checker.clean_cert(cert, project, bindings, normalizer)
    }

    /// Creates a test Processor from code containing a theorem named "goal".
    /// Loads facts and sets up the goal, which triggers normalization.
    /// Returns the Processor (which owns the Normalizer) and the goal-level BindingMap.
    #[cfg(test)]
    pub fn test_goal(code: &str) -> (Processor, BindingMap) {
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
        let normalized_goal = cursor
            .normalized_goal()
            .expect("missing prenormalized goal");
        processor.set_normalized_goal(normalized_goal);

        (processor, goal_env.bindings.clone())
    }

    /// Test helper: verify a line of certificate code can be parsed.
    /// Panics if parsing fails.
    #[cfg(test)]
    pub fn test_parse_code(&self, code: &str, bindings: &BindingMap) {
        use std::borrow::Cow;

        let normalizer = self.normalizer.clone();
        let kernel_context = normalizer.kernel_context().clone();
        let mut normalizer_cow = Cow::Owned(normalizer);
        let mut bindings_cow = Cow::Borrowed(bindings);
        let project = Project::new_mock();

        Checker::parse_code_line(
            code,
            &project,
            &mut bindings_cow,
            &mut normalizer_cow,
            &kernel_context,
        )
        .unwrap();
    }
}
