use std::collections::HashSet;
use tokio_util::sync::CancellationToken;

use super::active_set::ActiveSet;
use super::passive_set::PassiveSet;
use super::proof::Proof;
use crate::certificate::Certificate;
use crate::code_generator::{CodeGenerator, Error};
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::goal::Goal;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::unifier::{Scope, Unifier};
use crate::kernel::variable_map::VariableMap;
use crate::kernel::EqualityGraphContradiction;
use crate::normalizer::Normalizer;
use crate::proof_step::{PremiseMap, ProofStep, ProofStepId, Rule, Truthiness};
use crate::prover::{Outcome, ProverMode};

/// A traditional saturation prover. Uses just a bit of AI for scoring.
///
/// Uses the "given-clause" algorithm.
/// Passive clauses are those generated but no yet processed.
/// Active clauses are those already selected for inference.
///
/// At each iteration, the prover selects a given clause from the passive set, moves it to the
/// active set, and performs inferences between it and the active clauses. This continues until
/// a contradiction is found or the search saturates.
#[derive(Clone)]
pub struct Prover {
    /// The "active" clauses are the ones we use for reasoning.
    active_set: ActiveSet,

    /// The "passive" clauses are a queue of pending clauses that
    /// we will add to the active clauses in the future.
    passive_set: PassiveSet,

    /// The last step of the proof search that leads to a contradiction.
    /// If we haven't finished the search, this is None.
    final_step: Option<ProofStep>,

    /// Clauses that we never activated, but we did use to find a contradiction.
    useful_passive: Vec<ProofStep>,

    /// If any one of these tokens is canceled, the prover should stop working and exit
    /// with an Outcome::Interrupted.
    cancellation_tokens: Vec<CancellationToken>,

    /// Number of proof steps activated, not counting Factual ones.
    nonfactual_activations: i32,

    /// The goal of the prover.
    /// If this is None, the goal hasn't been set yet.
    goal: Option<Goal>,
}

impl Prover {
    /// Creates a new Prover instance.
    /// The prover must stop when any of its cancellation tokens are canceled.
    pub fn new(tokens: Vec<CancellationToken>) -> Prover {
        Prover {
            active_set: ActiveSet::new(),
            passive_set: PassiveSet::new(),
            final_step: None,
            cancellation_tokens: tokens,
            useful_passive: vec![],
            nonfactual_activations: 0,
            goal: None,
        }
    }

    /// Returns an iterator over the active proof steps
    pub fn iter_active_steps(&self) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.active_set.iter_steps()
    }

    /// (description, id) for every clause this rule depends on.
    /// Entries with an id are references to clauses we are using.
    /// An entry with no id is like a comment, it won't be linked to anything.
    fn descriptive_dependencies(&self, step: &ProofStep) -> Vec<(String, ProofStepId)> {
        let mut answer = vec![];
        match &step.rule {
            Rule::Assumption(_) => {}
            Rule::Resolution(info) => {
                answer.push((
                    "long resolver".to_string(),
                    ProofStepId::Active(info.long_id),
                ));
                answer.push((
                    "short resolver".to_string(),
                    ProofStepId::Active(info.short_id),
                ));
            }
            Rule::Rewrite(info) => {
                answer.push(("target".to_string(), ProofStepId::Active(info.target_id)));
                answer.push(("pattern".to_string(), ProofStepId::Active(info.pattern_id)));
            }
            Rule::EqualityFactoring(info) => {
                answer.push(("source".to_string(), ProofStepId::Active(info.id)));
            }
            Rule::EqualityResolution(info) => {
                answer.push(("source".to_string(), ProofStepId::Active(info.id)));
            }
            Rule::Injectivity(info) => {
                answer.push(("source".to_string(), ProofStepId::Active(info.id)));
            }
            Rule::BooleanReduction(info) => {
                answer.push(("source".to_string(), ProofStepId::Active(info.id)));
            }
            Rule::Extensionality(info) => {
                answer.push(("source".to_string(), ProofStepId::Active(info.id)));
            }
            Rule::Specialization(info) => {
                answer.push(("pattern".to_string(), ProofStepId::Active(info.pattern_id)));
            }
            Rule::MultipleRewrite(info) => {
                answer.push((
                    "inequality".to_string(),
                    ProofStepId::Active(info.inequality_id),
                ));
                for &id in &info.active_ids {
                    answer.push(("equality".to_string(), ProofStepId::Active(id)));
                }
                for &id in &info.passive_ids {
                    answer.push(("specialization".to_string(), ProofStepId::Passive(id)));
                }
            }
            Rule::PassiveContradiction(n) => {
                for id in 0..*n {
                    answer.push(("clause".to_string(), ProofStepId::Passive(id)));
                }
            }
            Rule::Simplification(info) => {
                // Include the original step's descriptive dependencies
                answer.extend(self.descriptive_dependencies(&info.original));
                // Add the simplifying clauses
                for &id in &info.simplifying_ids {
                    answer.push(("simplification".to_string(), ProofStepId::Active(id)));
                }
            }
        }

        answer
    }

    /// Returns the number of activated clauses
    pub fn num_activated(&self) -> usize {
        self.active_set.len()
    }

    /// Returns the number of passive clauses
    pub fn num_passive(&self) -> usize {
        self.passive_set.len()
    }

    /// Prints the proof in a human-readable form.
    pub fn print_proof(&self, proof: &Proof, bindings: &BindingMap, normalizer: &Normalizer) {
        println!(
            "in total, we activated {} proof steps.",
            self.active_set.len()
        );
        println!("non-factual activations: {}", self.nonfactual_activations);

        println!("the proof uses {} steps:", proof.steps.len());
        println!();

        for (step_id, step) in &proof.steps {
            let rule_name = step.rule.name().to_lowercase();
            let preposition = "by";
            let rule = format!("{} {}", preposition, rule_name);

            if step.clause.is_impossible() {
                println!("Contradiction, depth {}, {}.", step.depth, rule);
            } else {
                let denormalized = normalizer.denormalize(&step.clause, None, None, false);
                let clause_text = CodeGenerator::new(bindings)
                    .value_to_code(&denormalized)
                    .unwrap_or_else(|_| format!("{:?}", step.clause));

                match step_id.active_id() {
                    None => {
                        println!(
                            "An unactivated clause, depth {}, {}:\n    {}",
                            step.depth, rule, clause_text
                        );
                    }
                    Some(id) => {
                        println!(
                            "Clause {}, depth {}, {}:\n    {}",
                            id, step.depth, rule, clause_text
                        );
                    }
                };
            }

            for (desc, dep_id) in self.descriptive_dependencies(&step) {
                let dep_clause = self.get_clause(dep_id);
                match dep_id.active_id() {
                    Some(id) => {
                        println!("  using clause {} as {}:", id, desc);
                    }
                    None => {
                        println!("  using {}:", desc);
                    }
                }
                let dep_text = if dep_clause.is_impossible() {
                    "contradiction".to_string()
                } else {
                    let denormalized = normalizer.denormalize(&dep_clause, None, None, false);
                    CodeGenerator::new(bindings)
                        .value_to_code(&denormalized)
                        .unwrap_or_else(|_| format!("{:?}", dep_clause))
                };
                println!("    {}", dep_text);
            }
            println!();
        }
    }

    /// get_uncondensed_proof gets a proof, if we have one.
    /// It does not do any simplification of the proof, it's just exactly how we found it.
    /// We always include all of the steps that are mathematically necessary for the proof.
    /// The include_inspiration flag determines whether we include the "inspiration" steps,
    /// which the prover used to find the proof, but are not needed for the proof to be valid.
    fn get_proof<'a>(
        &'a self,
        normalizer: &'a Normalizer,
        include_inspiration: bool,
    ) -> Option<Proof<'a>> {
        let final_step = match &self.final_step {
            Some(step) => step,
            None => return None,
        };
        let mut useful_active = HashSet::new();
        self.active_set
            .find_upstream(&final_step, include_inspiration, &mut useful_active);
        for step in &self.useful_passive {
            self.active_set
                .find_upstream(step, include_inspiration, &mut useful_active);
        }
        let mut proof = Proof::new(&normalizer);
        let mut active_ids: Vec<_> = useful_active.iter().collect();
        active_ids.sort();
        for i in active_ids {
            let step = self.active_set.get_step(*i);
            proof.add_step(ProofStepId::Active(*i), step);
        }
        for (i, step) in self.useful_passive.iter().enumerate() {
            proof.add_step(ProofStepId::Passive(i as u32), step);
        }
        proof.add_step(ProofStepId::Final, final_step);
        Some(proof)
    }

    /// Generate a certificate for the goal.
    /// If a proof was found, creates a certificate with the proof.
    /// If no proof was found, creates a placeholder certificate with no proof.
    /// If `print` is true, we print the proof.
    pub fn make_cert(
        &self,
        bindings: &BindingMap,
        normalizer: &Normalizer,
        print: bool,
    ) -> Result<Certificate, Error> {
        let goal_name = self
            .goal
            .as_ref()
            .ok_or_else(|| Error::internal("no goal set"))?
            .name
            .clone();

        let proof = self
            .get_proof(&normalizer, false)
            .ok_or_else(|| Error::internal("No proof found"))?;

        if print {
            self.print_proof(&proof, bindings, normalizer);
        }

        let cert = proof.make_cert(goal_name, bindings)?;
        if print {
            println!("concrete proof:");
            if let Some(proof) = &cert.proof {
                for line in proof {
                    println!("  {}", line);
                }
            } else {
                println!("  <no proof>");
            }
        }
        // Check parameter removed - was always false

        Ok(cert)
    }

    fn report_equality_graph_contradiction(
        &mut self,
        contradiction: EqualityGraphContradiction,
        #[cfg_attr(not(feature = "validate"), allow(unused_variables))]
        kernel_context: &KernelContext,
    ) {
        let mut active_ids = vec![];
        let mut passive_ids = vec![];
        let mut new_clauses = HashSet::new();
        let mut max_depth = 0;
        let inequality_step = self.active_set.get_step(contradiction.inequality_id);
        let mut truthiness = inequality_step.truthiness;
        for step in contradiction.rewrite_chain {
            let pattern_id = step.source.pattern_id.get();
            let rewrite_step = self.active_set.get_step(pattern_id);
            truthiness = truthiness.combine(rewrite_step.truthiness);

            // Check whether we need to explicitly add a specialized clause to the proof.
            let has_type_params = rewrite_step
                .clause
                .get_local_context()
                .get_var_types()
                .iter()
                .any(|t| t.as_ref().is_type_param_kind());
            let needs_specialization = rewrite_step.clause.has_any_variable() || has_type_params;

            let inspiration_id = match step.source.inspiration_id {
                Some(id) => id.get(),
                None => {
                    // If the rewrite pattern is concrete, no extra specialized clause is needed.
                    // But if the pattern has variables, we must emit a specialization so the
                    // checker can see the concrete equality used in the rewrite chain.
                    active_ids.push(step.source.pattern_id.get());
                    max_depth = max_depth.max(rewrite_step.depth);
                    if !needs_specialization {
                        continue;
                    }
                    step.source.pattern_id.get()
                }
            };

            // Create a new proof step, without activating it, to express the
            // specific equality used by this rewrite.
            let (literal, _flipped) =
                Literal::new_with_flip(true, step.left_term().clone(), step.right_term().clone());
            let (clause, _var_ids) =
                Clause::normalize_with_var_ids(vec![literal], &LocalContext::empty());
            if new_clauses.contains(&clause) {
                // We already created a step for this equality
                // TODO: is it really okay to not insert any sort of id here?
                continue;
            }
            new_clauses.insert(clause.clone());
            // Compute pattern var_map by unifying the pattern literal against the concrete literal.
            let pattern_clause = &rewrite_step.clause;
            let mut unifier = Unifier::new(3, kernel_context);
            unifier.set_input_context(Scope::LEFT, pattern_clause.get_local_context());
            unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());
            let mut unified = unifier.unify_literals(
                Scope::LEFT,
                &pattern_clause.literals[0],
                Scope::RIGHT,
                &clause.literals[0],
                false,
            );
            if !unified {
                let mut flipped_unifier = Unifier::new(3, kernel_context);
                flipped_unifier.set_input_context(Scope::LEFT, pattern_clause.get_local_context());
                flipped_unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());
                unified = flipped_unifier.unify_literals(
                    Scope::LEFT,
                    &pattern_clause.literals[0],
                    Scope::RIGHT,
                    &clause.literals[0],
                    true,
                );
                if unified {
                    unifier = flipped_unifier;
                }
            }
            if !unified {
                panic!(
                    "Failed to unify rewrite pattern with concrete clause.\nPattern: {}\nClause: {}",
                    pattern_clause, clause
                );
            }
            let (all_maps, output_context) = unifier.into_maps_with_context();
            let pattern_var_map = all_maps
                .into_iter()
                .find(|(scope, _)| *scope == Scope::LEFT)
                .map(|(_, map)| map)
                .unwrap_or_else(VariableMap::new);
            let premise_map = PremiseMap::new(vec![pattern_var_map], vec![], output_context);
            let step = ProofStep::specialization(
                step.source.pattern_id.get(),
                inspiration_id,
                rewrite_step,
                clause,
                premise_map,
            );

            // Validate specialization steps
            #[cfg(feature = "validate")]
            if let Err(e) = self.active_set.validate_step(&step, kernel_context) {
                panic!(
                    "Invalid specialization step: {}\nStep clause: {}\nInspiration id: {}",
                    e, step.clause, inspiration_id
                );
            }

            max_depth = max_depth.max(step.depth);
            let passive_id = self.useful_passive.len() as u32;
            self.useful_passive.push(step);
            passive_ids.push(passive_id);
        }

        active_ids.sort();
        active_ids.dedup();

        self.final_step = Some(ProofStep::multiple_rewrite(
            contradiction.inequality_id,
            active_ids,
            passive_ids,
            truthiness,
            max_depth,
        ));
    }

    fn report_passive_contradiction(&mut self, passive_steps: Vec<ProofStep>) {
        assert!(self.useful_passive.is_empty());
        for passive_step in passive_steps {
            self.useful_passive.push(passive_step);
        }
        self.final_step = Some(ProofStep::passive_contradiction(&self.useful_passive));
    }

    /// Activates the next clause from the queue, unless we're already done.
    /// Returns whether the prover finished.
    fn activate_next(&mut self, kernel_context: &KernelContext) -> bool {
        if self.final_step.is_some() {
            return true;
        }

        if let Some(passive_steps) = self.passive_set.get_contradiction() {
            self.report_passive_contradiction(passive_steps);
            return true;
        }

        let step = match self.passive_set.pop() {
            Some(step) => step,
            None => {
                // We're out of clauses to process, so we can't make any more progress.
                return true;
            }
        };

        if step.truthiness != Truthiness::Factual {
            self.nonfactual_activations += 1;
        }

        if step.clause.is_impossible() {
            self.final_step = Some(step);
            return true;
        }

        self.activate(step, kernel_context)
    }

    /// Generates new passive clauses, simplifying appropriately, and adds them to the passive set.
    ///
    /// This does two forms of simplification. It simplifies all existing passive clauses based on
    /// the newly activated clause, and simplifies the new passive clauses based on all
    /// existing active clauses.
    ///
    /// This double simplification ensures that every passive clause is always simplified with
    /// respect to every active clause.
    ///
    /// Returns whether the prover finished.
    fn activate(&mut self, activated_step: ProofStep, kernel_context: &KernelContext) -> bool {
        // Use the step for simplification
        let activated_id = self.active_set.next_id();
        if activated_step.clause.literals.len() == 1 {
            self.passive_set.simplify(
                activated_id,
                &activated_step,
                &self.active_set,
                kernel_context,
            );
        }

        // Generate new clauses
        let (alt_activated_id, generated_steps) =
            self.active_set.activate(activated_step, kernel_context);
        assert_eq!(activated_id, alt_activated_id);

        let mut new_steps = vec![];
        for step in generated_steps {
            if step.finishes_proof() {
                self.final_step = Some(step);
                return true;
            }

            if step.automatic_reject() {
                continue;
            }

            if let Some(simple_step) = self.active_set.simplify(step, kernel_context) {
                if simple_step.clause.is_impossible() {
                    self.final_step = Some(simple_step);
                    return true;
                }
                new_steps.push(simple_step);
            }
        }
        self.passive_set.push_batch(new_steps, kernel_context);

        // Sometimes we find a bunch of contradictions at once.
        // It doesn't really matter what we pick, so we guess which is most likely
        // to be aesthetically pleasing.
        // First regular contradictions (in the loop above), then term graph.

        if let Some(contradiction) = self.active_set.graph.get_contradiction_trace() {
            self.report_equality_graph_contradiction(contradiction, kernel_context);
            return true;
        }

        false
    }

    /// Gets a clause by its proof step ID
    fn get_clause(&self, id: ProofStepId) -> &Clause {
        match id {
            ProofStepId::Active(i) => self.active_set.get_clause(i),
            ProofStepId::Passive(i) => &self.useful_passive[i as usize].clause,
            ProofStepId::Final => {
                let final_step = self.final_step.as_ref().unwrap();
                &final_step.clause
            }
        }
    }

    /// Add proof steps to the prover.
    /// These can be used as initial facts for starting the proof.
    pub fn add_steps(&mut self, steps: Vec<ProofStep>, kernel_context: &KernelContext) {
        self.passive_set.push_batch(steps, kernel_context);
    }

    /// The prover will exit with Outcome::Constrained if it hits a constraint:
    ///   Activating activation_limit nonfactual clauses
    ///   Going over the time limit, in seconds
    ///   Activating all shallow steps, if shallow_only is set
    pub fn search(&mut self, mode: ProverMode, normalizer: &Normalizer) -> Outcome {
        let kernel_context = normalizer.kernel_context();

        // Convert mode to actual parameters
        let (activation_limit, seconds, shallow_only) = match mode {
            ProverMode::Interactive { timeout_secs } => (2000, timeout_secs, false),
            ProverMode::Test => (500, 0.3, true),
        };
        // Special test behavior: if we're in test mode and trying to prove "test_hang",
        // wait for cancellation instead of actually proving
        #[cfg(test)]
        {
            if let Some(goal) = &self.goal {
                if goal.name == "test_hang" {
                    // Wait indefinitely for cancellation
                    loop {
                        for token in &self.cancellation_tokens {
                            if token.is_cancelled() {
                                return Outcome::Interrupted;
                            }
                        }
                        std::thread::sleep(std::time::Duration::from_millis(10));
                    }
                }
            }
        }

        let start_time = std::time::Instant::now();
        loop {
            if shallow_only && !self.passive_set.all_shallow {
                return Outcome::Exhausted;
            }
            if self.activate_next(kernel_context) {
                // The prover terminated. Determine which outcome that is.
                if let Some(final_step) = &self.final_step {
                    if final_step.truthiness == Truthiness::Counterfactual {
                        // The normal success case
                        return Outcome::Success;
                    }
                    if let Some(goal) = &self.goal {
                        if goal.inconsistency_okay {
                            // We found an inconsistency in our assumptions, but it's okay
                            return Outcome::Success;
                        }
                    }
                    // We found an inconsistency and it's not okay
                    return Outcome::Inconsistent;
                }
                return Outcome::Exhausted;
            }
            for token in &self.cancellation_tokens {
                if token.is_cancelled() {
                    return Outcome::Interrupted;
                }
            }
            if self.nonfactual_activations >= activation_limit {
                return Outcome::Constrained;
            }
            let elapsed = start_time.elapsed().as_secs_f32();
            if elapsed >= seconds {
                return Outcome::Timeout;
            }
        }
    }

    pub fn set_goal(&mut self, goal: Goal, steps: Vec<ProofStep>, kernel_context: &KernelContext) {
        assert!(self.goal.is_none());
        self.add_steps(steps, kernel_context);
        self.goal = Some(goal);
    }
}
