use std::collections::HashSet;
use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use tower_lsp::lsp_types::Url;

use crate::active_set::ActiveSet;
use crate::binding_map::BindingMap;
use crate::certificate::Certificate;
use crate::checker::Checker;
use crate::clause::Clause;
use crate::code_generator::{CodeGenerator, Error};
use crate::display::DisplayClause;
use crate::interfaces::{ClauseInfo, InfoResult, Location, ProofStepInfo};
use crate::literal::Literal;
use crate::module::ModuleId;
use crate::normalizer::{NormalizedGoal, Normalizer};
use crate::passive_set::PassiveSet;
use crate::project::Project;
use crate::proof::{Difficulty, Proof};
use crate::proof_step::{ProofStep, ProofStepId, Rule, Truthiness};
use crate::term_graph::TermGraphContradiction;

#[derive(Clone)]
pub struct Prover {
    /// The normalizer is used when we are turning the facts and goals from the environment into
    /// clauses that we can use internally.
    /// TODO: make the normalizer not live inside the prover.
    pub normalizer: Normalizer,

    /// The checker validates a proof certificate, after the prover creates it.
    /// TODO: make the checker not live inside the prover.
    pub checker: Checker,

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

    /// Setting any of these flags to true externally will stop the prover.
    pub stop_flags: Vec<Arc<AtomicBool>>,


    /// Number of proof steps activated, not counting Factual ones.
    nonfactual_activations: i32,

    /// The goal of the prover.
    /// If this is None, the goal hasn't been set yet.
    goal: Option<NormalizedGoal>,

    /// If strict codegen is set, we panic when we can't generate code correctly.
    /// Good for testing.
    /// Otherwise, we kinda guess. Good for production.
    pub strict_codegen: bool,
}

/// The outcome of a prover operation.
/// - "Success" means we proved it.
/// - "Exhausted" means we tried every possibility and couldn't prove it.
/// - "Inconsistent" means that we found a contradiction just in our initial assumptions.
/// - "Interrupted" means that the prover was explicitly stopped.
/// - "Timeout" means that we hit a nondeterministic timing limit.
/// - "Constrained" means that we hit some deterministic limit.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Outcome {
    Success,
    Exhausted,
    Inconsistent,
    Interrupted,
    Timeout,
    Constrained,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Timeout => write!(f, "Timeout"),
            Outcome::Constrained => write!(f, "Constrained"),
        }
    }
}

impl Prover {
    /// Creates a new Prover instance
    pub fn new(project: &Project) -> Prover {
        Prover {
            normalizer: Normalizer::new(),
            active_set: ActiveSet::new(),
            passive_set: PassiveSet::new(),
            checker: Checker::new(),
            final_step: None,
            stop_flags: vec![project.build_stopped.clone()],
            useful_passive: vec![],
            nonfactual_activations: 0,
            goal: None,
            strict_codegen: false,
        }
    }

    /// Add proof steps to the prover.
    /// These can be used as initial facts for starting the proof.
    pub fn add_steps(&mut self, steps: Vec<ProofStep>) {
        for step in &steps {
            self.checker.insert_clause(&step.clause);
        }
        self.passive_set.push_batch(steps);
    }

    /// Sets the prover goal and adds the goal-derived steps.
    /// This replaces the common pattern of calling `add_steps` for the goal
    /// steps followed by `set_goal`.
    pub fn set_goal(&mut self, ng: NormalizedGoal, steps: Vec<ProofStep>) {
        assert!(self.goal.is_none());
        self.add_steps(steps);
        self.goal = Some(ng);
    }

    /// Returns the final step of the proof if available
    pub fn get_final_step(&self) -> Option<&ProofStep> {
        self.final_step.as_ref()
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
            Rule::FunctionElimination(info) => {
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
        }

        for rule in &step.simplification_rules {
            answer.push(("simplification".to_string(), ProofStepId::Active(*rule)));
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
    pub fn print_proof(
        &self,
        proof: &Proof,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) {
        println!(
            "in total, we activated {} proof steps.",
            self.active_set.len()
        );
        println!("non-factual activations: {}", self.nonfactual_activations);

        // This logic is similar to the display logic in ProofStep.svelte, but for the terminal.
        let proof_info = self.to_proof_info(&proof, project, bindings, normalizer);
        println!("the proof uses {} steps:", proof_info.len());
        println!();

        for step in proof_info {
            let preposition = match step.location {
                None => "by",
                Some(_) => "from",
            };
            let rule = format!("{} {}", preposition, step.rule);

            // New
            match step.clause.text {
                None => {
                    println!("Contradiction, depth {}, {}.", step.depth, rule);
                }
                Some(clause) => {
                    match &step.clause.id {
                        None => {
                            println!(
                                "An unactivated clause, depth {}, {}:\n    {}",
                                step.depth, rule, clause
                            );
                        }
                        Some(id) => {
                            println!(
                                "Clause {}, depth {}, {}:\n    {}",
                                id, step.depth, rule, clause
                            );
                        }
                    };
                }
            }
            for (desc, premise) in step.premises {
                match premise.id {
                    Some(id) => {
                        println!("  using clause {} as {}:", id, desc);
                    }
                    None => {
                        println!("  using {}:", desc);
                    }
                }
                println!("    {}", premise.text.unwrap_or_else(|| "???".to_string()));
            }
            println!();
        }
    }

    /// get_uncondensed_proof gets a proof, if we have one.
    /// It does not do any simplification of the proof, it's just exactly how we found it.
    /// We always include all of the steps that are mathematically necessary for the proof.
    /// The include_inspiration flag determines whether we include the "inspiration" steps,
    /// which the prover used to find the proof, but are not needed for the proof to be valid.
    pub fn get_uncondensed_proof<'a>(
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
        let negated_goal = match &self.goal {
            Some(goal) => &goal.counterfactual,
            _ => return None,
        };

        let difficulty = if self.nonfactual_activations > Self::VERIFICATION_LIMIT {
            // Verification mode won't find this proof, so we definitely need a shorter one
            Difficulty::Complicated
        } else if self.nonfactual_activations > 500 {
            // Arbitrary heuristic
            Difficulty::Intermediate
        } else {
            Difficulty::Simple
        };

        let mut proof = Proof::new(&normalizer, negated_goal, difficulty);
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

    /// Returns a condensed proof, if we have a proof.
    /// The condensed proof is what we recommend inserting into the code.
    pub fn get_condensed_proof<'a>(&'a self, normalizer: &'a Normalizer) -> Option<Proof<'a>> {
        let mut proof = self.get_uncondensed_proof(normalizer, false)?;
        proof.condense();
        Some(proof)
    }

    /// Generate a certificate for the goal.
    /// If a proof was found, creates a certificate with the proof.
    /// If no proof was found, creates a placeholder certificate with no proof.
    /// If `print` is true, we print the proof.
    pub fn make_cert(
        &self,
        project: &Project,
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

        let proof = match self.get_uncondensed_proof(&normalizer, false) {
            Some(proof) => proof,
            None => {
                // No proof found, create a placeholder certificate
                if print {
                    println!(
                        "No proof found, creating placeholder certificate for goal: {}",
                        goal_name
                    );
                }
                return Ok(Certificate::placeholder(goal_name));
            }
        };

        if print {
            self.print_proof(&proof, project, bindings, normalizer);
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

    fn report_term_graph_contradiction(&mut self, contradiction: TermGraphContradiction) {
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
            let inspiration_id = match step.source.inspiration_id {
                Some(id) => id.get(),
                None => {
                    // No extra specialized clause needed
                    active_ids.push(step.source.pattern_id.get());
                    max_depth = max_depth.max(rewrite_step.depth);
                    continue;
                }
            };

            // Create a new proof step, without activating it, to express the
            // specific equality used by this rewrite.
            let (literal, flipped) =
                Literal::new_with_flip(true, step.left_term().clone(), step.right_term().clone());
            let (clause, traces) = Clause::from_literal(literal, flipped);
            if new_clauses.contains(&clause) {
                // We already created a step for this equality
                // TODO: is it really okay to not insert any sort of id here?
                continue;
            }
            new_clauses.insert(clause.clone());
            let step = ProofStep::specialization(
                step.source.pattern_id.get(),
                inspiration_id,
                rewrite_step,
                clause,
                traces,
            );
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
        for mut passive_step in passive_steps {
            passive_step.printable = false;
            self.useful_passive.push(passive_step);
        }
        self.final_step = Some(ProofStep::passive_contradiction(&self.useful_passive));
    }

    /// Activates the next clause from the queue, unless we're already done.
    /// Returns whether the prover finished.
    pub fn activate_next(&mut self) -> bool {
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

        self.activate(step)
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
    fn activate(&mut self, activated_step: ProofStep) -> bool {
        // Use the step for simplification
        let activated_id = self.active_set.next_id();
        if activated_step.clause.literals.len() == 1 {
            self.passive_set.simplify(activated_id, &activated_step);
        }

        // Generate new clauses
        let (alt_activated_id, generated_steps) = self.active_set.activate(activated_step);
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

            if let Some(simple_step) = self.active_set.simplify(step) {
                if simple_step.clause.is_impossible() {
                    self.final_step = Some(simple_step);
                    return true;
                }
                new_steps.push(simple_step);
            }
        }
        self.passive_set.push_batch(new_steps);

        // Sometimes we find a bunch of contradictions at once.
        // It doesn't really matter what we pick, so we guess which is most likely
        // to be aesthetically pleasing.
        // First regular contradictions (in the loop above), then term graph.

        if let Some(contradiction) = self.active_set.graph.get_contradiction_trace() {
            self.report_term_graph_contradiction(contradiction);
            return true;
        }

        false
    }

    /// The activation_limit to use for verification mode.
    const VERIFICATION_LIMIT: i32 = 2000;

    /// Searches with a short duration.
    /// Designed to be called multiple times in succession.
    /// The time-based limit is set low, so that it feels interactive.
    pub fn partial_search(&mut self) -> Outcome {
        self.search_for_contradiction(5000, 0.1, false)
    }

    /// Search in verification mode to see if this goal can be easily proven.
    /// The time-based limit is set high enough so that hopefully it will not apply,
    /// because we don't want the result of verification to be machine-dependent.
    pub fn verification_search(&mut self) -> Outcome {
        self.search_for_contradiction(Self::VERIFICATION_LIMIT, 5.0, false)
    }

    /// A fast search, for testing.
    pub fn quick_search(&mut self) -> Outcome {
        self.search_for_contradiction(500, 0.3, false)
    }

    /// A fast search that only uses shallow steps, for testing.
    pub fn quick_shallow_search(&mut self) -> Outcome {
        self.search_for_contradiction(500, 0.3, true)
    }

    /// The prover will exit with Outcome::Constrained if it hits a constraint:
    ///   Activating activation_limit nonfactual clauses
    ///   Going over the time limit, in seconds
    ///   Activating all shallow steps, if shallow_only is set
    pub fn search_for_contradiction(
        &mut self,
        activation_limit: i32,
        seconds: f32,
        shallow_only: bool,
    ) -> Outcome {
        let start_time = std::time::Instant::now();
        loop {
            if shallow_only && !self.passive_set.all_shallow {
                return Outcome::Exhausted;
            }
            if self.activate_next() {
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
            for stop_flag in &self.stop_flags {
                if stop_flag.load(std::sync::atomic::Ordering::Relaxed) {
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

    /// Attempts to convert this clause to code, but shows the clause form if that's all we can.
    fn clause_to_code(
        &self,
        clause: &Clause,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) -> String {
        let denormalized = normalizer.denormalize(clause, None);
        match CodeGenerator::new(bindings).value_to_code(&denormalized) {
            Ok(code) => return code,
            Err(Error::Skolem(_)) => {
                // TODO: is this fixed now? We at least sometimes generate skolems.
            }
            Err(e) => {
                // We shouldn't run into these sorts of errors in testing.
                if self.strict_codegen {
                    panic!("{}: could not generate code for clause: {}", e, clause);
                }
            }
        };
        DisplayClause { clause, normalizer }.to_string()
    }

    /// Convert a clause to a jsonable form
    /// We only take active ids, because the others have no external meaning.
    /// If we are given a binding map, use it to make a nicer-looking display.
    fn to_clause_info(
        &self,
        clause: &Clause,
        id: Option<usize>,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) -> ClauseInfo {
        let text = if clause.is_impossible() {
            None
        } else {
            Some(self.clause_to_code(clause, bindings, normalizer))
        };
        ClauseInfo { text, id }
    }

    fn to_proof_step_info(
        &self,
        step: &ProofStep,
        active_id: Option<usize>,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) -> ProofStepInfo {
        let clause = self.to_clause_info(&step.clause, active_id, bindings, normalizer);
        let mut premises = vec![];
        for (description, id) in self.descriptive_dependencies(&step) {
            let clause = self.get_clause(id);
            let clause_info = self.to_clause_info(clause, id.active_id(), bindings, normalizer);
            premises.push((description, clause_info));
        }
        let (rule, location) = match &step.rule {
            Rule::Assumption(info) => {
                let location = project
                    .path_from_module_id(info.source.module_id)
                    .and_then(|path| Url::from_file_path(path).ok())
                    .map(|uri| Location {
                        uri,
                        range: info.source.range,
                    });

                (info.source.description(), location)
            }
            _ => (step.rule.name().to_lowercase(), None),
        };
        ProofStepInfo {
            clause,
            premises,
            rule,
            location,
            depth: step.depth,
        }
    }

    /// Call this after the prover succeeds to get the proof steps in jsonable form.
    /// This is called with the bindings for the top-level environment.
    /// However, that doesn't really seem like the right thing to od.
    /// It isn't clear to me whether this is okay or not.
    pub fn to_proof_info(
        &self,
        proof: &Proof,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) -> Vec<ProofStepInfo> {
        let mut result = vec![];
        for (step_id, step) in &proof.all_steps {
            result.push(self.to_proof_step_info(
                step,
                step_id.active_id(),
                project,
                bindings,
                normalizer,
            ));
        }
        result
    }

    /// Generates information about a clause in jsonable format.
    /// Returns None if we don't have any information about this clause.
    pub fn info_result(
        &self,
        id: usize,
        project: &Project,
        bindings: &BindingMap,
        normalizer: &Normalizer,
    ) -> Option<InfoResult> {
        // Information for the step that proved this clause
        if !self.active_set.has_step(id) {
            return None;
        }
        let step = self.to_proof_step_info(
            self.active_set.get_step(id),
            Some(id),
            project,
            bindings,
            normalizer,
        );
        let mut consequences = vec![];
        let mut num_consequences = 0;
        let limit = 100;

        // Check if the final step is a consequence of this clause
        if let Some(final_step) = &self.final_step {
            if final_step.depends_on_active(id) {
                consequences.push(self.to_proof_step_info(
                    &final_step,
                    None,
                    project,
                    bindings,
                    normalizer,
                ));
                num_consequences += 1;
            }
        }

        // Check the active set for consequences
        for (i, step) in self.active_set.find_consequences(id) {
            if consequences.len() < limit {
                consequences.push(self.to_proof_step_info(
                    step,
                    Some(i),
                    project,
                    bindings,
                    normalizer,
                ));
            }
            num_consequences += 1;
        }

        // Check the passive set for consequences
        for step in self.passive_set.find_consequences(id) {
            if consequences.len() < limit {
                consequences
                    .push(self.to_proof_step_info(step, None, project, bindings, normalizer));
            }
            num_consequences += 1;
        }

        Some(InfoResult {
            step,
            consequences,
            num_consequences,
        })
    }

    /// Should only be called after proving completes successfully.
    /// Gets the qualified name of every fact that was used in the proof.
    /// This includes the "inspiration" facts that were used to find the proof but are
    /// not mathematically necessary for the proof to be valid.
    pub fn get_useful_source_names(
        &self,
        names: &mut HashSet<(ModuleId, String)>,
        normalizer: &Normalizer,
    ) {
        let proof = match self.get_uncondensed_proof(&normalizer, true) {
            Some(proof) => proof,
            None => return,
        };
        for (_, step) in proof.all_steps {
            if let Rule::Assumption(ai) = &step.rule {
                if !ai.source.importable {
                    // Non-importable facts are local ones that don't count.
                    continue;
                }
                if let Some(qn) = ai.source.qualified_name() {
                    names.insert(qn);
                }
            }
        }
    }
}
