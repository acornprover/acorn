use std::borrow::Cow;
use std::collections::HashSet;
use std::env;
use std::fmt::Write as _;
use tokio_util::sync::CancellationToken;
use tracing::trace;

use super::active_set::ActiveSet;
use super::passive_set::PassiveSet;
use super::proof::Proof;
use super::synthetic::WitnessRegistry;
use crate::certificate::Certificate;
use crate::code_generator::{CodeGenerator, Error};
use crate::elaborator::acorn_type::TypeParam;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::goal::Goal;
use crate::kernel::clause::Clause;
use crate::kernel::display::DisplayClause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{
    BooleanReductionInfo, PremiseMap, ProofStep, ProofStepId, Rule, ShallowStatus, Truthiness,
};
use crate::kernel::EqualityGraphContradiction;
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

    /// Prover-owned search context, including any named witness symbols introduced
    /// during existential activation.
    kernel_context: Option<KernelContext>,

    /// Metadata for prover-generated existential witnesses.
    witness_registry: WitnessRegistry,
}

impl Prover {
    fn should_log_boolean_reductions() -> bool {
        env::var_os("ACORN_LOG_BOOLEAN_REDUCTIONS").is_some()
    }

    fn verbose_depth_label(step: &ProofStep) -> String {
        match step.shallow_status {
            ShallowStatus::Unspent => "unspent shallow".to_string(),
            ShallowStatus::Spent => "spent shallow".to_string(),
            ShallowStatus::Contradiction => "shallow".to_string(),
            ShallowStatus::Deep => format!("depth {}", step.depth),
        }
    }

    fn goal_name_for_trace(&self) -> &str {
        self.goal
            .as_ref()
            .map(|goal| goal.name.as_str())
            .unwrap_or("<unset>")
    }

    fn log_boolean_reduction_activation(
        &self,
        step: &ProofStep,
        info: BooleanReductionInfo,
        source_step: &ProofStep,
    ) {
        eprintln!(
            "BOOLEAN_REDUCTION goal={} kind={} step_status={:?} source_status={:?} source_rule={} truthiness={:?}",
            self.goal_name_for_trace(),
            info.kind.as_str(),
            step.shallow_status,
            source_step.shallow_status,
            source_step.rule.name(),
            step.truthiness,
        );
    }

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

    fn bindings_with_goal_type_params<'a>(&self, bindings: &'a BindingMap) -> Cow<'a, BindingMap> {
        let Some(goal) = self.goal.as_ref() else {
            return Cow::Borrowed(bindings);
        };
        Self::bindings_with_type_params(bindings, &goal.proposition.params)
    }

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
            kernel_context: None,
            witness_registry: WitnessRegistry::new(),
        }
    }

    /// Returns an iterator over the active proof steps
    pub fn iter_active_steps(&self) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.active_set.iter_steps()
    }

    pub fn goal_type_params(&self) -> Option<&[TypeParam]> {
        self.goal
            .as_ref()
            .map(|goal| goal.proposition.params.as_slice())
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

    fn clause_text(
        &self,
        clause: &Clause,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
    ) -> String {
        let quoted = kernel_context.quote_clause(clause, None, None, false);
        CodeGenerator::new(bindings)
            .value_to_code(&quoted)
            .unwrap_or_else(|_| {
                format!(
                    "{}",
                    DisplayClause {
                        clause,
                        context: kernel_context
                    }
                )
            })
    }

    /// Formats the verbose search trace for a single goal.
    pub fn format_active_steps(
        &self,
        outcome: Outcome,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
    ) -> String {
        let effective_kernel_context = self.kernel_context.as_ref().unwrap_or(kernel_context);
        let cert_bindings = self.bindings_with_goal_type_params(bindings);
        let mut output = String::new();

        writeln!(output, "search outcome: {}", outcome).unwrap();
        writeln!(
            output,
            "activated {} proof steps ({} non-factual, {} passive remain):",
            self.active_set.len(),
            self.nonfactual_activations,
            self.passive_set.len()
        )
        .unwrap();
        writeln!(output).unwrap();

        for (id, step) in self.iter_active_steps() {
            let clause_text = if step.clause.is_impossible() {
                "contradiction".to_string()
            } else {
                self.clause_text(
                    &step.clause,
                    cert_bindings.as_ref(),
                    effective_kernel_context,
                )
            };
            let depth_label = match step.shallow_origin() {
                Some(origin) => format!("{}, origin {:?}", Self::verbose_depth_label(step), origin),
                None => Self::verbose_depth_label(step),
            };
            let rule_label = match step.underlying_boolean_reduction() {
                Some(info) => format!(
                    "{} [{}]",
                    step.rule.name().to_lowercase(),
                    info.kind.as_str()
                ),
                None => step.rule.name().to_lowercase(),
            };

            writeln!(
                output,
                "Clause {}, {}, {:?}, by {}:",
                id, depth_label, step.truthiness, rule_label
            )
            .unwrap();
            writeln!(output, "    {}", clause_text).unwrap();
            writeln!(output).unwrap();
        }

        if let Some(final_step) = &self.final_step {
            writeln!(
                output,
                "final contradiction, {}, {:?}, by {}:",
                Self::verbose_depth_label(final_step),
                final_step.truthiness,
                final_step.rule.name().to_lowercase()
            )
            .unwrap();
            writeln!(output, "    contradiction").unwrap();

            if matches!(final_step.rule, Rule::PassiveContradiction(_)) {
                writeln!(output).unwrap();
                writeln!(output, "passive contradiction clauses:").unwrap();
                for (i, step) in self.useful_passive.iter().enumerate() {
                    let clause_text = self.clause_text(
                        &step.clause,
                        cert_bindings.as_ref(),
                        effective_kernel_context,
                    );
                    writeln!(output, "    Passive {}: {}", i, clause_text).unwrap();
                }
            }
        }

        output
    }

    /// Prints every activated proof step in activation order.
    pub fn print_active_steps(
        &self,
        outcome: Outcome,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
    ) {
        print!(
            "{}",
            self.format_active_steps(outcome, bindings, kernel_context)
        );
    }

    /// Prints the proof in a human-readable form.
    pub fn print_proof(
        &self,
        proof: &Proof,
        bindings: &BindingMap,
        kernel_context: &KernelContext,
    ) {
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
                let clause_text = self.clause_text(&step.clause, bindings, kernel_context);

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
                    self.clause_text(dep_clause, bindings, kernel_context)
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
        kernel_context: &'a KernelContext,
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
        let mut proof = Proof::new_with_witnesses(kernel_context, Some(&self.witness_registry));
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
        kernel_context: &KernelContext,
        print: bool,
    ) -> Result<Certificate, Error> {
        let goal = self
            .goal
            .as_ref()
            .ok_or_else(|| Error::internal("no goal set"))?;
        let goal_name = goal.name.clone();
        let cert_bindings = self.bindings_with_goal_type_params(bindings);
        let effective_kernel_context = self.kernel_context.as_ref().unwrap_or(kernel_context);

        let proof = self
            .get_proof(effective_kernel_context, false)
            .ok_or_else(|| Error::internal("No proof found"))?;

        if print {
            self.print_proof(&proof, cert_bindings.as_ref(), effective_kernel_context);
        }

        proof.make_cert(goal_name, cert_bindings.as_ref())
    }

    fn report_equality_graph_contradiction(
        &mut self,
        contradiction: EqualityGraphContradiction,
        shallow_status: ShallowStatus,
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
                .any(|t| t.as_ref().is_some_and(|t| t.as_ref().is_type_param_kind()));
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
            let clause = Clause::new(vec![literal], &LocalContext::empty());
            if new_clauses.contains(&clause) {
                // We already created a step for this equality
                // TODO: is it really okay to not insert any sort of id here?
                continue;
            }
            new_clauses.insert(clause.clone());
            let premise_map = PremiseMap::new(
                vec![step.source.pattern_var_map().clone()],
                vec![],
                step.source.pattern_output_context().clone(),
            );
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

        let final_step = ProofStep::multiple_rewrite(
            contradiction.inequality_id,
            active_ids,
            passive_ids,
            truthiness,
            max_depth,
            shallow_status,
        );

        #[cfg(feature = "validate")]
        if let Err(e) = ActiveSet::validate_step_shape(&final_step, kernel_context) {
            panic!(
                "Invalid multiple-rewrite final step: {}\nStep clause: {}",
                e, final_step.clause
            );
        }

        self.final_step = Some(final_step);
    }

    fn report_passive_contradiction(
        &mut self,
        passive_steps: Vec<ProofStep>,
        #[cfg_attr(not(feature = "validate"), allow(unused_variables))]
        kernel_context: &KernelContext,
    ) {
        assert!(self.useful_passive.is_empty());
        for passive_step in passive_steps {
            self.useful_passive.push(passive_step);
        }
        let final_step = ProofStep::passive_contradiction(&self.useful_passive);

        #[cfg(feature = "validate")]
        if let Err(e) = ActiveSet::validate_step_shape(&final_step, kernel_context) {
            panic!(
                "Invalid passive-contradiction final step: {}\nStep clause: {}",
                e, final_step.clause
            );
        }

        self.final_step = Some(final_step);
    }

    fn maybe_finish_with_step(&mut self, step: ProofStep, shallow_only: bool) -> bool {
        if step.finishes_proof() {
            self.final_step = Some(step);
            return true;
        }
        if shallow_only && !step.is_shallow() {
            return false;
        }
        self.final_step = Some(step);
        true
    }

    /// Activates the next clause from the queue, unless we're already done.
    /// Returns whether the prover finished.
    fn activate_next(&mut self, kernel_context: &mut KernelContext, shallow_only: bool) -> bool {
        if self.final_step.is_some() {
            return true;
        }

        if let Some(passive_steps) = self.passive_set.get_contradiction() {
            trace!(
                target: "acorn::prover::activation",
                goal = self.goal_name_for_trace(),
                passive_count = passive_steps.len(),
                "found passive contradiction"
            );
            self.report_passive_contradiction(passive_steps, kernel_context);
            return true;
        }

        let (step, was_shallow) = match self.passive_set.pop_with_shallow() {
            Some(step) => step,
            None => {
                // We're out of clauses to process, so we can't make any more progress.
                trace!(
                    target: "acorn::prover::activation",
                    goal = self.goal_name_for_trace(),
                    "passive set exhausted"
                );
                return true;
            }
        };

        trace!(
            target: "acorn::prover::activation",
            goal = self.goal_name_for_trace(),
            active_id = self.active_set.next_id(),
            shallow = was_shallow,
            shallow_status = ?step.shallow_status,
            depth = step.depth,
            truthiness = ?step.truthiness,
            rule = step.rule.name(),
            clause = %step.clause,
            "activating clause"
        );

        if Self::should_log_boolean_reductions() {
            if let Some(info) = step.underlying_boolean_reduction() {
                let source_step = self.active_set.get_step(info.id);
                self.log_boolean_reduction_activation(&step, info, source_step);
            }
        }

        if step.truthiness != Truthiness::Factual {
            self.nonfactual_activations += 1;
        }

        let finished = if step.clause.is_impossible() {
            self.maybe_finish_with_step(step, shallow_only)
        } else {
            self.activate(step, kernel_context, shallow_only)
        };
        finished
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
    fn activate(
        &mut self,
        activated_step: ProofStep,
        kernel_context: &mut KernelContext,
        shallow_only: bool,
    ) -> bool {
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
        let module_id = self
            .goal
            .as_ref()
            .map(|goal| goal.module_id)
            .unwrap_or_default();
        let (alt_activated_id, generated_steps) = self.active_set.activate(
            activated_step,
            kernel_context,
            &mut self.witness_registry,
            module_id,
        );
        assert_eq!(activated_id, alt_activated_id);

        let mut new_steps = vec![];
        for step in generated_steps {
            if step.finishes_proof() {
                if self.maybe_finish_with_step(step, shallow_only) {
                    return true;
                }
                continue;
            }

            if step.automatic_reject() {
                continue;
            }

            if let Some(simple_step) = self.active_set.simplify(step, kernel_context) {
                if simple_step.clause.is_impossible() {
                    if self.maybe_finish_with_step(simple_step, shallow_only) {
                        return true;
                    }
                    continue;
                }
                new_steps.push(simple_step);
            }
        }
        self.passive_set.push_batch(new_steps, kernel_context);
        if let Some(passive_steps) = self.passive_set.get_contradiction() {
            trace!(
                target: "acorn::prover::activation",
                goal = self.goal_name_for_trace(),
                passive_count = passive_steps.len(),
                "found passive contradiction after push"
            );
            self.report_passive_contradiction(passive_steps, kernel_context);
            return true;
        }

        // Sometimes we find a bunch of contradictions at once.
        // It doesn't really matter what we pick, so we guess which is most likely
        // to be aesthetically pleasing.
        // First regular contradictions (in the loop above), then term graph.

        if let Some(contradiction) = self.active_set.graph.get_contradiction_trace() {
            self.report_equality_graph_contradiction(
                contradiction,
                ShallowStatus::Contradiction,
                kernel_context,
            );
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
        if self.kernel_context.is_none() {
            self.kernel_context = Some(kernel_context.clone());
        }
        self.passive_set.push_batch(steps, kernel_context);
    }

    fn check_shallow_frontier(
        &mut self,
        shallow_only: bool,
        kernel_context: &mut KernelContext,
    ) -> Option<Outcome> {
        if !shallow_only || self.passive_set.can_pop_for_verification() {
            return None;
        }
        if let Some(passive_steps) = self.passive_set.get_contradiction() {
            trace!(
                target: "acorn::prover::activation",
                goal = self.goal_name_for_trace(),
                passive_count = passive_steps.len(),
                "found passive contradiction at shallow frontier"
            );
            self.report_passive_contradiction(passive_steps, kernel_context);
            let final_step = self.final_step.as_ref().unwrap();
            if final_step.truthiness == Truthiness::Counterfactual {
                return Some(Outcome::Success);
            }
            if let Some(goal) = &self.goal {
                if goal.inconsistency_okay {
                    return Some(Outcome::Success);
                }
            }
            return Some(Outcome::Inconsistent);
        }
        trace!(
            target: "acorn::prover::activation",
            goal = self.goal_name_for_trace(),
            active_count = self.active_set.len(),
            passive_count = self.passive_set.len(),
            "stopping at shallow frontier"
        );
        Some(Outcome::ShallowExhausted)
    }

    /// Search stops for one of five reasons:
    ///   Succeeding or finding an inconsistency
    ///   Exhausting the shallow fragment in test mode
    ///   Exhausting the full passive set in interactive mode
    ///   Hitting the activation cap, either shallow or regular
    ///   Going over the time limit
    pub fn search(&mut self, mode: ProverMode, kernel_context: &KernelContext) -> Outcome {
        let mut search_kernel_context = self
            .kernel_context
            .take()
            .unwrap_or_else(|| kernel_context.clone());
        let outcome = self.search_with_context(mode, &mut search_kernel_context);
        self.kernel_context = Some(search_kernel_context);
        outcome
    }

    /// Run proof search against the prover-owned mutable kernel context snapshot.
    fn search_with_context(
        &mut self,
        mode: ProverMode,
        kernel_context: &mut KernelContext,
    ) -> Outcome {
        // Convert mode to actual parameters
        let (activation_limit, seconds, shallow_only) = match mode {
            ProverMode::Interactive {
                timeout_secs,
                activation_limit,
            } => (activation_limit, timeout_secs, false),
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
            if let Some(outcome) = self.check_shallow_frontier(shallow_only, kernel_context) {
                return outcome;
            }
            if self.activate_next(kernel_context, shallow_only) {
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
            if let Some(outcome) = self.check_shallow_frontier(shallow_only, kernel_context) {
                return outcome;
            }
            if self.passive_set.is_empty() {
                return Outcome::Exhausted;
            }
            if self.nonfactual_activations >= activation_limit {
                if self.passive_set.can_pop_for_verification() {
                    return Outcome::ShallowExplosion;
                }
                return Outcome::ActivationCap;
            }
            let elapsed = start_time.elapsed().as_secs_f32();
            if elapsed >= seconds {
                return Outcome::Timeout;
            }
        }
    }

    pub fn set_goal(&mut self, goal: Goal, steps: Vec<ProofStep>, kernel_context: &KernelContext) {
        assert!(self.goal.is_none());
        self.kernel_context = Some(kernel_context.clone());
        self.add_steps(steps, kernel_context);
        self.goal = Some(goal);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::equality_graph::{RewriteSource, RewriteStep, StepId};
    use crate::module::ModuleId;

    #[test]
    fn test_multiple_rewrite_specialization_uses_saved_map() {
        let mut kernel_context = KernelContext::new();
        kernel_context
            .parse_constants(&["c0", "c1", "c2"], "Bool")
            .parse_constants(&["g0", "g1"], "Bool -> Bool");

        let pattern_clause = kernel_context.parse_clause(
            "ite(Bool, eq(Bool, x0, c0), c1, g0(x0)) = g1(x0)",
            &["Bool"],
        );
        let pattern_step = ProofStep::mock_from_clause(pattern_clause);

        let inequality_clause =
            kernel_context.parse_clause("ite(Bool, eq(Bool, c0, c2), c1, g0(c2)) != g1(c2)", &[]);
        let mut inequality_step = ProofStep::mock_from_clause(inequality_clause.clone());
        inequality_step.truthiness = Truthiness::Counterfactual;

        let mut prover = Prover::new(vec![]);
        prover.active_set.activate(
            pattern_step,
            &mut kernel_context,
            &mut prover.witness_registry,
            ModuleId::default(),
        );
        prover.active_set.activate(
            inequality_step,
            &mut kernel_context,
            &mut prover.witness_registry,
            ModuleId::default(),
        );

        let left_term = inequality_clause.literals[0].left.clone();
        let right_term = inequality_clause.literals[0].right.clone();
        let left_id = prover
            .active_set
            .graph
            .insert_term(&left_term, &kernel_context);
        let right_id = prover
            .active_set
            .graph
            .insert_term(&right_term, &kernel_context);
        let mut pattern_var_map = crate::kernel::variable_map::VariableMap::new();
        pattern_var_map.set(0, kernel_context.parse_term("c2"));

        let contradiction = EqualityGraphContradiction {
            inequality_id: 1,
            rewrite_chain: vec![RewriteStep {
                source: RewriteSource::new(
                    StepId(0),
                    Some(StepId(1)),
                    left_id,
                    right_id,
                    pattern_var_map,
                    LocalContext::empty(),
                ),
                input_term: left_term,
                output_term: right_term,
                forwards: true,
            }],
        };

        prover.report_equality_graph_contradiction(
            contradiction,
            ShallowStatus::Contradiction,
            &kernel_context,
        );

        let specialization = prover
            .useful_passive
            .first()
            .expect("expected a specialization step for the concrete rewrite");
        let expected =
            kernel_context.parse_clause("ite(Bool, eq(Bool, c0, c2), c1, g0(c2)) = g1(c2)", &[]);
        assert_eq!(specialization.clause, expected);
        prover
            .active_set
            .validate_step(specialization, &kernel_context)
            .expect("stored specialization map should validate");
    }

    #[test]
    fn test_print_active_steps_uses_search_kernel_context_for_named_witnesses() {
        let stale_kernel_context = KernelContext::new();
        let mut search_kernel_context = KernelContext::new();

        let source_clause = Clause::new(
            vec![crate::kernel::literal::Literal::positive(
                crate::kernel::term::Term::exists(
                    crate::kernel::term::Term::bool_type(),
                    crate::kernel::term::Term::not(crate::kernel::term::Term::eq(
                        crate::kernel::term::Term::bool_type(),
                        crate::kernel::term::Term::atom(crate::kernel::atom::Atom::BoundVariable(
                            0,
                        )),
                        crate::kernel::term::Term::new_true(),
                    )),
                ),
            )],
            &LocalContext::empty(),
        );
        let source_step = ProofStep::mock_from_clause(source_clause.clone());

        let mut prover = Prover::new(vec![]);
        let exists_reduction = source_clause
            .positive_exists_reduction(&search_kernel_context)
            .expect("expected positive exists reduction");
        let opening = prover.witness_registry.open_positive_exists(
            &mut search_kernel_context,
            ModuleId::default(),
            &source_clause,
            &exists_reduction,
        );
        let reduction = opening.reduction;
        let witness_step = ProofStep::direct(
            &source_step,
            Rule::BooleanReduction(crate::kernel::proof_step::BooleanReductionInfo {
                id: 0,
                kind: crate::kernel::clause::BooleanReductionKind::PositiveExistsOpen,
            }),
            reduction.clause,
            PremiseMap::new(
                vec![crate::kernel::variable_map::VariableMap::new()],
                reduction.var_ids,
                reduction.pre_norm_context,
            ),
        );
        prover.active_set.activate(
            witness_step,
            &mut search_kernel_context,
            &mut prover.witness_registry,
            ModuleId::default(),
        );
        prover.kernel_context = Some(search_kernel_context);

        let bindings = BindingMap::new(ModuleId::default());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prover.print_active_steps(Outcome::Success, &bindings, &stale_kernel_context);
        }));
        assert!(
            result.is_ok(),
            "print_active_steps should quote named witnesses with the prover-owned search context"
        );
    }

    #[test]
    fn test_format_active_steps_shows_passive_contradiction_clauses() {
        let kernel_context = KernelContext::new();

        let positive = ProofStep::mock("true = false", &kernel_context);
        let negative = ProofStep::mock("true != false", &kernel_context);
        let final_step = ProofStep::passive_contradiction(&[positive.clone(), negative.clone()]);

        let mut prover = Prover::new(vec![]);
        prover.useful_passive = vec![positive, negative];
        prover.final_step = Some(final_step);

        let bindings = BindingMap::new(ModuleId::default());
        let formatted = prover.format_active_steps(Outcome::Success, &bindings, &kernel_context);

        assert!(formatted.contains("search outcome: Success"));
        assert!(formatted.contains("final contradiction, shallow"));
        assert!(formatted.contains("passive contradiction clauses:"));
        assert!(formatted.contains("Passive 0: false = true"));
        assert!(formatted.contains("Passive 1: not false"));
    }

    #[test]
    fn test_format_active_steps_labels_shallow_activated_steps() {
        let mut kernel_context = KernelContext::new();
        let step = ProofStep::mock("true = false", &kernel_context);

        let mut prover = Prover::new(vec![]);
        prover.active_set.activate(
            step,
            &mut kernel_context,
            &mut prover.witness_registry,
            ModuleId::default(),
        );

        let bindings = BindingMap::new(ModuleId::default());
        let formatted =
            prover.format_active_steps(Outcome::ShallowExhausted, &bindings, &kernel_context);

        assert!(formatted.contains("Clause 0, unspent shallow, Factual, by assumption:"));
        assert!(!formatted.contains("Clause 0, depth 0, Factual, by assumption:"));
    }

    #[test]
    fn test_format_active_steps_labels_spent_shallow_activated_steps() {
        let mut kernel_context = KernelContext::new();
        let mut step = ProofStep::mock("true = false", &kernel_context);
        step.shallow_status = ShallowStatus::Spent;

        let mut prover = Prover::new(vec![]);
        prover.active_set.activate(
            step,
            &mut kernel_context,
            &mut prover.witness_registry,
            ModuleId::default(),
        );

        let bindings = BindingMap::new(ModuleId::default());
        let formatted =
            prover.format_active_steps(Outcome::ShallowExhausted, &bindings, &kernel_context);

        assert!(formatted.contains("Clause 0, spent shallow, Factual, by assumption:"));
    }

    #[test]
    fn test_search_returns_shallow_explosion_when_activation_cap_hits_in_shallow_fragment() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1", "c2"], "Bool");

        let mut step1 = ProofStep::mock("c0 = c1", &kernel_context);
        step1.truthiness = Truthiness::Counterfactual;
        let mut step2 = ProofStep::mock("c1 = c2", &kernel_context);
        step2.truthiness = Truthiness::Counterfactual;

        let mut prover = Prover::new(vec![]);
        prover.add_steps(vec![step1, step2], &kernel_context);

        let outcome = prover.search_with_context(
            ProverMode::Interactive {
                timeout_secs: 1.0,
                activation_limit: 1,
            },
            &mut kernel_context,
        );

        assert_eq!(outcome, Outcome::ShallowExplosion);
    }

    #[test]
    fn test_search_returns_activation_cap_after_leaving_shallow_fragment() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1", "c2"], "Bool");

        let mut step1 = ProofStep::mock("c0 = c1", &kernel_context);
        step1.truthiness = Truthiness::Counterfactual;
        step1.shallow_status = ShallowStatus::Deep;
        let mut step2 = ProofStep::mock("c1 = c2", &kernel_context);
        step2.truthiness = Truthiness::Counterfactual;
        step2.shallow_status = ShallowStatus::Deep;

        let mut prover = Prover::new(vec![]);
        prover.add_steps(vec![step1, step2], &kernel_context);

        let outcome = prover.search_with_context(
            ProverMode::Interactive {
                timeout_secs: 1.0,
                activation_limit: 1,
            },
            &mut kernel_context,
        );

        assert_eq!(outcome, Outcome::ActivationCap);
    }
}
