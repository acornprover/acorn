use std::collections::HashSet;

use im::HashMap as ImHashMap;
use im::HashSet as ImHashSet;
use im::Vector as ImVector;

use crate::code_generator::Error;
use crate::elaborator::source::Source;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::CertificateStep;
use crate::kernel::clause::BooleanReductionKind;
use crate::kernel::clause::{Clause, NormalizedClauseTrace};
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::Rule;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_clause_subterms;
use crate::kernel::{EqualityGraph, StepId};
use tracing::trace;

/// The reason why a certificate step was accepted.
#[derive(Debug, Clone)]
pub enum StepReason {
    /// Proven by the term graph (concrete reasoning via congruence closure and propositional logic).
    EqualityGraph,

    /// An assumption based on normalizing a statement elsewhere in the code.
    /// The source points to the location of the assumption.
    Assumption(Source),

    /// A let...satisfy statement that skolemizes an exists statement.
    /// The source points to where the exists was originally defined.
    Skolemization(Source),

    /// A witness declaration accepted from a previously proven existential.
    WitnessDeclaration,
    /// The checker already had a contradiction, so everything is trivially true.
    Contradiction,

    /// A claim statement from a previous certificate step.
    PreviousClaim,

    /// A clause inserted during testing.
    Testing,

    /// Proven by a single step of equality resolution, based on the given step id
    EqualityResolution(usize),

    /// Proven by extensionality, based on the given step id
    Extensionality(usize),

    /// Proven by equality factoring, based on the given step id
    EqualityFactoring(usize),

    /// Proven by injectivity, based on the given step id
    Injectivity(usize),

    /// Proven by boolean reduction, based on the given step id
    BooleanReduction(usize),
}

impl StepReason {
    pub fn description(&self) -> String {
        match self {
            StepReason::EqualityGraph => "simplification".to_string(),
            StepReason::Assumption(source) | StepReason::Skolemization(source) => {
                source.description()
            }
            StepReason::WitnessDeclaration => "witness declaration".to_string(),
            StepReason::Contradiction => "ex falso".to_string(),
            StepReason::PreviousClaim => "previous claim".to_string(),
            StepReason::Testing => "testing".to_string(),
            StepReason::EqualityResolution(_) => "equality resolution".to_string(),
            StepReason::Extensionality(_) => "extensionality".to_string(),
            StepReason::EqualityFactoring(_) => "equality factoring".to_string(),
            StepReason::Injectivity(_) => "injectivity".to_string(),
            StepReason::BooleanReduction(_) => "boolean reduction".to_string(),
        }
    }

    pub fn dependency(&self) -> Option<usize> {
        match self {
            StepReason::EqualityResolution(step_id)
            | StepReason::Extensionality(step_id)
            | StepReason::EqualityFactoring(step_id)
            | StepReason::Injectivity(step_id)
            | StepReason::BooleanReduction(step_id) => Some(*step_id),
            _ => None,
        }
    }
}

/// A checked certificate claim in kernel terms.
#[derive(Debug, Clone)]
pub struct CheckedStep {
    /// The claim clause as checked by the kernel.
    pub clause: Clause,

    /// The reason this step was accepted.
    pub reason: StepReason,

    /// The original certificate code line for this step, when available.
    pub code_line: Option<String>,

    /// Prefer the original code line over reconstructed code for display.
    pub prefer_code_line: bool,
}

/// A clause inserted into the legacy checker, together with the reason used for dependency IDs.
#[derive(Debug, Clone)]
pub struct InsertedClause {
    pub clause: Clause,
    pub reason: StepReason,
}

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
///
/// The types of single-step we support are:
///
///   Substitutions into a known theorem (or exact variable-clause matches for variable clauses).
///   "Congruence closure" of equalities and subterm relationships. Handled by the EqualityGraph.
///   Propositional calculus on concrete literals. Handled by the EqualityGraph.
///   Introducing variables for existential quantifiers during clausification.
#[derive(Clone)]
pub struct Checker {
    /// For deductions among concrete clauses.
    term_graph: EqualityGraph,

    /// Clauses are matched by exact normalized equality only.
    /// The `usize` value is the `step_id` (index into `self.reasons`) for that clause.
    exact_clauses: ImHashMap<Clause, usize>,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,

    /// The concrete-fact generation at which each variable clause was last expanded.
    variable_clause_generations: ImHashMap<Clause, u64>,

    /// Increments whenever a new concrete clause is added to the equality graph.
    concrete_generation: u64,

    /// A hack, but we need to break out of loops, since equality factoring and boolean
    /// reduction can create cycles.
    past_boolean_reductions: ImHashSet<Clause>,

    /// Types that previous certificate steps established as inhabited.
    proven_inhabited: HashSet<(Term, LocalContext)>,

    /// The reason for each step. The step_id is the index in this vector.
    reasons: ImVector<StepReason>,

    /// Clauses inserted into the checker, indexed in parallel with `reasons`.
    inserted_clauses: ImVector<Clause>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker {
            term_graph: EqualityGraph::new(),
            exact_clauses: ImHashMap::new(),
            direct_contradiction: false,
            variable_clause_generations: ImHashMap::new(),
            concrete_generation: 0,
            past_boolean_reductions: ImHashSet::new(),
            proven_inhabited: HashSet::new(),
            reasons: ImVector::new(),
            inserted_clauses: ImVector::new(),
        }
    }

    fn inhabited_type_key(var_type: &Term, context: &LocalContext) -> (Term, LocalContext) {
        let mut normalized_type = var_type.clone();
        let mut var_ids = Vec::new();
        normalized_type.normalize_var_ids_with_context(&mut var_ids, context);
        (normalized_type, context.remap(&var_ids))
    }

    fn inhabited_type_from_clause(
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<(Term, LocalContext)> {
        let reduction = clause.positive_exists_witness_reduction(kernel_context)?;
        Some(Self::inhabited_type_key(
            &reduction.binder_type,
            clause.get_local_context(),
        ))
    }

    fn mark_inhabited_from_clause(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<(Term, LocalContext)> {
        let Some(key) = Self::inhabited_type_from_clause(clause, kernel_context) else {
            return None;
        };
        self.proven_inhabited.insert(key.clone()).then_some(key)
    }

    fn negated_exists_true_type_from_clause(clause: &Clause) -> Option<(Term, LocalContext)> {
        if clause.literals.len() != 1 {
            return None;
        }
        let literal = clause.literals.first()?;
        if literal.positive || !literal.right.is_true() {
            return None;
        }
        let (binder_type, body) = literal.left.as_ref().split_exists()?;
        if !body.is_true() {
            return None;
        }
        Some(Self::inhabited_type_key(
            &binder_type.to_owned(),
            clause.get_local_context(),
        ))
    }

    fn has_negated_exists_true_for(&self, key: &(Term, LocalContext)) -> bool {
        self.exact_clauses
            .keys()
            .any(|clause| Self::negated_exists_true_type_from_clause(clause).as_ref() == Some(key))
    }

    fn provably_inhabited_for_elimination(
        kernel_context: &KernelContext,
        var_type: &Term,
        local_context: Option<&LocalContext>,
    ) -> bool {
        kernel_context.provably_inhabited_without_local_elements(var_type, local_context)
    }

    /// A normalized derived clause is only sound when every variable erased by normalization
    /// ranges over a type we can constructively prove inhabited.
    fn eliminated_vars_inhabited(
        &self,
        trace: &NormalizedClauseTrace,
        kernel_context: &KernelContext,
    ) -> bool {
        for var_id in 0..trace.pre_norm_context.len() {
            let var_id_atom = var_id as AtomId;
            if trace.var_ids.contains(&var_id_atom) {
                continue;
            }
            let Some(var_type) = trace.pre_norm_context.get_var_type(var_id) else {
                continue;
            };
            let proven_inhabited = self
                .proven_inhabited
                .contains(&Self::inhabited_type_key(var_type, &trace.pre_norm_context));
            if !proven_inhabited
                && !Self::provably_inhabited_for_elimination(
                    kernel_context,
                    var_type,
                    Some(&trace.pre_norm_context),
                )
            {
                return false;
            }
        }
        true
    }

    fn normalize_checker_trace(
        &self,
        trace: &NormalizedClauseTrace,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        if !self.eliminated_vars_inhabited(trace, kernel_context) {
            return None;
        }

        let subterm_normalized = normalize_clause_subterms(&trace.clause);
        let subterm_context = subterm_normalized.get_local_context().clone();
        let first = Clause::normalize_with_trace(subterm_normalized.literals, &subterm_context);
        if !self.eliminated_vars_inhabited(&first, kernel_context) {
            return None;
        }
        let first_context = first.clause.get_local_context().clone();
        let second = Clause::normalize_with_trace(first.clause.literals, &first_context);
        if !self.eliminated_vars_inhabited(&second, kernel_context) {
            return None;
        }
        Some(second.clause)
    }

    fn checker_boolean_reductions(
        &self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Vec<Clause> {
        clause
            .find_boolean_reduction_kinds_with_options(kernel_context, true)
            .into_iter()
            .filter_map(|(_kind, trace)| {
                if self.past_boolean_reductions.contains(&trace.clause) {
                    None
                } else {
                    self.normalize_checker_trace(&trace, kernel_context)
                }
            })
            .collect()
    }

    fn checker_boolean_reduction_sets(
        &self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Vec<Vec<Clause>> {
        use BooleanReductionKind::*;

        let reductions = clause.find_boolean_reduction_kinds_with_options(kernel_context, true);

        let mut sets = Vec::new();
        let mut index = 0;
        while index < reductions.len() {
            let (kind, trace) = &reductions[index];
            let next = reductions.get(index + 1);
            let paired = match (kind, next.map(|(kind, _)| kind)) {
                (IteSplitLeftThenBranch, Some(IteSplitLeftElseBranch))
                | (IteSplitRightThenBranch, Some(IteSplitRightElseBranch))
                | (PositiveAndLeft, Some(PositiveAndRight))
                | (NegativeOrLeft, Some(NegativeOrRight))
                | (BooleanEqualityLeftOrNotRight, Some(BooleanEqualityNotLeftOrRight))
                | (BooleanInequalityNotLeftOrNotRight, Some(BooleanInequalityLeftOrRight)) => true,
                _ => false,
            };

            if paired {
                let (_, next_trace) = &reductions[index + 1];
                if let (Some(clause), Some(next_clause)) = (
                    self.normalize_checker_trace(trace, kernel_context),
                    self.normalize_checker_trace(next_trace, kernel_context),
                ) {
                    sets.push(vec![clause, next_clause]);
                }
                index += 2;
                continue;
            }

            let is_second_half = matches!(
                kind,
                IteSplitLeftElseBranch
                    | IteSplitRightElseBranch
                    | PositiveAndRight
                    | NegativeOrRight
                    | BooleanEqualityNotLeftOrRight
                    | BooleanInequalityLeftOrRight
            );
            if !is_second_half {
                if let Some(clause) = self.normalize_checker_trace(trace, kernel_context) {
                    sets.push(vec![clause]);
                }
            }
            index += 1;
        }

        sets
    }

    fn insert_boolean_reductions_with_reason(
        &mut self,
        clause: &Clause,
        step_id: usize,
        kernel_context: &KernelContext,
    ) {
        if !Self::clause_symbols_available(clause, kernel_context) {
            return;
        }
        for boolean_reduction in self.checker_boolean_reductions(clause, kernel_context) {
            // Guard against infinite loops
            if self.past_boolean_reductions.contains(&boolean_reduction) {
                continue;
            }
            self.past_boolean_reductions
                .insert(boolean_reduction.clone());
            self.insert_clause_internal(
                &boolean_reduction,
                StepReason::BooleanReduction(step_id),
                kernel_context,
            );
        }
    }

    fn reprocess_boolean_reductions(&mut self, kernel_context: &KernelContext) {
        let clauses: Vec<(Clause, usize)> = self
            .exact_clauses
            .iter()
            .map(|(clause, step_id)| (clause.clone(), *step_id))
            .collect();
        for (clause, step_id) in clauses {
            self.insert_boolean_reductions_with_reason(&clause, step_id, kernel_context);
        }
    }

    fn term_symbols_available(term: &Term, kernel_context: &KernelContext) -> bool {
        term.iter_atoms().all(|atom| match atom {
            Atom::Symbol(symbol) => kernel_context.symbol_table.contains_symbol(*symbol),
            Atom::FreeVariable(_) | Atom::BoundVariable(_) => true,
        })
    }

    fn clause_symbols_available(clause: &Clause, kernel_context: &KernelContext) -> bool {
        clause
            .get_local_context()
            .get_var_types()
            .iter()
            .all(|var_type| {
                var_type
                    .as_ref()
                    .is_none_or(|term| Self::term_symbols_available(term, kernel_context))
            })
            && clause.iter_atoms().all(|atom| match atom {
                Atom::Symbol(symbol) => kernel_context.symbol_table.contains_symbol(*symbol),
                Atom::FreeVariable(_) | Atom::BoundVariable(_) => true,
            })
    }

    fn insert_clause_internal(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        trace!(clause = %clause, reason = ?reason.description(), "inserting clause");

        if clause.is_impossible() {
            self.direct_contradiction = true;
            return;
        }

        let has_any_variable = clause.has_any_variable();
        if has_any_variable {
            if self
                .variable_clause_generations
                .get(clause)
                .is_some_and(|generation| *generation == self.concrete_generation)
            {
                return;
            }
            self.variable_clause_generations
                .insert(clause.clone(), self.concrete_generation);
        } else if self.exact_clauses.contains_key(clause) {
            return;
        }

        let step_id = self.reasons.len();
        self.reasons.push_back(reason.clone());
        self.inserted_clauses.push_back(clause.clone());

        self.exact_clauses.entry(clause.clone()).or_insert(step_id);

        let should_reprocess_for_inhabitedness = matches!(
            &reason,
            StepReason::PreviousClaim | StepReason::WitnessDeclaration | StepReason::Testing
        );
        if let Some(key) = Self::negated_exists_true_type_from_clause(clause) {
            if self.proven_inhabited.contains(&key) {
                self.direct_contradiction = true;
            }
        }

        if let Some(key) = self.mark_inhabited_from_clause(clause, kernel_context) {
            if self.has_negated_exists_true_for(&key) {
                self.direct_contradiction = true;
            }
            if should_reprocess_for_inhabitedness {
                self.reprocess_boolean_reductions(kernel_context);
            }
        }

        if has_any_variable {
            if let Some(reduced_clause) =
                self.simplify_variable_clause_with_concrete_facts(clause, kernel_context)
            {
                self.insert_clause_internal(
                    &reduced_clause,
                    StepReason::EqualityGraph,
                    kernel_context,
                );
            }

            // We only need to do equality resolution for clauses with free variables,
            // because resolvable concrete literals would already have been simplified out.
            for (literals, context, _) in
                inference::find_equality_resolutions(clause, kernel_context)
            {
                let trace = Clause::normalize_with_trace(literals, &context);
                let Some(resolution) = self.normalize_checker_trace(&trace, kernel_context) else {
                    continue;
                };
                if resolution.is_tautology() {
                    continue;
                }
                self.insert_clause_internal(
                    &resolution,
                    StepReason::EqualityResolution(step_id),
                    kernel_context,
                );
            }

            if let Some(extensionality) = clause.find_extensionality(kernel_context) {
                let ext_clause = Clause::new(extensionality, clause.get_local_context());
                self.insert_clause_internal(
                    &ext_clause,
                    StepReason::Extensionality(step_id),
                    kernel_context,
                );
            }
        } else {
            // The clause is concrete.
            self.concrete_generation += 1;
            self.term_graph
                .insert_clause(clause, StepId(step_id), kernel_context);
        }

        for (literals, context, _) in inference::find_equality_factorings(clause, kernel_context) {
            let trace = Clause::normalize_with_trace(literals, &context);
            let Some(factoring) = self.normalize_checker_trace(&trace, kernel_context) else {
                continue;
            };
            if factoring.is_tautology() {
                continue;
            }
            self.insert_clause_internal(
                &factoring,
                StepReason::EqualityFactoring(step_id),
                kernel_context,
            );
        }

        for literals in clause.find_injectivities() {
            let trace = Clause::normalize_with_trace(literals, clause.get_local_context());
            let Some(injectivity) = self.normalize_checker_trace(&trace, kernel_context) else {
                continue;
            };
            if injectivity.is_tautology() {
                continue;
            }
            self.insert_clause_internal(
                &injectivity,
                StepReason::Injectivity(step_id),
                kernel_context,
            );
        }

        self.insert_boolean_reductions_with_reason(clause, step_id, kernel_context);
    }

    /// Adds a true clause to the checker with a specific reason.
    pub fn insert_clause(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        let clause = normalize_clause_subterms(clause).normalized();
        self.insert_clause_internal(&clause, reason, kernel_context);
    }

    /// Adds a true clause that was already normalized while lowering.
    pub fn insert_normalized_clause(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        debug_assert_eq!(
            normalize_clause_subterms(clause).normalized(),
            *clause,
            "insert_normalized_clause called with an unnormalized clause"
        );
        self.insert_clause_internal(clause, reason, kernel_context);
    }

    /// Checks if a clause is known to be true, and returns the reason if so.
    /// Returns None if the clause cannot be proven.
    fn check_clause_direct(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        debug_assert!(clause.is_normalized());
        if self.has_contradiction() {
            trace!(clause = %clause, result = "contradiction", "checking clause");
            return Some(StepReason::Contradiction);
        }

        // Check the term graph for concrete evaluation
        if self.term_graph.check_clause(clause, kernel_context) {
            trace!(clause = %clause, result = "term_graph", "checking clause");
            return Some(StepReason::EqualityGraph);
        }

        if let Some(step_id) = self.exact_clauses.get(clause) {
            trace!(
                clause = %clause,
                result = "exact_clause",
                "checking clause"
            );
            return Some(self.reasons[*step_id].clone());
        }

        trace!(clause = %clause, result = "failed", "checking clause");
        None
    }

    fn check_clause_via_boolean_reductions(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        let mut seen = HashSet::new();
        self.check_clause_via_boolean_reductions_inner(clause, kernel_context, &mut seen)
    }

    fn check_clause_via_boolean_reductions_inner(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
        seen: &mut HashSet<Clause>,
    ) -> Option<StepReason> {
        if clause.has_any_variable() || !seen.insert(clause.clone()) {
            return None;
        }

        for reduction_set in self.checker_boolean_reduction_sets(clause, kernel_context) {
            let mut first_reason = None;
            let mut set_seen = seen.clone();
            let mut all_known = true;

            for candidate in reduction_set {
                let reason = self
                    .check_clause_direct(&candidate, kernel_context)
                    .or_else(|| {
                        self.check_clause_via_boolean_reductions_inner(
                            &candidate,
                            kernel_context,
                            &mut set_seen,
                        )
                    });

                if let Some(reason) = reason {
                    if first_reason.is_none() {
                        first_reason = Some(reason);
                    }
                } else {
                    all_known = false;
                    break;
                }
            }

            if all_known {
                return first_reason.or(Some(StepReason::EqualityGraph));
            }
        }

        None
    }

    /// Checks if a clause is known to be true, and returns the reason if so.
    /// Returns None if the clause cannot be proven.
    pub fn check_clause(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        let clause = normalize_clause_subterms(clause).normalized();
        self.check_clause_direct(&clause, kernel_context)
            .or_else(|| self.check_clause_via_boolean_reductions(&clause, kernel_context))
    }

    pub fn inserted_len(&self) -> usize {
        self.inserted_clauses.len()
    }

    pub fn inserted_clause(&self, id: usize) -> Option<InsertedClause> {
        Some(InsertedClause {
            clause: self.inserted_clauses.get(id)?.clone(),
            reason: self.reasons.get(id)?.clone(),
        })
    }

    pub fn exact_clause_id(&self, clause: &Clause) -> Option<usize> {
        self.exact_clauses.get(clause).copied()
    }

    fn simplify_variable_clause_with_concrete_facts(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let mut changed = false;
        let mut reduced_literals = Vec::with_capacity(clause.literals.len());
        for literal in &clause.literals {
            match self.term_graph.evaluate_literal(literal, kernel_context) {
                Some(true) => return None,
                Some(false) => changed = true,
                None => reduced_literals.push(literal.clone()),
            }
        }
        if !changed {
            return None;
        }
        Some(Clause::new(reduced_literals, clause.get_local_context()))
    }

    /// Returns true if the checker has encountered a contradiction.
    ///
    /// It is possible that both a clause and its negation are known to be true, and yet
    /// has_contradiction returns false.
    /// This is because we do not unify all terms we ever encounter.
    ///
    /// We do guarantee that if you insert both a term and its negation then
    /// has_contradiction will return true.
    pub fn has_contradiction(&self) -> bool {
        self.direct_contradiction || self.term_graph.has_contradiction()
    }

    /// Insert goal clauses into the checker.
    /// Normalizes the goal and inserts all resulting clauses as assumptions.
    pub fn insert_goal(
        &mut self,
        goal: &crate::elaborator::goal::Goal,
        kernel_context: &mut crate::kernel::kernel_context::KernelContext,
    ) -> Result<(), Error> {
        trace!("inserting goal {} (line {})", goal.name, goal.first_line);

        let source = &goal.proposition.source;
        let lowered =
            crate::elaborator::lowering::lower_goal(kernel_context, goal).map_err(|e| e.message)?;
        // Use the post-lowering kernel context, since lowering the goal may register
        // additional symbols and type metadata.
        let kernel_context = kernel_context;
        for step in &lowered.steps {
            // Use the step's own source if it's an assumption (which includes negated goals),
            // otherwise use the goal's source
            let step_source = if let Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source.clone()),
                kernel_context,
            );
        }
        Ok(())
    }

    /// Insert pre-lowered goal clauses into the checker.
    /// Uses the provided lowered goal (including its kernel context state).
    pub fn insert_lowered_goal(
        &mut self,
        normalized: &crate::elaborator::lowering::LoweredGoal,
    ) -> Result<(), Error> {
        trace!(
            "inserting lowered goal {} (line {})",
            normalized.goal.name,
            normalized.goal.first_line
        );

        let source = &normalized.goal.proposition.source;
        let kernel_context = &normalized.kernel_context;
        for step in &normalized.steps {
            let step_source = if let Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source.clone()),
                kernel_context,
            );
        }
        Ok(())
    }

    /// Check already-parsed certificate steps.
    pub fn check_cert_steps(
        &mut self,
        cert_steps: &[CertificateStep],
        code_lines: Option<&[String]>,
        kernel_context: &KernelContext,
    ) -> Result<(Vec<CheckedStep>, usize), Error> {
        let mut checked_steps = Vec::new();
        let mut seen_claims = HashSet::new();
        let mut witness_validation_context = kernel_context.clone();

        for (step_index, step) in cert_steps.iter().enumerate() {
            if self.has_contradiction() {
                trace!("has_contradiction (early exit)");
                return Ok((checked_steps, step_index));
            }

            #[cfg(feature = "validate")]
            step.validate_normalized_shape(kernel_context)
                .map_err(Error::GeneratedBadCode)?;

            match step {
                CertificateStep::Claim(claim) => {
                    claim
                        .validate_checker_payload(kernel_context)
                        .map_err(Error::GeneratedBadCode)?;

                    let generic_clause = claim.normalized_generic_clause();
                    let clause = Self::instantiate_claim_clause(claim, kernel_context)?;
                    if !seen_claims.insert(clause.clone()) {
                        continue;
                    }

                    let reason = self
                        .check_clause(&generic_clause, &kernel_context)
                        .or_else(|| self.check_clause(&clause, &kernel_context));

                    let Some(reason) = reason else {
                        let cert_line_context = code_lines
                            .and_then(|lines| lines.get(step_index))
                            .map(|line| {
                                format!("; certificate line {}: {:?}", step_index + 1, line)
                            })
                            .unwrap_or_default();
                        return Err(Error::GeneratedBadCode(format!(
                            "Claim at step {} is not obviously true{} (generic debug: {:?}; specialized debug: {:?})",
                            step_index + 1,
                            cert_line_context,
                            claim.clause(),
                            clause,
                        )));
                    };

                    checked_steps.push(CheckedStep {
                        clause: clause.clone(),
                        reason,
                        code_line: code_lines.and_then(|lines| lines.get(step_index)).cloned(),
                        prefer_code_line: false,
                    });

                    self.insert_clause(&generic_clause, StepReason::PreviousClaim, &kernel_context);
                    self.insert_clause(&clause, StepReason::PreviousClaim, &kernel_context);
                }
                CertificateStep::Satisfy(step) => {
                    step.validate_checker_payload(&mut witness_validation_context)
                        .map_err(Error::GeneratedBadCode)?;

                    let generic_clause = step.justification.normalized_generic_clause();
                    let justification_clause =
                        Self::instantiate_claim_clause(&step.justification, kernel_context)?;
                    let justification_ok = self
                        .check_clause(&generic_clause, kernel_context)
                        .or_else(|| self.check_clause(&justification_clause, kernel_context))
                        .is_some();
                    if !justification_ok {
                        let cert_line_context = code_lines
                            .and_then(|lines| lines.get(step_index))
                            .map(|line| {
                                format!("; certificate line {}: {:?}", step_index + 1, line)
                            })
                            .unwrap_or_default();
                        return Err(Error::GeneratedBadCode(format!(
                            "Witness declaration at step {} is not obviously true{} (missing implicit existential {:?})",
                            step_index + 1,
                            cert_line_context,
                            justification_clause,
                        )));
                    }

                    self.insert_clause(
                        &generic_clause,
                        StepReason::WitnessDeclaration,
                        kernel_context,
                    );
                    self.insert_clause(
                        &justification_clause,
                        StepReason::WitnessDeclaration,
                        kernel_context,
                    );
                    if let Some(specialized_clause) = &step.specialized_clause {
                        self.insert_clause(
                            specialized_clause,
                            StepReason::WitnessDeclaration,
                            kernel_context,
                        );
                    }
                    for clause in &step.witness_clauses {
                        self.insert_clause(clause, StepReason::WitnessDeclaration, kernel_context);
                    }

                    checked_steps.push(CheckedStep {
                        clause: justification_clause,
                        reason: StepReason::WitnessDeclaration,
                        code_line: code_lines.and_then(|lines| lines.get(step_index)).cloned(),
                        prefer_code_line: true,
                    });
                }
            }
        }

        if self.has_contradiction() {
            trace!("has_contradiction (end of proof)");
            Ok((checked_steps, cert_steps.len()))
        } else {
            Err(Error::GeneratedBadCode(
                "proof does not result in a contradiction".to_string(),
            ))
        }
    }

    fn instantiate_claim_clause(
        claim: &crate::kernel::certificate_step::Claim,
        kernel_context: &KernelContext,
    ) -> Result<Clause, Error> {
        claim
            .normalized_specialized_clause(kernel_context)
            .map_err(Error::GeneratedBadCode)
    }
}

/// A test wrapper that combines a Checker with a KernelContext.
#[cfg(test)]
struct TestChecker {
    checker: Checker,
    context: KernelContext,
}

#[cfg(test)]
impl TestChecker {
    /// Creates a TestChecker with properly typed symbols.
    fn with_clauses(clauses: &[&str]) -> TestChecker {
        let mut context = KernelContext::new();
        // c0-c5: Bool constants
        context.parse_constants(&["c0", "c1", "c2", "c3", "c4", "c5"], "Bool");
        // g0, g1, g3, g4: (Bool, Bool) -> Bool functions
        context.parse_constants(&["g0", "g1"], "(Bool, Bool) -> Bool");
        // g2 placeholder to get to g3 and g4
        context.parse_constant("g2", "(Bool, Bool) -> Bool");
        context.parse_constants(&["g3", "g4"], "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        for clause_str in clauses {
            let clause = context.parse_clause(clause_str, &[]);
            checker.insert_clause(&clause, StepReason::Testing, &context);
        }
        TestChecker { checker, context }
    }

    fn check_clause_str(&mut self, s: &str) {
        let clause = self.context.parse_clause(s, &[]);
        if !self.checker.check_clause(&clause, &self.context).is_some() {
            panic!("check_clause_str(\"{}\") failed", s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::inference;
    use std::collections::{HashSet, VecDeque};

    fn problematic_negated_forall_clause() -> (KernelContext, Clause) {
        use crate::kernel::atom::Atom;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["g0", "g1"], "Bool -> Bool");
        let binder = Term::bool_type();
        let bound = Term::atom(Atom::BoundVariable(0));
        let g0_body =
            Term::new_variable(0).apply(&[context.parse_term("g0").apply(&[bound.clone()])]);
        let g1_body = Term::new_variable(0).apply(&[context.parse_term("g1").apply(&[bound])]);

        let clause = Clause::new(
            vec![
                Literal::negative(Term::forall(binder.clone(), g0_body)),
                Literal::negative(Term::forall(binder, g1_body)),
                Literal::positive(Term::new_variable(0).apply(&[Term::new_variable(1)])),
            ],
            &LocalContext::from_types(vec![context.parse_type("Bool -> Bool"), Term::bool_type()]),
        );
        (context, clause)
    }

    fn checker_style_clause_closure(
        kernel_context: &KernelContext,
        start: Clause,
        limit: usize,
    ) -> Vec<Clause> {
        let mut seen = HashSet::new();
        let mut queue = VecDeque::new();
        let mut ordered = vec![];

        seen.insert(start.clone());
        queue.push_back(start);

        while let Some(clause) = queue.pop_front() {
            ordered.push(clause.clone());
            if ordered.len() >= limit {
                break;
            }

            for next in clause.boolean_reductions(kernel_context) {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            for next in inference::equality_resolutions(&clause, kernel_context) {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            for next in inference::equality_factorings(&clause, kernel_context) {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            for next in clause.injectivities() {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            if let Some(extensionality) = clause.find_extensionality(kernel_context) {
                let next = Clause::new(extensionality, clause.get_local_context());
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
        }

        ordered
    }

    #[test]
    fn test_checker_should_be_monovariant() {
        // This basic case works
        let mut checker1 = TestChecker::with_clauses(&[
            "not g0(g1(c5, c0), c1)",
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or g0(g1(c5, c0), c1) or c4 = c1",
        ]);

        checker1.check_clause_str(
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or c4 = c1",
        );

        // This is the basic case plus extra things. So it should also work.
        let mut checker2 = TestChecker::with_clauses(&[
            // The minimal set of clauses that screw up our result
            "g4(c4, c5) = c3",
            "c4 != c0",
            "g4(c4, c5) != c3 or g4(c4, g1(c5, c0)) = g1(c3, c0) or c4 = c0",

            // The clauses from the basic case
            "not g0(g1(c5, c0), c1)",
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or g0(g1(c5, c0), c1) or c4 = c1",
        ]);

        checker2.check_clause_str(
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or c4 = c1",
        );
    }

    #[test]
    fn test_checker_cascades_updates() {
        // "c0 or c1 or c2" should combine with "not c2" to yield "c0 or c1".
        // That should then reduce via truth table logic with "not c0 or c1" to yield "c1".
        let mut checker = TestChecker::with_clauses(&["c0 or c1 or c2", "not c0 or c1", "not c2"]);
        checker.check_clause_str("c1");
    }

    #[test]
    fn test_checker_requires_exact_variable_clause_match() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context.parse_constant("g0", "Bool -> Bool");

        let mut checker = Checker::new();
        let generic = context.parse_clause("g0(x0)", &["Bool"]);
        checker.insert_clause(&generic, StepReason::Testing, &context);

        // Exact variable clause lookup is allowed for variable clauses.
        assert!(checker.check_clause(&generic, &context).is_some());

        // But specialization via generalization matching is disabled for variable clauses.
        let specialized = context.parse_clause("g0(c0)", &[]);
        assert!(checker.check_clause(&specialized, &context).is_none());
    }

    #[test]
    fn test_checker_simplifies_variable_clause_using_concrete_literal() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context.parse_constant("g0", "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        let not_baz = context.parse_clause("not c1", &[]);
        checker.insert_clause(&not_baz, StepReason::Testing, &context);

        let generic = context.parse_clause("not g0(x0, c0) or c1", &["Bool"]);
        checker.insert_clause(&generic, StepReason::Testing, &context);

        let reduced = context.parse_clause("not g0(x0, c0)", &["Bool"]);
        assert!(checker.check_clause(&reduced, &context).is_some());
    }

    #[test]
    fn test_checker_requires_explicit_step_for_late_variable_clause_simplification() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context.parse_constant("g0", "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        let generic = context.parse_clause("not g0(x0, c0) or c1", &["Bool"]);
        checker.insert_clause(&generic, StepReason::Testing, &context);

        let not_baz = context.parse_clause("not c1", &[]);
        checker.insert_clause(&not_baz, StepReason::Testing, &context);

        let reduced = context.parse_clause("not g0(x0, c0)", &["Bool"]);
        assert!(checker.check_clause(&reduced, &context).is_none());
    }

    #[test]
    fn test_checker_matches_identical_boolean_formula_literal_clause() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["g0", "g1", "g2", "g3"], "Bool -> Bool");

        let x0 = Term::new_variable(0);
        let g0 = context.parse_term("g0").apply(std::slice::from_ref(&x0));
        let g1 = context.parse_term("g1").apply(std::slice::from_ref(&x0));
        let g2 = context.parse_term("g2").apply(std::slice::from_ref(&x0));
        let g3 = context.parse_term("g3").apply(std::slice::from_ref(&x0));
        let term = Term::or(Term::and(g0, Term::or(Term::not(g1), Term::not(g2))), g3);

        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(term)],
            &LocalContext::from_types(vec![Term::bool_type()]),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&clause, StepReason::Testing, &context);

        let canonical = clause.normalized();
        assert!(
            checker.exact_clauses.contains_key(&canonical),
            "expected canonical clause {} to be stored for exact matching",
            canonical
        );
        assert!(checker.check_clause(&clause, &context).is_some());
    }

    #[test]
    fn test_insert_clause_normalizes_raw_impossible_clause() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");
        let c0 = context.parse_term("c0");

        let raw_clause = Clause::from_literals_unnormalized(
            vec![Literal::negative(Term::eq(
                Term::bool_type(),
                c0.clone(),
                c0,
            ))],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&raw_clause, StepReason::Testing, &context);

        assert!(
            checker.has_contradiction(),
            "checker insertion should normalize raw impossible clauses on entry"
        );
    }

    #[test]
    fn test_checker_matches_identical_concrete_boolean_formula_literal_clause() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");

        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::and(Term::not(c0), Term::not(c1)))],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&clause, StepReason::Testing, &context);

        assert!(checker.check_clause(&clause, &context).is_some());
    }

    #[test]
    fn test_checker_reduces_concrete_boolean_formula_clause_before_checking() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");
        let c0 = context.parse_term("c0");

        let reduced = Clause::from_literals_unnormalized(
            vec![Literal::positive(c0.clone())],
            &LocalContext::empty(),
        );
        let query = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::not(Term::not(c0)))],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&reduced, StepReason::Testing, &context);

        assert!(checker.check_clause(&query, &context).is_some());
    }

    #[test]
    fn test_checker_accepts_unit_resolution_for_existential_formula_clause() {
        use crate::kernel::atom::Atom;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");
        let bound = Term::atom(Atom::BoundVariable(0));

        let forward_exists = Term::exists(
            Term::bool_type(),
            Term::eq(Term::bool_type(), bound.clone(), c1.clone()),
        );
        let reversed_exists =
            Term::exists(Term::bool_type(), Term::eq(Term::bool_type(), c1, bound));

        let mut checker = Checker::new();
        let premise = Clause::from_literals_unnormalized(
            vec![Literal::positive(c0.clone())],
            &LocalContext::empty(),
        );
        checker.insert_clause(&premise, StepReason::Testing, &context);

        let implication = Clause::from_literals_unnormalized(
            vec![Literal::negative(c0), Literal::positive(forward_exists)],
            &LocalContext::empty(),
        );
        checker.insert_clause(&implication, StepReason::Testing, &context);

        let query = Clause::from_literals_unnormalized(
            vec![Literal::positive(reversed_exists)],
            &LocalContext::empty(),
        );
        assert!(checker.check_clause(&query, &context).is_some());
    }

    #[test]
    fn test_checker_requires_both_positive_and_branches() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");
        let query = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::and(c0.clone(), c1.clone()))],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![Literal::positive(c0.clone())],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );
        assert!(
            checker.check_clause(&query, &context).is_none(),
            "knowing only c0 must not prove c0 and c1"
        );

        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![Literal::positive(c1)],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );
        assert!(
            checker.check_clause(&query, &context).is_some(),
            "knowing both branches should prove the conjunction"
        );
    }

    #[test]
    fn test_checker_requires_both_boolean_equality_branches() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;

        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");
        let query = Clause::from_literals_unnormalized(
            vec![Literal::equals(c0.clone(), c1.clone())],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![Literal::positive(c0.clone())],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );
        assert!(
            checker.check_clause(&query, &context).is_none(),
            "one boolean-equality branch must not prove c0 = c1"
        );

        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![Literal::positive(c1)],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );
        assert!(
            checker.check_clause(&query, &context).is_some(),
            "true booleans on both sides should prove boolean equality"
        );
    }

    #[test]
    fn test_checker_does_not_resolve_self_inequality_over_arbitrary_type() {
        let mut context = KernelContext::new();
        context.parse_polymorphic_constant("c0", "T: Type", "Bool");

        let clause = context.parse_clause("x1 != x1 or c0(x0)", &["Type", "x0"]);
        let query = context.parse_clause("c0(x0)", &["Type"]);

        let mut checker = Checker::new();
        checker.insert_clause(&clause, StepReason::Testing, &context);
        assert!(
            checker.check_clause(&query, &context).is_none(),
            "x != x may only be resolved away when x's type is known inhabited"
        );
    }

    #[test]
    fn test_checker_resolves_self_inequality_over_inhabited_type() {
        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");

        let clause = context.parse_clause("x0 != x0 or c0", &["Bool"]);
        let query = context.parse_clause("c0", &[]);

        let mut checker = Checker::new();
        checker.insert_clause(&clause, StepReason::Testing, &context);
        assert!(
            checker.check_clause(&query, &context).is_some(),
            "Bool is inhabited, so equality resolution may remove x != x"
        );
    }

    #[test]
    fn test_checker_uses_obvious_witness_exists_as_inhabited() {
        let context = KernelContext::new();
        let local_context = context.parse_local(&["Type", "x0"]);
        let binder_type = Term::new_variable(0);
        let bound = Term::atom(Atom::BoundVariable(0));
        let witness = Term::new_variable(1);
        let positive_exists = Clause::new(
            vec![crate::kernel::literal::Literal::positive(Term::exists(
                binder_type.clone(),
                Term::eq(binder_type.clone(), bound, witness),
            ))],
            &local_context,
        );
        let negative_exists = Clause::new(
            vec![crate::kernel::literal::Literal::negative(Term::exists(
                binder_type,
                Term::new_true(),
            ))],
            &local_context,
        );

        let mut checker = Checker::new();
        checker.insert_clause(&positive_exists, StepReason::Testing, &context);
        checker.insert_clause(&negative_exists, StepReason::Testing, &context);

        assert!(
            checker.has_contradiction(),
            "an accepted existential with an obvious witness proves the witness type inhabited"
        );

        let mut checker = Checker::new();
        checker.insert_clause(&negative_exists, StepReason::Testing, &context);
        checker.insert_clause(&positive_exists, StepReason::Testing, &context);

        assert!(
            checker.has_contradiction(),
            "inhabitedness reprocessing should also close an earlier negated existential"
        );
    }

    #[test]
    fn test_checker_accepts_multi_step_unit_resolution_for_existential_formula_clause() {
        use crate::kernel::atom::Atom;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1", "c2"], "Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");
        let c2 = context.parse_term("c2");
        let bound = Term::atom(Atom::BoundVariable(0));

        let forward_exists = Term::exists(
            Term::bool_type(),
            Term::eq(Term::bool_type(), bound.clone(), c2.clone()),
        );
        let reversed_exists =
            Term::exists(Term::bool_type(), Term::eq(Term::bool_type(), c2, bound));

        let mut checker = Checker::new();
        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![Literal::positive(c0.clone())],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );
        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![Literal::negative(c1.clone())],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );
        checker.insert_clause(
            &Clause::from_literals_unnormalized(
                vec![
                    Literal::negative(c0),
                    Literal::positive(forward_exists),
                    Literal::positive(c1),
                ],
                &LocalContext::empty(),
            ),
            StepReason::Testing,
            &context,
        );

        let query = Clause::from_literals_unnormalized(
            vec![Literal::positive(reversed_exists)],
            &LocalContext::empty(),
        );
        assert!(checker.check_clause(&query, &context).is_some());
    }

    #[test]
    fn test_checker_mixed_clause_extensionality_contradicts_direct_function_inequality() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context
            .parse_constant("g0", "Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool");

        let mut checker = Checker::new();
        let mixed = context.parse_clause("not c1 or g0(c0, x0) = g1(c0, x0)", &["Bool"]);
        checker.insert_clause(&mixed, StepReason::Testing, &context);

        let guard = context.parse_clause("c1", &[]);
        checker.insert_clause(&guard, StepReason::Testing, &context);

        let neq = context.parse_clause("g0(c0) != g1(c0)", &[]);
        checker.insert_clause(&neq, StepReason::Testing, &context);

        assert!(
            checker.has_contradiction(),
            "mixed-clause extensionality should derive g0(c0) = g1(c0) and contradict the direct inequality"
        );
    }

    #[test]
    fn test_checker_typeclass_generalization() {
        // This test reproduces the exact bug from test_proving_with_default_required_attribute.
        //
        // From debug output of the failing test:
        // - Inserted: g4(x0) or g3(x0) = g2(x0) with x0: Typeclass(0)
        //   Only 1 form generated (stays as-is)
        // - Searched: g4(T0) or g3(T0) = g2(T0) with T0 = GroundTypeId(0)
        //   Specialized form: g3(T0) = g2(T0) or g4(T0) (reordered!)
        //
        // The bug: literals get reordered in specialized form but the general form
        // doesn't have that ordering stored.

        use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
        use crate::kernel::atom::Atom;
        use crate::kernel::generalization_set::GeneralizationSet;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::module::ModuleId;

        let mut kctx = KernelContext::new();

        // Create typeclass Arf (TypeclassId(0))
        let arf_tc = Typeclass {
            module_id: ModuleId(0),
            name: "Arf".to_string(),
        };
        let arf_tc_id = kctx.type_store.add_typeclass(&arf_tc);

        // Create ground type Foo (GroundTypeId(0)) that implements Arf
        kctx.parse_datatype("Foo");
        let foo_id = kctx.type_store.get_ground_id_by_name("Foo").unwrap();
        let foo_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Foo".to_string(),
        };
        kctx.type_store
            .add_type_instance(&AcornType::Data(foo_datatype, vec![]), arf_tc_id);

        // Set up function types to match the real test:
        // - g4 (diff): Arf -> Bool
        // - g3 (Arf.foo): (A: Arf) -> A (dependent - returns value of the type parameter)
        // - g2 (Arf.bar): (A: Arf) -> A (dependent - returns value of the type parameter)
        //
        // For dependent types, the output uses BoundVariable(0) to refer to the input.
        // When applied, type_apply_with_arg substitutes the argument.
        //
        // When applied to type variable x0:
        // - g4(x0) has type Bool
        // - g3(x0) has type x0 (the type variable)
        //
        // When applied to ground type Foo (T0):
        // - g4(T0) has type Bool
        // - g3(T0) has type Foo (T0)
        //
        // In sub_invariant_term_cmp:
        // - Comparing Bool vs x0 (type variable) returns None (head is variable)
        // - Comparing Bool vs Foo (ground type) returns Some(ordering)
        let arf_type = Term::typeclass(arf_tc_id);

        // g4: Arf -> Bool (non-dependent)
        let g4_type = Term::pi(arf_type.clone(), Term::bool_type());

        // g3, g2: (A: Arf) -> A (dependent type using BoundVariable)
        // BoundVariable(0) refers to the input A
        let bound_var = Term::atom(Atom::BoundVariable(0));
        let g3_type = Term::pi(arf_type.clone(), bound_var.clone());
        let g2_type = Term::pi(arf_type.clone(), bound_var.clone());

        kctx.symbol_table.add_global_constant(g4_type.clone()); // g0 (unused)
        kctx.symbol_table.add_global_constant(g4_type.clone()); // g1 (unused)
        kctx.symbol_table.add_global_constant(g2_type); // g2
        kctx.symbol_table.add_global_constant(g3_type); // g3
        kctx.symbol_table.add_global_constant(g4_type); // g4

        // Create general clause: g4(x0) or g3(x0) = g2(x0) where x0: Arf
        let general_clause = kctx.parse_clause("g4(x0) or g3(x0) = g2(x0)", &["Arf"]);

        // Create special clause: g4(Foo) or g3(Foo) = g2(Foo)
        let foo_term = Term::ground_type(foo_id);
        let special_clause = Clause::new(
            vec![
                Literal::new(
                    true,
                    Term::new(
                        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 4)),
                        vec![foo_term.clone()],
                    ),
                    Term::new_true(),
                ),
                Literal::new(
                    true,
                    Term::new(
                        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 3)),
                        vec![foo_term.clone()],
                    ),
                    Term::new(
                        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 2)),
                        vec![foo_term.clone()],
                    ),
                ),
            ],
            &LocalContext::empty(),
        );

        // Test at the GeneralizationSet level
        let mut gen_set = GeneralizationSet::new();
        gen_set.insert(general_clause.clone(), 0, &kctx);

        let result = gen_set.find_generalization(special_clause.clone(), &kctx);
        assert!(
            result.is_some(),
            "GeneralizationSet should find the general clause as a match for the special clause"
        );
    }

    #[test]
    fn test_parse_rejects_multi_trivial_witness_declaration() {
        use crate::certificate::Certificate;
        use crate::processor::Processor;
        use crate::project::Project;
        use std::borrow::Cow;

        let (_processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            theorem goal { true }
            "#,
        );

        let project = Project::new_mock();
        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Owned(normalized_goal.kernel_context.clone());

        let err = match Certificate::parse_code_line(
            "let (x: Bool, y: Bool) satisfy { true }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        ) {
            Ok(_) => panic!("expected parse failure"),
            Err(err) => err,
        };

        let Error::GeneratedBadCode(msg) = err else {
            panic!("expected GeneratedBadCode");
        };
        assert!(msg.contains("only supports a single declaration"));
    }

    #[test]
    fn test_check_cert_steps_rejects_tampered_witness_clauses() {
        use crate::certificate::Certificate;
        use crate::kernel::certificate_step::CertificateStep;
        use crate::processor::Processor;
        use crate::project::Project;
        use std::borrow::Cow;

        let (_processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            theorem goal { true }
            "#,
        );

        let project = Project::new_mock();
        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Owned(normalized_goal.kernel_context.clone());

        let mut satisfy_step = match Certificate::parse_code_line(
            "let w: Bool satisfy { true }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("valid satisfy step should parse")
        {
            CertificateStep::Satisfy(step) => step,
            CertificateStep::Claim(_) => panic!("expected satisfy step"),
        };

        let kernel_context = kernel_context_cow.as_ref();
        let mut checker = Checker::new();
        checker.insert_clause(
            &satisfy_step.justification.normalized_generic_clause(),
            StepReason::Testing,
            kernel_context,
        );

        satisfy_step.witness_clauses = vec![Clause::impossible()];
        let err = checker
            .check_cert_steps(
                &[CertificateStep::Satisfy(satisfy_step)],
                None,
                kernel_context,
            )
            .expect_err("tampered witness clauses should be rejected");
        assert!(
            err.to_string().contains("witness clauses mismatch"),
            "unexpected checker error: {err}"
        );
    }

    #[test]
    fn test_check_cert_steps_rejects_tampered_witness_specialized_clause() {
        use crate::certificate::Certificate;
        use crate::kernel::certificate_step::CertificateStep;
        use crate::processor::Processor;
        use crate::project::Project;
        use std::borrow::Cow;

        let (_processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            theorem goal { true }
            "#,
        );

        let project = Project::new_mock();
        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Owned(normalized_goal.kernel_context.clone());

        let mut satisfy_step = match Certificate::parse_code_line(
            "let w: Bool satisfy { true }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("valid satisfy step should parse")
        {
            CertificateStep::Satisfy(step) => step,
            CertificateStep::Claim(_) => panic!("expected satisfy step"),
        };

        let kernel_context = kernel_context_cow.as_ref();
        let mut checker = Checker::new();
        checker.insert_clause(
            &satisfy_step.justification.normalized_generic_clause(),
            StepReason::Testing,
            kernel_context,
        );

        assert_ne!(satisfy_step.specialized_clause, Some(Clause::impossible()));
        satisfy_step.specialized_clause = Some(Clause::impossible());
        let err = checker
            .check_cert_steps(
                &[CertificateStep::Satisfy(satisfy_step)],
                None,
                kernel_context,
            )
            .expect_err("tampered specialized clause should be rejected");
        assert!(
            err.to_string()
                .contains("witness specialized clause mismatch"),
            "unexpected checker error: {err}"
        );
    }

    #[test]
    fn test_check_cert_steps_rejects_ill_typed_claim_specialization_that_proves_false() {
        use crate::kernel::certificate_step::{CertificateStep, Claim};
        use crate::kernel::literal::Literal;
        use crate::kernel::variable_map::VariableMap;

        let mut context = KernelContext::new();
        context.parse_type_constructor("Empty", 0);
        let generic = Clause::new(
            vec![Literal::new(
                false,
                Term::new_variable(0),
                Term::new_variable(0),
            )],
            &LocalContext::from_types(vec![context.parse_type("Empty")]),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&generic, StepReason::Testing, &context);

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_true());
        let claim = Claim::new(generic, var_map).expect("old constructor only checks scope");

        let err = checker
            .check_cert_steps(&[CertificateStep::Claim(claim)], None, &context)
            .expect_err("ill-typed claim specialization should be rejected");
        assert!(
            err.to_string().contains("claim specialization"),
            "unexpected checker error: {err}"
        );
    }

    #[test]
    fn test_instantiate_claim_clause_normalizes_lambda_valued_arguments() {
        use crate::kernel::atom::Atom;
        use crate::kernel::certificate_step::Claim;
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");

        let claim = Claim::new(context.parse_clause("x0(c0)", &["Bool -> Bool"]), {
            let mut var_map = VariableMap::new();
            var_map.set(
                0,
                Term::lambda(
                    Term::bool_type(),
                    Term::not(Term::not(Term::atom(Atom::BoundVariable(0)))),
                ),
            );
            var_map
        })
        .expect("claim should normalize");

        let instantiated = Checker::instantiate_claim_clause(&claim, &context)
            .expect("claim instantiation should succeed");

        assert_eq!(
            instantiated,
            Clause::from_literals_unnormalized(
                vec![Literal::positive(Term::parse("c0"))],
                &LocalContext::empty(),
            )
        );
    }

    #[test]
    fn test_check_cert_steps_records_normalized_claim_clause() {
        use crate::kernel::atom::Atom;
        use crate::kernel::certificate_step::{CertificateStep, Claim};
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");

        let known = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::parse("c0"))],
            &LocalContext::empty(),
        );
        let generic = context.parse_clause("x0(c0)", &["Bool -> Bool"]);
        let negated = context.parse_clause("not c0", &[]);

        let mut checker = Checker::new();
        checker.insert_clause(&generic, StepReason::Testing, &context);
        checker.insert_clause(&negated, StepReason::Testing, &context);

        let claim = Claim::new(context.parse_clause("x0(c0)", &["Bool -> Bool"]), {
            let mut var_map = VariableMap::new();
            var_map.set(
                0,
                Term::lambda(
                    Term::bool_type(),
                    Term::not(Term::not(Term::atom(Atom::BoundVariable(0)))),
                ),
            );
            var_map
        })
        .expect("claim should normalize");

        let (checked_steps, used) = checker
            .check_cert_steps(&[CertificateStep::Claim(claim)], None, &context)
            .expect("claim should check");

        assert_eq!(used, 1);
        assert_eq!(checked_steps.len(), 1);
        assert_eq!(checked_steps[0].clause, known);
    }

    #[test]
    fn test_check_cert_steps_rejects_empty_non_contradictory_proof() {
        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");

        let mut checker = Checker::new();
        let known = context.parse_clause("c0", &[]);
        checker.insert_clause(&known, StepReason::Testing, &context);

        let err = checker
            .check_cert_steps(&[], None, &context)
            .expect_err("empty proof should not check without an existing contradiction");
        assert!(
            err.to_string()
                .contains("proof does not result in a contradiction"),
            "unexpected checker error: {err}"
        );
    }

    #[test]
    fn test_checker_problematic_negated_forall_clause_growth() {
        let (context, clause) = problematic_negated_forall_clause();
        let closure = checker_style_clause_closure(&context, clause, 40);

        for (i, clause) in closure.iter().enumerate() {
            println!("clause {i}: {clause}");
        }

        let canonical_count = closure
            .iter()
            .map(Clause::normalized)
            .collect::<HashSet<_>>()
            .len();
        let display_count = closure
            .iter()
            .map(|clause| clause.to_string())
            .collect::<HashSet<_>>()
            .len();

        println!("raw clause count: {}", closure.len());
        println!("canonical clause count: {}", canonical_count);
        println!("display string count: {}", display_count);

        let clause_strings: Vec<String> = closure.iter().map(|clause| clause.to_string()).collect();
        assert!(
            clause_strings
                .iter()
                .any(|s| s.matches("exists(Bool => not(").count() >= 2),
            "expected boolean reduction to surface the negated foralls as positive exists literals"
        );
        assert!(
            closure.len() < 40,
            "expected closure to stabilize well before the exploration limit, got {} clauses",
            closure.len()
        );
        assert!(
            canonical_count == closure.len() && display_count == closure.len(),
            "expected genuinely distinct clauses, got raw={}, canonical={}, display={}",
            closure.len(),
            canonical_count,
            display_count
        );
    }

    #[test]
    fn test_checker_accepts_canonicalized_variable_boolean_reduction_clause() {
        use crate::kernel::atom::Atom;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["g0", "g1"], "(Bool, Bool) -> Bool");
        let g0 = context.parse_term("g0");
        let g1 = context.parse_term("g1");
        let assumption_context =
            LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]);
        let assumption_body = Term::and(
            g0.apply(&[Term::new_variable(0), Term::atom(Atom::BoundVariable(0))]),
            Term::not(Term::eq(
                Term::bool_type(),
                Term::new_variable(1),
                Term::atom(Atom::BoundVariable(0)),
            )),
        );
        let assumption = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::or(
                Term::not(Term::exists(Term::bool_type(), assumption_body)),
                g1.apply(&[Term::new_variable(0), Term::new_variable(1)]),
            ))],
            &assumption_context,
        );
        let canonical_reduction = Clause::from_literals_unnormalized(
            vec![
                Literal::negative(Term::and(
                    g0.apply(&[Term::new_variable(0), Term::new_variable(1)]),
                    Term::not(Term::eq(
                        Term::bool_type(),
                        Term::new_variable(2),
                        Term::new_variable(1),
                    )),
                )),
                Literal::positive(g1.apply(&[Term::new_variable(0), Term::new_variable(2)])),
            ],
            &LocalContext::from_types(vec![
                Term::bool_type(),
                Term::bool_type(),
                Term::bool_type(),
            ]),
        )
        .normalized();

        let mut checker = Checker::new();
        checker.insert_clause(&assumption, StepReason::Testing, &context);

        assert!(
            checker.check_clause(&canonical_reduction, &context).is_some(),
            "checker should prove the canonical boolean-reduction clause after inserting the assumption",
        );
    }
}
