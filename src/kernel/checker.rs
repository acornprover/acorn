use std::collections::HashSet;

use im::HashMap as ImHashMap;
use im::HashSet as ImHashSet;
use im::Vector as ImVector;

use crate::code_generator::Error;
use crate::elaborator::source::Source;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::BooleanReductionKind;
use crate::kernel::clause::{Clause, NormalizedClauseTrace};
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::Rule;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_clause_subterms;
use crate::kernel::variable_map::VariableMap;
use crate::kernel::{EqualityGraph, StepId};
use tracing::trace;

/// The reason why a certificate step was accepted.
#[derive(Debug, Clone)]
pub enum StepReason {
    /// Proven by the term graph (concrete reasoning via congruence closure and propositional logic).
    EqualityGraph,

    /// Proven by simplifying a variable clause against current concrete equality-graph facts.
    VariableSimplification(Vec<usize>),

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
            StepReason::VariableSimplification(_) => "simplification".to_string(),
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
        self.dependencies().into_iter().next()
    }

    pub fn dependencies(&self) -> Vec<usize> {
        match self {
            StepReason::EqualityResolution(step_id)
            | StepReason::Extensionality(step_id)
            | StepReason::EqualityFactoring(step_id)
            | StepReason::Injectivity(step_id)
            | StepReason::BooleanReduction(step_id) => vec![*step_id],
            StepReason::VariableSimplification(step_ids) => step_ids.clone(),
            _ => vec![],
        }
    }
}

/// A clause inserted into the checker, together with the reason used for dependency IDs.
#[derive(Debug, Clone)]
pub struct InsertedClause {
    pub clause: Clause,
    pub reason: StepReason,
}

/// A constructed justification for a clause via boolean-reduction reasoning.
///
/// This is the evidence behind `check_clause_via_boolean_reductions`: a clause holds
/// because every member of one of its reduction sets holds, recursively, down to
/// leaves the checker knows directly. Certificate writing serializes this tree into
/// explicit trace steps, so replay can verify each node locally instead of
/// re-running the search.
#[derive(Debug, Clone)]
pub(crate) enum BooleanReductionWitness {
    /// The clause is directly known. When it matches an inserted clause, the id
    /// lets the trace writer replay that clause's own derivation chain.
    Direct {
        clause: Clause,
        inserted_id: Option<usize>,
    },
    /// The clause follows because every member of one of its reduction sets holds.
    Reduced {
        clause: Clause,
        members: Vec<BooleanReductionWitness>,
    },
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

    /// Dependencies for a direct contradiction, when it was produced by a traceable step.
    direct_contradiction_dependencies: Option<Vec<usize>>,

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

    /// Whether inserting a clause should eagerly insert all of its boolean reductions.
    eager_boolean_reductions: bool,
}

impl Checker {
    pub fn new() -> Checker {
        Checker {
            term_graph: EqualityGraph::new(),
            exact_clauses: ImHashMap::new(),
            direct_contradiction: false,
            direct_contradiction_dependencies: None,
            variable_clause_generations: ImHashMap::new(),
            concrete_generation: 0,
            past_boolean_reductions: ImHashSet::new(),
            proven_inhabited: HashSet::new(),
            reasons: ImVector::new(),
            inserted_clauses: ImVector::new(),
            eager_boolean_reductions: true,
        }
    }

    pub(crate) fn set_eager_boolean_reductions(&mut self, enabled: bool) {
        self.eager_boolean_reductions = enabled;
    }

    pub(crate) fn enable_eager_boolean_reductions(&mut self, kernel_context: &KernelContext) {
        self.eager_boolean_reductions = true;
        self.reprocess_boolean_reductions(kernel_context);
    }

    fn dependencies_for_reason(reason: &StepReason) -> Option<Vec<usize>> {
        let dependencies = reason.dependencies();
        (!dependencies.is_empty()).then_some(dependencies)
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

    pub(crate) fn checker_boolean_reduction_sets(
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
            self.direct_contradiction_dependencies = Self::dependencies_for_reason(&reason);
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
                self.direct_contradiction_dependencies = Self::dependencies_for_reason(&reason);
            }
        }

        if let Some(key) = self.mark_inhabited_from_clause(clause, kernel_context) {
            if self.has_negated_exists_true_for(&key) {
                self.direct_contradiction = true;
                self.direct_contradiction_dependencies = Self::dependencies_for_reason(&reason);
            }
            if should_reprocess_for_inhabitedness && self.eager_boolean_reductions {
                self.reprocess_boolean_reductions(kernel_context);
            }
        }

        if has_any_variable {
            if let Some((reduced_clause, mut dependencies)) = self
                .simplify_variable_clause_with_concrete_facts_and_dependencies(
                    clause,
                    kernel_context,
                )
            {
                dependencies.push(step_id);
                dependencies.sort_unstable();
                dependencies.dedup();
                self.insert_clause_internal(
                    &reduced_clause,
                    StepReason::VariableSimplification(dependencies),
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

        if self.eager_boolean_reductions {
            self.insert_boolean_reductions_with_reason(clause, step_id, kernel_context);
        }
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

    pub(crate) fn insert_clause_for_trace(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        let clause = normalize_clause_subterms(clause).normalized();
        self.insert_clause_shallow_for_trace(&clause, reason, kernel_context);
    }

    fn insert_clause_shallow_for_trace(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        trace!(clause = %clause, reason = ?reason.description(), "inserting certificate trace clause");

        if clause.is_impossible() {
            self.direct_contradiction = true;
            self.direct_contradiction_dependencies = Self::dependencies_for_reason(&reason);
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

        if let Some(key) = Self::negated_exists_true_type_from_clause(clause) {
            if self.proven_inhabited.contains(&key) {
                self.direct_contradiction = true;
                self.direct_contradiction_dependencies = Self::dependencies_for_reason(&reason);
            }
        }
        if let Some(key) = self.mark_inhabited_from_clause(clause, kernel_context) {
            if self.has_negated_exists_true_for(&key) {
                self.direct_contradiction = true;
                self.direct_contradiction_dependencies = Self::dependencies_for_reason(&reason);
            }
        }

        if !has_any_variable {
            self.concrete_generation += 1;
            self.term_graph
                .insert_clause(clause, StepId(step_id), kernel_context);
        }
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

    pub(crate) fn check_clause_direct_for_trace(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        let clause = normalize_clause_subterms(clause).normalized();
        if clause.is_tautology() {
            return Some(StepReason::EqualityGraph);
        }
        self.check_clause_direct(&clause, kernel_context)
            .or_else(|| self.check_clause_via_concrete_simplification(&clause, kernel_context))
    }

    pub(crate) fn boolean_reduction_proves_for_trace(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        let clause = normalize_clause_subterms(clause).normalized();
        self.check_clause_via_boolean_reductions(&clause, kernel_context)
            .is_some()
    }

    pub(crate) fn boolean_reduction_closes_for_trace(
        &self,
        source: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        let source = normalize_clause_subterms(source).normalized();
        if source.is_impossible() {
            return true;
        }

        let mut local = self.clone();
        local.set_eager_boolean_reductions(false);
        local.insert_clause_for_trace(&source, StepReason::PreviousClaim, kernel_context);
        let Some(step_id) = local.exact_clause_id(&source) else {
            return false;
        };
        local.eager_boolean_reductions = true;
        local.insert_boolean_reductions_with_reason(&source, step_id, kernel_context);
        local.has_contradiction()
    }

    /// Canonicalizes a clause the same way trace reduction candidates are normalized.
    ///
    /// Clauses that describe the same logical step can reach the trace machinery with
    /// different variable numberings, depending on whether they were produced by the
    /// kernel's normalization or parsed back from generated claim code. Comparing
    /// canonical forms makes those alpha-equivalent clauses compare equal.
    pub(crate) fn canonical_clause_for_trace(
        &self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let context = clause.get_local_context().clone();
        let trace = Clause::normalize_with_trace(clause.literals.clone(), &context);
        self.normalize_checker_trace(&trace, kernel_context)
    }

    /// Whether a canonical trace candidate matches the given target clause, either
    /// exactly or after canonicalizing the target.
    fn trace_candidate_matches(
        &self,
        candidate: &Clause,
        target: &Clause,
        canonical_target: Option<&Clause>,
    ) -> bool {
        candidate == target || canonical_target.is_some_and(|canonical| candidate == canonical)
    }

    pub(crate) fn boolean_reduction_set_contains_for_trace(
        &self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        let canonical_result = self.canonical_clause_for_trace(result, kernel_context);
        self.checker_boolean_reduction_sets(source, kernel_context)
            .into_iter()
            .flatten()
            .any(|candidate| {
                self.trace_candidate_matches(&candidate, result, canonical_result.as_ref())
            })
    }

    pub(crate) fn boolean_reduction_detail_for_trace(
        &self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<(BooleanReductionKind, usize)> {
        let canonical_result = self.canonical_clause_for_trace(result, kernel_context);
        source
            .find_boolean_reduction_kinds_with_locations_with_options(kernel_context, true)
            .into_iter()
            .find_map(|(kind, literal_index, trace)| {
                self.normalize_checker_trace(&trace, kernel_context)
                    .filter(|candidate| {
                        self.trace_candidate_matches(candidate, result, canonical_result.as_ref())
                    })
                    .map(|_| (kind, literal_index))
            })
    }

    pub(crate) fn apply_boolean_reduction_for_trace(
        &self,
        source: &Clause,
        kind: BooleanReductionKind,
        literal_index: usize,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let trace =
            source.boolean_reduction_at_with_options(kind, literal_index, kernel_context, true)?;
        self.normalize_checker_trace(&trace, kernel_context)
    }

    pub(crate) fn equality_resolution_results_for_trace(
        &self,
        source: &Clause,
        kernel_context: &KernelContext,
    ) -> Vec<Clause> {
        inference::find_equality_resolutions(source, kernel_context)
            .into_iter()
            .filter_map(|(literals, context, _)| {
                let trace = Clause::normalize_with_trace(literals, &context);
                self.normalize_checker_trace(&trace, kernel_context)
            })
            .collect()
    }

    pub(crate) fn equality_resolution_derives_for_trace(
        &self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        self.equality_resolution_results_for_trace(source, kernel_context)
            .into_iter()
            .any(|candidate| candidate == *result)
    }

    pub(crate) fn equality_factoring_derives_for_trace(
        &self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        inference::find_equality_factorings(source, kernel_context)
            .into_iter()
            .filter_map(|(literals, context, _)| {
                let trace = Clause::normalize_with_trace(literals, &context);
                self.normalize_checker_trace(&trace, kernel_context)
            })
            .any(|candidate| candidate == *result)
    }

    pub(crate) fn injectivity_derives_for_trace(
        &self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        source
            .find_injectivities()
            .into_iter()
            .filter_map(|literals| {
                let trace = Clause::normalize_with_trace(literals, source.get_local_context());
                self.normalize_checker_trace(&trace, kernel_context)
            })
            .any(|candidate| candidate == *result)
    }

    pub(crate) fn extensionality_derives_for_trace(
        &self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        let Some(literals) = source.find_extensionality(kernel_context) else {
            return false;
        };
        Clause::new(literals, source.get_local_context()) == *result
    }

    pub(crate) fn equality_graph_derives_for_trace(
        &mut self,
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        if self
            .simplify_variable_clause_with_concrete_facts(source, kernel_context)
            .as_ref()
            == Some(result)
        {
            return true;
        }
        if self
            .check_clause_direct_for_trace(result, kernel_context)
            .is_some()
        {
            return true;
        }
        false
    }

    pub(crate) fn clause_specializes_for_trace(
        source: &Clause,
        result: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        let source = normalize_clause_subterms(source).normalized();
        let result = normalize_clause_subterms(result).normalized();
        if source == result {
            return true;
        }
        Self::clause_matches_with_var_map(&source, &result, kernel_context)
    }

    fn literals_match_with_var_map(
        general: &Literal,
        special: &Literal,
        var_map: &mut VariableMap,
        general_context: &LocalContext,
        special_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        if general.positive != special.positive {
            return false;
        }

        let mut direct = var_map.clone();
        if direct.match_terms(
            general.left.as_ref(),
            special.left.as_ref(),
            general_context,
            special_context,
            kernel_context,
        ) && direct.match_terms(
            general.right.as_ref(),
            special.right.as_ref(),
            general_context,
            special_context,
            kernel_context,
        ) {
            *var_map = direct;
            return true;
        }

        let mut flipped = var_map.clone();
        if flipped.match_terms(
            general.left.as_ref(),
            special.right.as_ref(),
            general_context,
            special_context,
            kernel_context,
        ) && flipped.match_terms(
            general.right.as_ref(),
            special.left.as_ref(),
            general_context,
            special_context,
            kernel_context,
        ) {
            *var_map = flipped;
            return true;
        }

        false
    }

    fn clause_matches_with_var_map(
        general: &Clause,
        special: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        if general.len() != special.len() {
            return false;
        }

        fn match_from(
            general: &Clause,
            special: &Clause,
            kernel_context: &KernelContext,
            general_index: usize,
            used_special: &mut [bool],
            var_map: VariableMap,
        ) -> bool {
            if general_index == general.len() {
                return true;
            }

            let general_literal = &general.literals[general_index];
            for special_index in 0..special.len() {
                if used_special[special_index] {
                    continue;
                }
                let mut candidate_map = var_map.clone();
                if !Checker::literals_match_with_var_map(
                    general_literal,
                    &special.literals[special_index],
                    &mut candidate_map,
                    general.get_local_context(),
                    special.get_local_context(),
                    kernel_context,
                ) {
                    continue;
                }
                used_special[special_index] = true;
                if match_from(
                    general,
                    special,
                    kernel_context,
                    general_index + 1,
                    used_special,
                    candidate_map,
                ) {
                    return true;
                }
                used_special[special_index] = false;
            }
            false
        }

        let mut used_special = vec![false; special.len()];
        match_from(
            general,
            special,
            kernel_context,
            0,
            &mut used_special,
            VariableMap::new(),
        )
    }

    pub(crate) fn clauses_contradict_for_trace(
        left: &Clause,
        right: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        if left.is_impossible() || right.is_impossible() {
            return true;
        }

        if let ([left_literal], [right_literal]) =
            (left.literals.as_slice(), right.literals.as_slice())
        {
            let negated_left = Clause::new(vec![left_literal.negate()], left.get_local_context());
            let negated_right =
                Clause::new(vec![right_literal.negate()], right.get_local_context());
            return Self::clause_specializes_for_trace(left, &negated_right, kernel_context)
                || Self::clause_specializes_for_trace(right, &negated_left, kernel_context);
        }

        if left.has_any_variable() || right.has_any_variable() {
            return false;
        }

        let mut local = Checker::new();
        local.insert_clause_for_trace(left, StepReason::PreviousClaim, kernel_context);
        local.insert_clause_for_trace(right, StepReason::PreviousClaim, kernel_context);
        local.has_contradiction()
    }

    fn check_clause_via_boolean_reductions(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        let mut seen = HashSet::new();
        self.check_clause_via_boolean_reductions_inner(clause, kernel_context, &mut seen)
    }

    /// Like `check_clause_via_boolean_reductions`, but returns the derivation tree
    /// instead of a bare verdict, so the certificate writer can serialize it.
    /// The input clause should be subterm-normalized, as in `check_clause`.
    pub(crate) fn boolean_reduction_witness(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<BooleanReductionWitness> {
        let clause = normalize_clause_subterms(clause).normalized();
        let mut seen = HashSet::new();
        self.boolean_reduction_witness_inner(&clause, kernel_context, &mut seen)
    }

    fn boolean_reduction_witness_inner(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
        seen: &mut HashSet<Clause>,
    ) -> Option<BooleanReductionWitness> {
        if clause.has_any_variable() || !seen.insert(clause.clone()) {
            return None;
        }

        for reduction_set in self.checker_boolean_reduction_sets(clause, kernel_context) {
            let mut set_seen = seen.clone();
            let mut members = Vec::with_capacity(reduction_set.len());
            let mut all_known = true;

            for candidate in reduction_set {
                let witness = if self
                    .check_clause_direct(&candidate, kernel_context)
                    .is_some()
                {
                    Some(BooleanReductionWitness::Direct {
                        inserted_id: self.exact_clause_id(&candidate),
                        clause: candidate,
                    })
                } else {
                    self.boolean_reduction_witness_inner(&candidate, kernel_context, &mut set_seen)
                };

                match witness {
                    Some(witness) => members.push(witness),
                    None => {
                        all_known = false;
                        break;
                    }
                }
            }

            if all_known {
                return Some(BooleanReductionWitness::Reduced {
                    clause: clause.clone(),
                    members,
                });
            }
        }

        None
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
            .or_else(|| self.check_clause_via_concrete_simplification(&clause, kernel_context))
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

    pub(crate) fn contradiction_dependencies_for_trace(&self) -> Option<Vec<usize>> {
        if self.direct_contradiction {
            return self.direct_contradiction_dependencies.clone();
        }
        let contradiction = self.term_graph.get_contradiction_trace()?;
        let mut dependencies = vec![contradiction.inequality_id];
        for step in contradiction.rewrite_chain {
            dependencies.push(step.source.pattern_id.get());
            if let Some(inspiration_id) = step.source.inspiration_id {
                dependencies.push(inspiration_id.get());
            }
        }
        dependencies.sort_unstable();
        dependencies.dedup();
        Some(dependencies)
    }

    pub(crate) fn equality_graph_dependencies_for_clause_for_trace(
        &self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<Vec<usize>> {
        let clause = normalize_clause_subterms(clause).normalized();
        if clause.literals.len() != 1 {
            return None;
        }
        let mut local = self.clone();
        if !local.term_graph.check_clause(&clause, kernel_context) {
            return None;
        }
        let before = local.inserted_len();
        let negated = Clause::new(
            vec![clause.literals[0].negate()],
            clause.get_local_context(),
        );
        local.insert_clause(&negated, StepReason::Testing, kernel_context);
        let mut dependencies = local.contradiction_dependencies_for_trace()?;
        dependencies.retain(|dependency| *dependency < before);
        if dependencies.is_empty() {
            None
        } else {
            Some(dependencies)
        }
    }

    pub fn exact_clause_id(&self, clause: &Clause) -> Option<usize> {
        self.exact_clauses.get(clause).copied()
    }

    /// Checks whether a clause follows from known facts after evaluating its literals
    /// against the concrete term graph.
    ///
    /// If some literal is concretely true, the disjunction holds outright. Otherwise,
    /// dropping concretely-false literals preserves equivalence, so if the reduced clause
    /// is directly known, the original clause is entailed. This covers certificate claims
    /// that are weaker than an eagerly-simplified known clause: insertion simplifies a
    /// known clause past the intermediate form the proof recorded (for example, a unit
    /// resolution whose remaining negative literal is also refuted by a known fact), and
    /// the intermediate claim then has no exact match.
    fn check_clause_via_concrete_simplification(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        let mut changed = false;
        let mut reduced_literals = Vec::with_capacity(clause.literals.len());
        for literal in &clause.literals {
            match self
                .term_graph
                .evaluate_literal_with_dependencies(literal, kernel_context)
            {
                Some((true, _)) => return Some(StepReason::EqualityGraph),
                Some((false, _)) => changed = true,
                None => reduced_literals.push(literal.clone()),
            }
        }
        if !changed || reduced_literals.is_empty() {
            return None;
        }
        let reduced = Clause::new(reduced_literals, clause.get_local_context());
        self.check_clause_direct(&reduced, kernel_context)
    }

    fn simplify_variable_clause_with_concrete_facts(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        self.simplify_variable_clause_with_concrete_facts_and_dependencies(clause, kernel_context)
            .map(|(clause, _dependencies)| clause)
    }

    fn simplify_variable_clause_with_concrete_facts_and_dependencies(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<(Clause, Vec<usize>)> {
        let mut changed = false;
        let mut dependencies = vec![];
        let mut reduced_literals = Vec::with_capacity(clause.literals.len());
        for literal in &clause.literals {
            match self
                .term_graph
                .evaluate_literal_with_dependencies(literal, kernel_context)
            {
                Some((true, _)) => return None,
                Some((false, mut literal_dependencies)) => {
                    changed = true;
                    dependencies.append(&mut literal_dependencies);
                }
                None => reduced_literals.push(literal.clone()),
            }
        }
        if !changed {
            return None;
        }
        dependencies.sort_unstable();
        dependencies.dedup();
        Some((
            Clause::new(reduced_literals, clause.get_local_context()),
            dependencies,
        ))
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
    fn test_claim_specialization_normalizes_lambda_valued_arguments() {
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

        let instantiated = claim
            .normalized_specialized_clause(&context)
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

#[cfg(test)]
mod alpha_regression_tests {
    use super::*;
    use crate::kernel::kernel_context::KernelContext;

    // Regression test for the certificate failures found by `reprove relation_basic` on
    // 2026-07-02 ("certificate trace br step N does not apply ..." and "inst step N generic
    // clause does not match premise ..."). Clauses reconstructed from generated claim code
    // keep the claim's variable ordering, while trace reduction candidates are renumbered by
    // first occurrence. The trace machinery compares such alpha-equivalent clauses through
    // canonical_clause_for_trace, which must map both numberings to the same clause.
    #[test]
    fn test_canonical_clause_for_trace_equates_alpha_variants() {
        use crate::kernel::clause::Clause;

        let mut context = KernelContext::new();
        context.parse_constant("g0", "(Type, Bool) -> Bool");

        // The canonical numbering orders variables by first occurrence.
        let canonical = context.parse_clause("g0(x0, x1)", &["Type", "Bool"]);

        // Build the same clause with permuted variable numbering, bypassing the
        // normalization that Clause::new applies.
        let permuted_context = context.parse_local(&["Bool", "Type"]);
        let permuted_literal = context.parse_literal("g0(x1, x0)");
        let permuted =
            Clause::from_literals_unnormalized(vec![permuted_literal], &permuted_context);

        // The permuted clause must actually differ syntactically, or this test is vacuous.
        assert_ne!(canonical, permuted);

        let checker = Checker::new();
        let canonical_form = checker.canonical_clause_for_trace(&canonical, &context);
        let permuted_form = checker.canonical_clause_for_trace(&permuted, &context);
        assert!(canonical_form.is_some());
        assert_eq!(canonical_form, permuted_form);
    }
}

#[cfg(test)]
mod concrete_simplification_check_tests {
    use super::*;
    use crate::kernel::atom::Atom;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;

    // Regression test for the "generated proof steps did not close" certificate failures
    // (compact_union.ac:55, order_bounds.ac:1542, 2026-07-02). Induction-style proofs record
    // an intermediate unit resolution:
    //   [1] forall(b0) { g0(b0) } = true            (step case, concrete boolean term)
    //   [2] not forall(b0){g0(b0)} or not g1(c0) or g1(x0)   (induction instance, generic)
    //   [3] not g1(c0) or g1(x0)                    (unit resolution of [2] with [1])
    // When the base case g1(c0) is also known, inserting [2] eagerly simplifies straight to
    // g1(x0), skipping past [3], so [3] has no exact match and claim emission failed. The
    // checker must accept a claim whose concretely-false literals reduce it to a known clause.
    #[test]
    fn test_check_clause_accepts_claim_weaker_than_simplified_fact() {
        let mut context = KernelContext::new();
        context.parse_constant("g0", "Bool -> Bool");
        context.parse_constant("g1", "Bool -> Bool");
        context.parse_constants(&["c0", "c1"], "Bool");

        let bound = Term::atom(Atom::BoundVariable(0));
        let forall_term = Term::forall(Term::bool_type(), context.parse_term("g0").apply(&[bound]));

        let step1 = Clause::new(
            vec![Literal::positive(forall_term.clone())],
            LocalContext::empty_ref(),
        );

        let x0 = Term::new_variable(0);
        let local = LocalContext::from_types(vec![Term::bool_type()]);
        let step2 = Clause::new(
            vec![
                Literal::negative(forall_term.clone()),
                Literal::negative(context.parse_term("g1").apply(&[context.parse_term("c0")])),
                Literal::positive(context.parse_term("g1").apply(&[x0.clone()])),
            ],
            &local,
        );

        let step3 = Clause::new(
            vec![
                Literal::negative(context.parse_term("g1").apply(&[context.parse_term("c0")])),
                Literal::positive(context.parse_term("g1").apply(&[x0])),
            ],
            &local,
        );

        let mut checker = Checker::new();
        // The base case g1(c0) is already proven in the surrounding context,
        // like p(List.nil) in the real proof.
        let base_case = Clause::new(
            vec![Literal::positive(
                context.parse_term("g1").apply(&[context.parse_term("c0")]),
            )],
            LocalContext::empty_ref(),
        );
        checker.insert_clause(&base_case, StepReason::Testing, &context);
        checker.insert_clause(&step1, StepReason::Testing, &context);
        checker.insert_clause(&step2, StepReason::Testing, &context);

        assert!(
            checker.check_clause(&step3, &context).is_some(),
            "intermediate unit resolution should check via concrete simplification"
        );
        // The concrete instance of the claim behaves the same way.
        let step3_concrete = Clause::new(
            vec![
                Literal::negative(context.parse_term("g1").apply(&[context.parse_term("c0")])),
                Literal::positive(context.parse_term("g1").apply(&[context.parse_term("c1")])),
            ],
            LocalContext::empty_ref(),
        );
        checker.insert_clause(
            &context.parse_clause("g1(c1)", &[]),
            StepReason::Testing,
            &context,
        );
        assert!(
            checker.check_clause(&step3_concrete, &context).is_some(),
            "concrete claim with a refuted literal should also check"
        );
    }
}

#[cfg(test)]
mod embedded_eq_symmetry_tests {
    use super::*;
    use crate::kernel::atom::Atom;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;

    // Regression tests for the embedded-equality symmetry gap found via order_bounds.ac:1542
    // (2026-07-02). Term normalization orients embedded eq terms before insertion, but
    // congruence after later merges can produce the orientation normalization would have
    // swapped. Without eq-symmetry in the graph, that orientation is stranded and the
    // contradiction goes undetected ("generated proof steps did not close").
    //
    // Replicates order_bounds.ac:1542 in miniature:
    //   a, x, b : Bool-ish constants (use Bool to keep types simple)
    //   idf : Bool -> Bool  (identity_fn)
    //   sing : (Bool, Bool) -> Bool  (is_singleton)
    //   pins : (Bool, Bool) -> Bool  (pred_insert applied to its function arg is too
    //          higher-order for the mini version; collapse to a binary op)
    // Steps:
    //   [1] idf(x) = x
    //   [2] sing(b, x) = eq(b, x)          (embedded eq term)
    //   [4] or(eq(a,x), eq(b,x)) != pins(a, x)
    //   [6] or(eq(a, idf(x)), sing(b, idf(x))) = pins(a, idf(x))
    // Expect: contradiction via concrete congruence.
    #[test]
    fn test_contradiction_through_identity_rewrite_and_embedded_eq() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1", "c2"], "Bool");
        context.parse_constant("g0", "Bool -> Bool");
        context.parse_constant("g1", "(Bool, Bool) -> Bool");
        context.parse_constant("g2", "(Bool, Bool) -> Bool");

        let a = context.parse_term("c0");
        let x = context.parse_term("c1");
        let b = context.parse_term("c2");
        let idf = context.parse_term("g0");
        let sing = context.parse_term("g1");
        let pins = context.parse_term("g2");
        let or = Term::atom(Atom::Symbol(Symbol::Or));
        let bool_ty = Term::bool_type();

        let idf_x = idf.apply(&[x.clone()]);

        let step1 = Clause::new(
            vec![Literal::equals(idf_x.clone(), x.clone())],
            LocalContext::empty_ref(),
        );
        let step2 = Clause::new(
            vec![Literal::equals(
                sing.apply(&[b.clone(), x.clone()]),
                Term::eq(bool_ty.clone(), b.clone(), x.clone()),
            )],
            LocalContext::empty_ref(),
        );
        let lhs4 = or.apply(&[
            Term::eq(bool_ty.clone(), a.clone(), x.clone()),
            Term::eq(bool_ty.clone(), b.clone(), x.clone()),
        ]);
        let step4 = Clause::new(
            vec![Literal::not_equals(
                lhs4,
                pins.apply(&[a.clone(), x.clone()]),
            )],
            LocalContext::empty_ref(),
        );
        let lhs6 = or.apply(&[
            Term::eq(bool_ty.clone(), a.clone(), idf_x.clone()),
            sing.apply(&[b.clone(), idf_x.clone()]),
        ]);
        let step6 = Clause::new(
            vec![Literal::equals(
                lhs6,
                pins.apply(&[a.clone(), idf_x.clone()]),
            )],
            LocalContext::empty_ref(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&step1, StepReason::Testing, &context);
        checker.insert_clause(&step2, StepReason::Testing, &context);
        checker.insert_clause(&step4, StepReason::Testing, &context);
        assert!(!checker.has_contradiction());
        checker.insert_clause(&step6, StepReason::Testing, &context);
        assert!(checker.has_contradiction());
    }
}

#[cfg(test)]
mod double_rewrite_congruence_tests {
    use super::*;
    use crate::kernel::atom::Atom;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;

    // Minimal shape of the order_bounds.ac:1542 failure: both or-arguments differ between
    // the two sides and each needs one rewrite, one of them inside an embedded eq term:
    //   or(eq(c0, g0(c1)), g1(c2, g0(c1)))  vs  or(eq(c0, c1), eq(c2, c1))
    // Closing requires eq-symmetry in the equality graph, because normalization orients
    // eq(c0, g0(c1)) opposite to eq(c0, c1) and congruence preserves orientation.
    #[test]
    fn test_double_rewrite_inside_or_closes() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1", "c2"], "Bool");
        context.parse_constant("g0", "Bool -> Bool");
        context.parse_constant("g1", "(Bool, Bool) -> Bool");
        context.parse_constant("g2", "(Bool, Bool) -> Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");
        let c2 = context.parse_term("c2");
        let g0 = context.parse_term("g0");
        let g1 = context.parse_term("g1");
        let g2 = context.parse_term("g2");
        let or = Term::atom(Atom::Symbol(Symbol::Or));
        let bool_ty = Term::bool_type();
        let g0_c1 = g0.apply(&[c1.clone()]);
        let concrete = |literals: Vec<Literal>| Clause::new(literals, LocalContext::empty_ref());

        let mut checker = Checker::new();
        checker.insert_clause(
            &concrete(vec![Literal::equals(g0_c1.clone(), c1.clone())]),
            StepReason::Testing,
            &context,
        );
        checker.insert_clause(
            &concrete(vec![Literal::equals(
                g1.apply(&[c2.clone(), c1.clone()]),
                Term::eq(bool_ty.clone(), c2.clone(), c1.clone()),
            )]),
            StepReason::Testing,
            &context,
        );
        checker.insert_clause(
            &concrete(vec![Literal::not_equals(
                or.apply(&[
                    Term::eq(bool_ty.clone(), c0.clone(), c1.clone()),
                    Term::eq(bool_ty.clone(), c2.clone(), c1.clone()),
                ]),
                g2.apply(&[c0.clone(), c1.clone()]),
            )]),
            StepReason::Testing,
            &context,
        );
        checker.insert_clause(
            &concrete(vec![Literal::equals(
                or.apply(&[
                    Term::eq(bool_ty.clone(), c0.clone(), g0_c1.clone()),
                    g1.apply(&[c2.clone(), g0_c1.clone()]),
                ]),
                g2.apply(&[c0.clone(), g0_c1.clone()]),
            )]),
            StepReason::Testing,
            &context,
        );
        assert!(checker.has_contradiction());
    }
}
