use std::collections::{HashMap, HashSet};

use super::proof::ProofResolver;
#[cfg(any(test, feature = "validate"))]
use super::proof::{reconstruct_step, ConcreteStep, ConcreteStepId};
use super::rewrite_tree::{Rewrite, RewriteTree};
use crate::code_generator::Error;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::clause_set::TermId;
use crate::kernel::fingerprint::FingerprintUnifier;
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pdt::LiteralSet;
use crate::kernel::proof_step::{
    PremiseMap, ProofStep, ProofStepId, Rule, SimplificationInfo, SingleSourceInfo, Truthiness,
};
use crate::kernel::term::{PathStep, Term};
use crate::kernel::unifier::{Scope, Unifier};
use crate::kernel::variable_map::VariableMap;
use crate::kernel::{EqualityGraph, StepId};

/// Result of evaluating whether a literal can be eliminated during simplification.
enum LiteralElimination {
    /// The literal is self-contradictory (e.g., x != x).
    Impossible,
    /// The literal was eliminated by matching an existing clause.
    Eliminated { step: usize, flipped: bool },
}

/// The ActiveSet stores a bunch of clauses that are indexed for various efficient lookups.
/// The goal is that, given a new clause, it is efficient to determine what can be concluded
/// given that clause and one clause from the active set.
/// "Efficient" is relative - this still may take time roughly linear to the size of the active set.
#[derive(Clone)]
pub struct ActiveSet {
    // A vector for indexed reference
    steps: Vec<ProofStep>,

    // The long clauses (ie more than one literal) that we have proven.
    long_clauses: HashSet<Clause>,

    // The short clauses (ie just one literal) that we have proven.
    literal_set: LiteralSet,

    // An index of all the positive literals that we can do resolution with.
    positive_res_targets: FingerprintUnifier<ResolutionTarget>,

    // An index of all the negative literals that we can do resolution with.
    negative_res_targets: FingerprintUnifier<ResolutionTarget>,

    // A graph that encodes equalities and inequalities between terms.
    pub graph: EqualityGraph,

    // Information about every subterm that appears in an activated concrete literal,
    // except "true".
    subterms: Vec<SubtermInfo>,

    // An index to find the id of a subterm for an exact match.
    subterm_map: HashMap<Term, usize>,

    // An index to find the id of subterms for a pattern match.
    subterm_unifier: FingerprintUnifier<usize>,

    // A data structure to do the mechanical rewriting of subterms.
    rewrite_tree: RewriteTree,
}

/// A ResolutionTarget represents a literal that we could do resolution with.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ResolutionTarget {
    // Which proof step the resolution target is in.
    step_index: usize,

    // Which literal within the clause the resolution target is in.
    literal_index: usize,

    // Whether we index starting with the left term of the literal.
    // (As opposed to the right term.)
    left: bool,
}

/// Information about a subterm that appears in an activated concrete literal.
#[derive(Clone)]
struct SubtermInfo {
    // The subterm itself
    term: Term,

    // Where the subterm occurs, in activated concrete literals.
    locations: Vec<SubtermLocation>,

    // The possible terms that this subterm can be rewritten to.
    // Note that this contains duplicates.
    // We do use duplicates to prevent factual-factual rewrites, but it is displeasing.
    rewrites: Vec<Rewrite>,

    // The inspiration id for a subterm is the first activated concrete proof step that contains it.
    inspiration_id: usize,
}

/// A SubtermLocation describes somewhere that the subterm exists among the activated clauses.
/// Subterm locations always refer to concrete single-literal clauses.
#[derive(Clone)]
struct SubtermLocation {
    // Which proof step the subterm is in.
    // The literal can be either positive or negative.
    target_id: usize,

    // Whether the subterm is in the left term of the literal.
    // (As opposed to the right one.)
    left: bool,

    // The path from the root term to the subterm.
    // Uses PathStep::Function/Argument to navigate the curried term structure.
    // An empty path means the root, so the whole term is the relevant subterm.
    path: Vec<PathStep>,
}

/// A context for validating proof steps using the ActiveSet.
/// Implements ProofResolver to allow using the same reconstruction logic
/// for validation at creation time.
pub struct ValidationContext<'a> {
    active_set: &'a ActiveSet,
    kernel_context: &'a KernelContext,
    /// A pending step that's about to be added to the active set.
    /// This allows validation to reference the activating step before it's actually added.
    pending_step: Option<(usize, &'a Clause)>,
}

impl<'a> ValidationContext<'a> {
    pub fn new(active_set: &'a ActiveSet, kernel_context: &'a KernelContext) -> Self {
        ValidationContext {
            active_set,
            kernel_context,
            pending_step: None,
        }
    }

    /// Create a validation context that includes a pending step.
    /// The pending step will be available at the given ID even though it's not yet in the active set.
    pub fn with_pending_step(
        active_set: &'a ActiveSet,
        kernel_context: &'a KernelContext,
        pending_id: usize,
        pending_clause: &'a Clause,
    ) -> Self {
        ValidationContext {
            active_set,
            kernel_context,
            pending_step: Some((pending_id, pending_clause)),
        }
    }
}

impl ProofResolver for ValidationContext<'_> {
    fn get_clause(&self, id: ProofStepId) -> Result<&Clause, Error> {
        match id {
            ProofStepId::Active(i) => {
                // First check if this is the pending step
                if let Some((pending_id, pending_clause)) = self.pending_step {
                    if i == pending_id {
                        return Ok(pending_clause);
                    }
                }
                // Otherwise look in the active set
                self.active_set
                    .steps
                    .get(i)
                    .map(|s| &s.clause)
                    .ok_or_else(|| Error::internal(format!("step {} not found in active set", i)))
            }
            ProofStepId::Passive(_) => Err(Error::internal(
                "passive steps not available during validation",
            )),
            ProofStepId::Final => Err(Error::internal(
                "final step not available during validation",
            )),
        }
    }

    fn kernel_context(&self) -> &KernelContext {
        self.kernel_context
    }
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            steps: vec![],
            long_clauses: HashSet::new(),
            literal_set: LiteralSet::new(),
            positive_res_targets: FingerprintUnifier::new(),
            negative_res_targets: FingerprintUnifier::new(),
            graph: EqualityGraph::new(),
            subterms: vec![],
            subterm_map: HashMap::new(),
            subterm_unifier: FingerprintUnifier::new(),
            rewrite_tree: RewriteTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    fn is_known_long_clause(&self, clause: &Clause) -> bool {
        clause.literals.len() > 1 && self.long_clauses.contains(clause)
    }

    /// Finds all resolutions that can be done with a given proof step.
    /// The "new clause" is the one that is being activated, and the "old clause" is the existing one.
    pub fn find_resolutions(
        &self,
        new_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        let new_step_id = self.next_id();
        for (i, new_literal) in new_step.clause.literals.iter().enumerate() {
            let target_map = if new_literal.positive {
                &self.negative_res_targets
            } else {
                &self.positive_res_targets
            };

            let targets = target_map.find_unifying(
                &new_literal.left,
                new_step.clause.get_local_context(),
                kernel_context,
            );
            for target in targets {
                let old_step = self.get_step(target.step_index);
                let flipped = !target.left;

                if new_step.truthiness == Truthiness::Factual
                    && old_step.truthiness == Truthiness::Factual
                {
                    // No global-global resolution
                    continue;
                }

                let step = if new_literal.positive {
                    self.try_resolution(
                        new_step_id,
                        new_step,
                        i,
                        target.step_index,
                        old_step,
                        target.literal_index,
                        flipped,
                        kernel_context,
                    )
                } else {
                    self.try_resolution(
                        target.step_index,
                        old_step,
                        target.literal_index,
                        new_step_id,
                        new_step,
                        i,
                        flipped,
                        kernel_context,
                    )
                };

                if let Some(step) = step {
                    output.push(step);
                }
            }
        }
    }

    /// Tries to do a resolution from two clauses. This works when two literals can be unified
    /// in such a way that they contradict each other.
    ///
    /// There are two ways that A = B and C != D can contradict.
    /// When u(A) = u(C) and u(B) = u(D), that is "not flipped".
    /// When u(A) = u(D) and u(B) = u(C), that is "flipped".
    ///
    /// To do resolution, one of the literals must be positive, and the other must be negative.
    fn try_resolution(
        &self,
        pos_id: usize,
        pos_step: &ProofStep,
        pos_index: usize,
        neg_id: usize,
        neg_step: &ProofStep,
        neg_index: usize,
        flipped: bool,
        kernel_context: &KernelContext,
    ) -> Option<ProofStep> {
        let pos_clause = &pos_step.clause;
        assert!(pos_clause.literals[pos_index].positive);

        let neg_clause = &neg_step.clause;
        assert!(!neg_clause.literals[neg_index].positive);

        // Figure out which of the positive and negative clauses are long and short.
        let (short_id, short_step, short_index, long_id, long_step, long_index) =
            if pos_clause.len() < neg_clause.len() {
                (pos_id, pos_step, pos_index, neg_id, neg_step, neg_index)
            } else {
                (neg_id, neg_step, neg_index, pos_id, pos_step, pos_index)
            };
        let short_clause = &short_step.clause;
        let long_clause = &long_step.clause;

        // Do some heuristic filtering before trying unification, because unification is expensive.

        // We do only the simplest form of two-long-clause resolution.
        // Concluding from concrete "A or B" and "not A or B" that "B" is true.
        // So let's allow that case, and return None otherwise.
        if short_clause.len() > 1 {
            if short_clause.len() != 2 || long_clause.len() != 2 {
                return None;
            }
            if short_clause.has_any_variable() || long_clause.has_any_variable() {
                return None;
            }
        }

        // Check the non-matching short literal.
        // This code would support short clauses longer than two literals, if we wanted.
        for (i, literal) in short_clause.literals.iter().enumerate() {
            if i == short_index {
                continue;
            }
            if literal.has_any_variable() {
                return None;
            }
            if let Some(index) = long_clause.literals.iter().position(|lit| lit == literal) {
                if index == long_index {
                    // This is a weird case. Two different literals in the short clause
                    // match the same literal in the long clause.
                    return None;
                }

                // This is the good case, where the other parts of the short clause match
                // things already in the long clause, thus we can ignore them
                continue;
            }
            return None;
        }

        // Heuristics done. Let's unify.
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, short_clause.get_local_context());
        unifier.set_input_context(Scope::RIGHT, long_clause.get_local_context());

        // The short clause is "left" scope and the long clause is "right" scope.
        // This is different from the "left" and "right" of the literals - unfortunately
        // "left" and "right" are a bit overloaded here.
        let short_a = &short_clause.literals[short_index].left;
        let short_b = &short_clause.literals[short_index].right;
        let (long_a, long_b) = if flipped {
            (
                &long_clause.literals[long_index].right,
                &long_clause.literals[long_index].left,
            )
        } else {
            (
                &long_clause.literals[long_index].left,
                &long_clause.literals[long_index].right,
            )
        };
        if !unifier.unify(Scope::LEFT, short_a, Scope::RIGHT, long_a) {
            return None;
        }
        if !unifier.unify(Scope::LEFT, short_b, Scope::RIGHT, long_b) {
            return None;
        }

        let mut literals = vec![];
        for (i, literal) in long_clause.literals.iter().enumerate() {
            if i == long_index {
                continue;
            }
            let left = unifier.apply(Scope::RIGHT, &literal.left);
            let right = unifier.apply(Scope::RIGHT, &literal.right);
            let (new_literal, _) = Literal::new_with_flip(literal.positive, left, right);
            literals.push(new_literal);
        }

        // Check inhabitedness for eliminated variables from BOTH premises.
        // A variable is "eliminated" if, after unification, it contributes no
        // output variables to the resulting clause. Resolution is only sound
        // when such eliminated variables have inhabited types.
        let mut output_vars: HashSet<AtomId> = HashSet::new();
        for literal in &literals {
            for atom in literal.iter_atoms() {
                if let Atom::FreeVariable(id) = atom {
                    output_vars.insert(*id);
                }
            }
        }

        let mut check_eliminated_vars = |scope: Scope, context: &LocalContext| -> bool {
            for var_id in 0..context.len() {
                // Apply the unifier to a variable term to get its mapped value.
                let var_term = Term::new_variable(var_id as AtomId);
                let mapped_term = unifier.apply(scope, &var_term);

                // If mapped to concrete term (no variables), the variable was instantiated.
                if !mapped_term.has_any_variable() {
                    continue;
                }

                // Check if any output variables in mapped_term appear in output literals.
                let appears_in_output = mapped_term.iter_atoms().any(|atom| {
                    if let Atom::FreeVariable(out_var) = atom {
                        output_vars.contains(out_var)
                    } else {
                        false
                    }
                });

                // If no output variables appear in output, this variable is eliminated.
                if !appears_in_output {
                    if let Some(var_type) = context.get_var_type(var_id) {
                        // Translate the type to output scope for inhabitedness check.
                        let translated_type = unifier.apply(scope, var_type);
                        if !kernel_context
                            .provably_inhabited(&translated_type, Some(unifier.output_context()))
                        {
                            return false;
                        }
                    }
                }
            }
            true
        };

        let short_context = short_clause.get_local_context();
        if !check_eliminated_vars(Scope::LEFT, short_context) {
            return None;
        }
        let long_context = long_clause.get_local_context();
        if !check_eliminated_vars(Scope::RIGHT, long_context) {
            return None;
        }

        // Gather the output data including variable maps for reconstruction
        let (all_maps, context) = unifier.into_maps_with_context();
        let mut short_var_map = VariableMap::new();
        let mut long_var_map = VariableMap::new();
        for (scope, map) in all_maps {
            if scope == Scope::LEFT {
                short_var_map = map;
            } else if scope == Scope::RIGHT {
                long_var_map = map;
            }
        }

        let (clause, var_ids) = Clause::normalize_with_var_ids(literals, &context);

        let premise_map = PremiseMap::new(
            vec![short_var_map.clone(), long_var_map.clone()],
            var_ids,
            context.clone(),
        );

        // Debug: validate resolution output before creating step
        // Note: use clause.get_local_context() because literals have been renormalized
        #[cfg(feature = "validate")]
        for (i, literal) in clause.literals.iter().enumerate() {
            let left_type = literal
                .left
                .get_type_with_context(clause.get_local_context(), kernel_context);
            let right_type = literal
                .right
                .get_type_with_context(clause.get_local_context(), kernel_context);
            if left_type != right_type {
                eprintln!("RESOLUTION PRODUCED TYPE MISMATCH:");
                eprintln!("  Short clause (id={}): {}", short_id, short_clause);
                eprintln!("  Short context: {:?}", short_clause.get_local_context());
                eprintln!("  Long clause (id={}): {}", long_id, long_clause);
                eprintln!("  Long context: {:?}", long_clause.get_local_context());
                eprintln!("  Long index (eliminated): {}", long_index);
                eprintln!("  Short index (eliminated): {}", short_index);
                eprintln!("  Flipped: {}", flipped);
                eprintln!("  Pre-normalization context: {:?}", context);
                eprintln!("  Result clause: {}", clause);
                eprintln!("  Result context: {:?}", clause.get_local_context());
                eprintln!("  Literal {}: {}", i, literal);
                eprintln!("  Left type: {:?}", left_type);
                eprintln!("  Right type: {:?}", right_type);
            }
        }

        let step = ProofStep::resolution(
            long_id,
            long_step,
            short_id,
            short_step,
            clause,
            premise_map,
        );
        Some(step)
    }

    /// Look for ways to rewrite a literal that is not yet in the active set.
    /// The literal must be concrete.
    /// The naming convention is that we use the pattern s->t to rewrite u in u ?= v.
    pub fn activate_rewrite_target(
        &mut self,
        target_id: usize,
        target_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        assert!(target_step.clause.len() == 1);
        let target_literal = &target_step.clause.literals[0];

        for (target_left, u, _) in target_literal.both_term_pairs() {
            let u_subterms = u.rewritable_subterms_with_paths();

            for (path, u_subterm) in u_subterms {
                // Skip subterms whose types contain BoundVariables (e.g., bare polymorphic constants).
                // These can't be meaningfully rewritten without type instantiation.
                let subterm_type =
                    u_subterm.get_type_with_context(LocalContext::empty_ref(), kernel_context);
                if subterm_type.has_bound_variable() {
                    continue;
                }

                let u_subterm_id = if let Some(id) = self.subterm_map.get(&u_subterm) {
                    // We already have data for this subterm.
                    *id
                } else {
                    // We've never seen this subterm before.
                    // We need to find all the possible rewrites for it.
                    // Note: concrete terms (no variables), so empty local context is safe.
                    let rewrites = self.rewrite_tree.get_rewrites(
                        &u_subterm,
                        0,
                        LocalContext::empty_ref(),
                        kernel_context,
                    );

                    // Validate rewrites from the rewrite tree
                    #[cfg(feature = "validate")]
                    for rewrite in &rewrites {
                        if !rewrite.term.has_any_variable() {
                            // Create a literal representing the rewrite: u_subterm = rewrite.term
                            let (lit, flipped) = if rewrite.forwards {
                                Literal::new_with_flip(
                                    true,
                                    u_subterm.clone(),
                                    rewrite.term.clone(),
                                )
                            } else {
                                Literal::new_with_flip(
                                    true,
                                    rewrite.term.clone(),
                                    u_subterm.clone(),
                                )
                            };

                            // Get the pattern clause and try to unify
                            let pattern_step = self.get_step(rewrite.pattern_id);
                            let pattern_lit = &pattern_step.clause.literals[0];

                            // Use the unifier to check if this specialization is valid
                            let mut unifier = Unifier::new(3, kernel_context);
                            unifier.set_input_context(
                                Scope::LEFT,
                                pattern_step.clause.get_local_context(),
                            );
                            unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());

                            let unified = unifier.unify_literals(
                                Scope::LEFT,
                                pattern_lit,
                                Scope::RIGHT,
                                &lit,
                                flipped,
                            );

                            if !unified {
                                panic!(
                                    "Rewrite tree produced invalid rewrite!\n\
                                     Pattern id: {}\n\
                                     Pattern clause: {}\n\
                                     Pattern context: {:?}\n\
                                     Subterm: {}\n\
                                     Rewrite term: {}\n\
                                     Forwards: {}",
                                    rewrite.pattern_id,
                                    pattern_step.clause,
                                    pattern_step.clause.get_local_context().get_var_types(),
                                    u_subterm,
                                    rewrite.term,
                                    rewrite.forwards
                                );
                            }
                        }
                    }

                    // Add these rewrites to the term graph (only if both terms are concrete)
                    let id1 = self.graph.insert_term(&u_subterm, kernel_context);
                    for rewrite in &rewrites {
                        // rewrite.term may have variables if the pattern had variables
                        // that weren't fully matched. Only add to term graph if concrete.
                        if !rewrite.term.has_any_variable() {
                            let id2 = self.graph.insert_term(&rewrite.term, kernel_context);
                            self.add_to_term_graph(
                                rewrite.pattern_id,
                                Some(target_id),
                                id1,
                                id2,
                                rewrite.forwards,
                                true,
                            );
                        }
                    }

                    // Populate the subterm info.
                    let id = self.subterms.len();
                    self.subterms.push(SubtermInfo {
                        term: u_subterm.clone(),
                        locations: vec![],
                        rewrites,
                        inspiration_id: target_id,
                    });
                    self.subterm_map.insert(u_subterm.clone(), id);
                    // Subterms are concrete (no variables), so empty local context is safe
                    self.subterm_unifier.insert(
                        &u_subterm,
                        id,
                        LocalContext::empty_ref(),
                        kernel_context,
                    );
                    id
                };

                // Apply all the ways to rewrite u_subterm.
                for rewrite in &self.subterms[u_subterm_id].rewrites {
                    if target_id == rewrite.pattern_id {
                        // Don't rewrite a literal with itself
                        continue;
                    }

                    let pattern_step = self.get_step(rewrite.pattern_id);
                    if target_step.truthiness == Truthiness::Factual
                        && pattern_step.truthiness == Truthiness::Factual
                    {
                        // No global-global rewriting
                        continue;
                    }

                    // Validate the rewrite using the unifier to check typeclass constraints.
                    // The PDT finds structural matches but doesn't validate typeclass constraints.
                    let pattern_literal = &pattern_step.clause.literals[0];
                    let (s, t) = if rewrite.forwards {
                        (&pattern_literal.left, &pattern_literal.right)
                    } else {
                        (&pattern_literal.right, &pattern_literal.left)
                    };
                    let mut unifier = Unifier::new(3, kernel_context);
                    unifier.set_input_context(Scope::LEFT, pattern_step.clause.get_local_context());
                    unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());
                    if !unifier.unify(Scope::LEFT, s, Scope::RIGHT, &u_subterm) {
                        // Typeclass constraint not satisfied - skip this rewrite
                        continue;
                    }

                    // Apply the unifier to the replacement term to create mappings for all
                    // pattern variables. This is needed for proof reconstruction - without it,
                    // variables that only appear in the replacement side won't have mappings.
                    let _ = unifier.apply(Scope::LEFT, t);

                    // Extract the pattern's variable map for reconstruction
                    let (all_maps, _) = unifier.into_maps_with_context();
                    let pattern_var_map = all_maps
                        .into_iter()
                        .find(|(scope, _)| *scope == Scope::LEFT)
                        .map(|(_, map)| map)
                        .unwrap_or_else(VariableMap::new);

                    let ps = ProofStep::rewrite(
                        rewrite.pattern_id,
                        &pattern_step,
                        target_id,
                        target_step,
                        target_left,
                        &path,
                        &rewrite.term,
                        &rewrite.context,
                        pattern_var_map,
                    );

                    // Debug: validate rewrite step types
                    #[cfg(any(test, feature = "validate"))]
                    for (i, lit) in ps.clause.literals.iter().enumerate() {
                        let ctx = ps.clause.get_local_context();
                        let left_type = lit.left.get_type_with_context(ctx, kernel_context);
                        let right_type = lit.right.get_type_with_context(ctx, kernel_context);
                        if left_type != right_type {
                            eprintln!("Type mismatch in rewrite step (activate_rewrite_target):");
                            eprintln!("  Pattern id: {}", rewrite.pattern_id);
                            eprintln!("  Pattern step: {}", pattern_step.clause);
                            eprintln!(
                                "  Pattern context: {:?}",
                                pattern_step.clause.get_local_context()
                            );
                            eprintln!("  Target id: {}", target_id);
                            eprintln!("  Target step: {}", target_step.clause);
                            eprintln!(
                                "  Target context: {:?}",
                                target_step.clause.get_local_context()
                            );
                            eprintln!("  Target left: {}", target_left);
                            eprintln!("  Path: {:?}", path);
                            eprintln!("  Subterm being rewritten: {}", u_subterm);
                            eprintln!("  Forwards: {}", rewrite.forwards);
                            eprintln!("  New subterm: {}", rewrite.term);
                            eprintln!("  Rewrite context: {:?}", rewrite.context);
                            eprintln!("  Result clause: {}", ps.clause);
                            eprintln!("  Result context: {:?}", ps.clause.get_local_context());
                            eprintln!("  Literal {}: {}", i, lit);
                            eprintln!("  Left type: {:?}", left_type);
                            eprintln!("  Right type: {:?}", right_type);
                            panic!("Type mismatch in rewrite");
                        }
                    }

                    output.push(ps);
                }

                // Record the location of this subterm.
                self.subterms[u_subterm_id].locations.push(SubtermLocation {
                    target_id,
                    left: target_left,
                    path,
                });
            }
        }
    }

    /// When we have a new rewrite pattern, find everything that we can rewrite with it.
    /// The naming convention is that we use the pattern s->t to rewrite u in u ?= v.
    pub fn activate_rewrite_pattern(
        &mut self,
        pattern_id: usize,
        pattern_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        assert!(pattern_step.clause.len() == 1);
        let pattern_literal = &pattern_step.clause.literals[0];
        assert!(pattern_literal.positive);

        for (forwards, s, t) in pattern_literal.both_term_pairs() {
            if s.is_true() {
                // Don't rewrite from "true"
                continue;
            }

            // Look for existing subterms that match s
            // Note: s comes from the pattern clause, subterms are concrete
            let subterm_ids: Vec<usize> = self
                .subterm_unifier
                .find_unifying(s, pattern_step.clause.get_local_context(), kernel_context)
                .iter()
                .map(|&x| *x)
                .collect();

            for subterm_id in subterm_ids {
                let subterm_info = &self.subterms[subterm_id];
                let subterm = &subterm_info.term;

                let mut unifier = Unifier::new(3, kernel_context);
                unifier.set_input_context(Scope::LEFT, pattern_step.clause.get_local_context());
                // Subterms are concrete (no variables), so empty local context is fine
                unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());
                if !unifier.unify(Scope::LEFT, s, Scope::RIGHT, subterm) {
                    continue;
                }
                let new_subterm = unifier.apply(Scope::LEFT, t);
                let new_subterm_context = unifier.output_context().clone();

                // Extract the pattern's variable map for reconstruction
                let (all_maps, _) = unifier.into_maps_with_context();
                let pattern_var_map = all_maps
                    .into_iter()
                    .find(|(scope, _)| *scope == Scope::LEFT)
                    .map(|(_, map)| map)
                    .unwrap_or_else(VariableMap::new);

                for location in &subterm_info.locations {
                    if location.target_id == pattern_id {
                        // Don't rewrite a literal with itself
                        continue;
                    }
                    let target_id = location.target_id;
                    let target_step = self.get_step(target_id);

                    if pattern_step.truthiness == Truthiness::Factual
                        && target_step.truthiness == Truthiness::Factual
                    {
                        // No global-global rewriting
                        continue;
                    }

                    let ps = ProofStep::rewrite(
                        pattern_id,
                        pattern_step,
                        target_id,
                        target_step,
                        location.left,
                        &location.path,
                        &new_subterm,
                        &new_subterm_context,
                        pattern_var_map.clone(),
                    );
                    output.push(ps);
                }

                // Add this rewrite to the term graph.
                // Only add to term graph if both terms are concrete (no variables).
                // The subterm is always concrete, but new_subterm may have variables
                // if the pattern had variables that weren't fully unified.
                if !new_subterm.has_any_variable() {
                    let id1 = self.graph.insert_term(&subterm, kernel_context);
                    let id2 = self.graph.insert_term(&new_subterm, kernel_context);
                    self.add_to_term_graph(
                        pattern_id,
                        Some(subterm_info.inspiration_id),
                        id1,
                        id2,
                        forwards,
                        true,
                    );
                }

                self.subterms[subterm_id].rewrites.push(Rewrite {
                    pattern_id,
                    forwards,
                    term: new_subterm,
                    context: new_subterm_context,
                });
            }
        }
    }

    /// Tries to do inference using the equality resolution (ER) rule.
    /// Specifically, when one literal is of the form
    ///   u != v
    /// then if we can unify u and v, we can eliminate this literal from the clause.
    pub fn equality_resolution(
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];
        let original_context = clause.get_local_context();

        // Use the new method to find all possible equality resolutions
        for (new_literals, context, input_var_map) in
            inference::find_equality_resolutions(clause, kernel_context)
        {
            // Check inhabitedness for eliminated variables.
            // We only need to check when a variable's type depends on other type variables
            // (which might be uninhabited). For concrete types, the prover's standard
            // behavior is correct.
            // Variables in the original clause that don't appear in new_literals are eliminated.
            let mut output_vars: HashSet<AtomId> = HashSet::new();
            for literal in &new_literals {
                for atom in literal.iter_atoms() {
                    if let Atom::FreeVariable(id) = atom {
                        output_vars.insert(*id);
                    }
                }
            }

            let mut skip = false;
            for var_id in 0..original_context.len() {
                if !output_vars.contains(&(var_id as AtomId)) {
                    // This variable is eliminated - check if its type is provably inhabited
                    if let Some(var_type) = original_context.get_var_type(var_id) {
                        // Only check inhabitedness if the type contains free variables
                        // (i.e., depends on type parameters that might be uninhabited)
                        if var_type.has_any_variable()
                            && !kernel_context.provably_inhabited(var_type, Some(original_context))
                        {
                            skip = true;
                            break;
                        }
                    }
                }
            }
            if skip {
                continue;
            }

            let (new_clause, var_ids) = Clause::normalize_with_var_ids(new_literals, &context);

            // Check if normalization resulted in a tautology
            if !new_clause.is_tautology() {
                let premise_map = PremiseMap::new(
                    vec![input_var_map.clone()],
                    var_ids.clone(),
                    context.clone(),
                );
                let step = ProofStep::direct(
                    activated_step,
                    Rule::EqualityResolution(SingleSourceInfo { id: activated_id }),
                    new_clause,
                    premise_map,
                );
                answer.push(step);
            }
        }

        answer
    }

    /// Tries to do inference using the function elimination (FE) rule.
    /// Note that I just made up this rule, it isn't part of standard superposition.
    /// Apply injectivity to derive inequalities from function inequalities.
    /// When f(a, b, d) != f(a, c, d), that implies that b != c.
    /// We can run this operation on any negative literal in the clause.
    pub fn injectivity(
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let original_context = clause.get_local_context();
        let mut answer = vec![];

        for literals in clause.find_injectivities() {
            // Check inhabitedness for eliminated variables.
            // We only need to check when a variable's type depends on other type variables
            // (which might be uninhabited). For concrete types, the prover's standard
            // behavior is correct.
            // Collect variables that appear in the new literals.
            let mut output_vars: HashSet<AtomId> = HashSet::new();
            for literal in &literals {
                for atom in literal.iter_atoms() {
                    if let Atom::FreeVariable(id) = atom {
                        output_vars.insert(*id);
                    }
                }
            }

            let mut skip = false;
            for var_id in 0..original_context.len() {
                if !output_vars.contains(&(var_id as AtomId)) {
                    // This variable is eliminated - check if its type is provably inhabited
                    if let Some(var_type) = original_context.get_var_type(var_id) {
                        // Only check inhabitedness if the type contains free variables
                        // (i.e., depends on type parameters that might be uninhabited)
                        if var_type.has_any_variable()
                            && !kernel_context.provably_inhabited(var_type, Some(original_context))
                        {
                            skip = true;
                            break;
                        }
                    }
                }
            }
            if skip {
                continue;
            }

            let context = original_context.clone();
            let (clause, var_ids) = Clause::normalize_with_var_ids(literals, &context);
            let premise_map = PremiseMap::new(vec![VariableMap::new()], var_ids, context);
            let step = ProofStep::direct(
                activated_step,
                Rule::Injectivity(SingleSourceInfo { id: activated_id }),
                clause,
                premise_map,
            );
            answer.push(step);
        }

        answer
    }

    /// Apply boolean reduction to derive new clauses.
    pub fn boolean_reduction(
        &self,
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        for literals in clause.find_boolean_reductions(kernel_context) {
            let context = activated_step.clause.get_local_context().clone();
            let (clause, var_ids) = Clause::normalize_with_var_ids(literals, &context);
            let premise_map = PremiseMap::new(vec![VariableMap::new()], var_ids, context);
            let step = ProofStep::direct(
                activated_step,
                Rule::BooleanReduction(SingleSourceInfo { id: activated_id }),
                clause,
                premise_map,
            );
            answer.push(step);
        }

        answer
    }

    /// Apply extensionality to derive function equality from pointwise equality.
    /// When f(x1, x2, ...) = g(x1, x2, ...) for all arguments, that implies f = g.
    pub fn extensionality(
        &self,
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        if let Some(literals) = clause.find_extensionality(kernel_context) {
            let context = activated_step.clause.get_local_context().clone();
            let (clause, var_ids) = Clause::normalize_with_var_ids(literals, &context);
            let premise_map = PremiseMap::new(vec![VariableMap::new()], var_ids, context);
            let step = ProofStep::direct(
                activated_step,
                Rule::Extensionality(SingleSourceInfo { id: activated_id }),
                clause,
                premise_map,
            );
            answer.push(step);
        }

        answer
    }

    /// Tries to do inference using the equality factoring (EF) rule.
    ///
    /// Given:
    ///   s = t | u = v | R
    /// if we can unify s and u, we can rewrite it to:
    ///   t != v | u = v | R
    ///
    /// "s = t" must be the first clause, but "u = v" can be any of them.
    ///
    /// I find this rule to be unintuitive, extracting an inequality from only equalities.
    pub fn equality_factoring(
        activated_id: usize,
        activated_step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Vec<ProofStep> {
        let clause = &activated_step.clause;
        let mut answer = vec![];

        // Use the clause's helper method to find all factorings
        let factorings = inference::find_equality_factorings(clause, kernel_context);

        for (literals, output_context, input_var_map) in factorings {
            // Create the new clause using the unifier's output context
            let (new_clause, var_ids) = Clause::normalize_with_var_ids(literals, &output_context);

            let premise_map = PremiseMap::new(vec![input_var_map.clone()], var_ids, output_context);
            let step = ProofStep::direct(
                activated_step,
                Rule::EqualityFactoring(SingleSourceInfo { id: activated_id }),
                new_clause,
                premise_map,
            );
            answer.push(step);
        }

        answer
    }

    pub fn get_clause(&self, index: usize) -> &Clause {
        &self.steps[index].clause
    }

    pub fn has_step(&self, index: usize) -> bool {
        index < self.steps.len()
    }

    pub fn get_step(&self, index: usize) -> &ProofStep {
        &self.steps[index]
    }

    /// Iterate over all active proof steps.
    pub fn iter_steps(&self) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.steps.iter().enumerate()
    }

    /// Iterate over all proof steps that depend on this id.
    pub fn find_consequences(&self, id: usize) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.steps
            .iter()
            .enumerate()
            .filter(move |(_, step)| step.depends_on_active(id))
    }

    /// Returns (value, elimination) when this literal's value is known due to some existing clause.
    fn evaluate_literal(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<(bool, LiteralElimination)> {
        #[cfg(any(test, feature = "validate"))]
        literal.validate_type(local_context, kernel_context);
        if literal.left == literal.right {
            return Some((literal.positive, LiteralElimination::Impossible));
        }
        match self
            .literal_set
            .find_generalization(&literal, local_context, kernel_context)
        {
            Some((positive, step, flipped)) => {
                Some((positive, LiteralElimination::Eliminated { step, flipped }))
            }
            None => None,
        }
    }

    /// Validates that a ProofStep's stored information is self-consistent.
    /// Uses the same logic as proof reconstruction to verify that the trace
    /// correctly describes how the clause was derived.
    ///
    /// This is used to catch bugs in trace composition early, rather than
    /// during proof reconstruction.
    #[cfg(any(test, feature = "validate"))]
    pub fn validate_step(
        &self,
        step: &ProofStep,
        kernel_context: &KernelContext,
    ) -> Result<(), Error> {
        let ctx = ValidationContext::new(self, kernel_context);
        let conclusion_map = VariableMap::new();
        let conclusion_context = step.clause.get_local_context();
        let mut concrete_steps: HashMap<ConcreteStepId, ConcreteStep> = HashMap::new();

        // Use a placeholder ID since the step isn't activated yet
        let id = ProofStepId::Active(self.len());

        reconstruct_step(
            &ctx,
            id,
            step,
            conclusion_map,
            conclusion_context,
            &mut concrete_steps,
        )
    }

    /// Validates a proof step, including a pending step that's about to be added.
    /// The pending step will be available at pending_id even though it's not yet in the active set.
    #[cfg(any(test, feature = "validate"))]
    pub fn validate_step_with_pending(
        &self,
        step: &ProofStep,
        kernel_context: &KernelContext,
        pending_id: usize,
        pending_clause: &Clause,
    ) -> Result<(), Error> {
        let ctx =
            ValidationContext::with_pending_step(self, kernel_context, pending_id, pending_clause);
        let conclusion_map = VariableMap::new();
        let conclusion_context = step.clause.get_local_context();
        let mut concrete_steps: HashMap<ConcreteStepId, ConcreteStep> = HashMap::new();

        // Use a placeholder ID since the step isn't activated yet
        let id = ProofStepId::Active(self.len());

        reconstruct_step(
            &ctx,
            id,
            step,
            conclusion_map,
            conclusion_context,
            &mut concrete_steps,
        )
    }

    /// Simplifies the clause based on both structural rules and the active set.
    /// If the result is redundant given what's already known, return None.
    /// Specializations are allowed, though, even if they're redundant.
    /// If the result is an impossibility, return an empty clause.
    pub fn simplify(
        &self,
        mut step: ProofStep,
        kernel_context: &KernelContext,
    ) -> Option<ProofStep> {
        if step.clause.is_tautology() {
            return None;
        }

        if self.is_known_long_clause(&step.clause) {
            return None;
        }

        // Filter out any literals that are known to be true
        let mut new_rules = vec![];
        let initial_num_literals = step.clause.literals.len();
        let mut output_literals = vec![];
        let local_context = step.clause.get_local_context().clone();

        // Debug: validate all literals before processing
        #[cfg(any(test, feature = "validate"))]
        for (i, literal) in step.clause.literals.iter().enumerate() {
            let left_type = literal
                .left
                .get_type_with_context(&local_context, kernel_context);
            let right_type = literal
                .right
                .get_type_with_context(&local_context, kernel_context);
            if left_type != right_type {
                eprintln!("Type mismatch in step being simplified:");
                eprintln!("  Step rule: {}", step.rule.name());
                eprintln!("  Step clause: {}", step.clause);
                eprintln!("  Literal {}: {}", i, literal);
                eprintln!("  Left type: {:?}", left_type);
                eprintln!("  Right type: {:?}", right_type);
                eprintln!("  Context: {:?}", local_context.get_var_types());
            }
        }

        // Clone the literals before consuming them, so we can restore the original step
        // if simplification happens (the original step is stored inline in Rule::Simplification).
        let original_literals = step.clause.literals.clone();
        let mut simplifying_var_maps: Vec<VariableMap> = vec![];
        for literal in std::mem::take(&mut step.clause.literals) {
            match self.evaluate_literal(&literal, &local_context, kernel_context) {
                Some((true, _)) => {
                    // This literal is already known to be true.
                    // Thus, the whole clause is a tautology.
                    return None;
                }
                Some((false, elimination)) => {
                    // This literal is already known to be false.
                    // Extract the var_map for the simplifying clause.
                    if let LiteralElimination::Eliminated {
                        step: simp_id,
                        flipped,
                    } = &elimination
                    {
                        let simp_step = self.get_step(*simp_id);
                        new_rules.push((*simp_id, simp_step));
                        if simp_step.clause.literals.len() == 1 {
                            let mut unifier = Unifier::new(3, kernel_context);
                            unifier.set_input_context(
                                Scope::LEFT,
                                simp_step.clause.get_local_context(),
                            );
                            unifier.set_input_context(Scope::RIGHT, &local_context);
                            let unified = unifier.unify_literals(
                                Scope::LEFT,
                                &simp_step.clause.literals[0],
                                Scope::RIGHT,
                                &literal,
                                *flipped,
                            );
                            if !unified {
                                let mut simp_var_map = VariableMap::new();
                                simp_var_map.match_literal(
                                    &simp_step.clause.literals[0],
                                    &literal,
                                    *flipped,
                                );
                                simplifying_var_maps.push(simp_var_map);
                            } else {
                                let (maps, _output_context) = unifier.into_maps_with_context();
                                let simp_var_map = maps
                                    .into_iter()
                                    .find(|(scope, _)| *scope == Scope::LEFT)
                                    .map(|(_, map)| map)
                                    .unwrap_or_else(VariableMap::new);
                                simplifying_var_maps.push(simp_var_map);
                            }
                        } else {
                            // Two-long-clause case - concrete, empty map
                            simplifying_var_maps.push(VariableMap::new());
                        }
                    }
                    continue;
                }
                None => {
                    output_literals.push(literal);
                }
            }
        }

        // Check inhabitedness for eliminated variables.
        // If simplification eliminates all occurrences of a variable, we need to verify
        // that variable's type is provably inhabited. Otherwise, the simplification is unsound.
        let mut output_vars: HashSet<AtomId> = HashSet::new();
        for literal in &output_literals {
            for atom in literal.iter_atoms() {
                if let Atom::FreeVariable(id) = atom {
                    output_vars.insert(*id);
                }
            }
        }

        for var_id in 0..local_context.len() {
            let var_id_atom = var_id as AtomId;
            if !output_vars.contains(&var_id_atom) {
                // This variable was eliminated - check if its type is provably inhabited
                if let Some(var_type) = local_context.get_var_type(var_id) {
                    if !kernel_context.provably_inhabited(var_type, Some(&local_context)) {
                        return None; // Reject the simplification
                    }
                }
            }
        }

        if output_literals.len() == initial_num_literals {
            // This proof step hasn't changed.
            step.clause.literals = output_literals;

            // Validate the unchanged step when the validate feature is enabled
            #[cfg(any(test, feature = "validate"))]
            if let Err(e) = self.validate_step(&step, kernel_context) {
                panic!(
                    "Invalid proof step (unchanged): {}\nStep clause: {}\nStep rule: {}",
                    e,
                    step.clause,
                    step.rule.name()
                );
            }

            return Some(step);
        }

        let pre_norm_context = step.clause.get_local_context().clone();
        let (clause, var_ids) = Clause::normalize_with_var_ids(output_literals, &pre_norm_context);
        if clause.is_tautology() {
            return None;
        }
        if self.is_known_long_clause(&clause) {
            return None;
        }

        // Compute combined truthiness, proof_size, depth from simplifying rules
        let mut truthiness = step.truthiness;
        let mut proof_size = step.proof_size;
        let mut depth = step.depth;
        let simplifying_ids: Vec<usize> = new_rules
            .iter()
            .map(|(id, short_step)| {
                truthiness = truthiness.combine(short_step.truthiness);
                proof_size += short_step.proof_size;
                depth = u32::max(depth, short_step.depth);
                *id
            })
            .collect();

        let premise_map = PremiseMap::new(simplifying_var_maps, var_ids, pre_norm_context);

        // Restore the original literals so the inline step has its complete clause
        step.clause.literals = original_literals;

        let result = ProofStep {
            clause,
            truthiness,
            rule: Rule::Simplification(SimplificationInfo {
                original: Box::new(step),
                simplifying_ids,
            }),
            proof_size,
            depth,
            premise_map,
        };

        // Validate the simplified step when the validate feature is enabled
        #[cfg(any(test, feature = "validate"))]
        if let Err(e) = self.validate_step(&result, kernel_context) {
            panic!(
                "Invalid proof step after simplification: {}\nStep clause: {}\nStep rule: {}",
                e,
                result.clause,
                result.rule.name()
            );
        }

        Some(result)
    }

    fn add_resolution_targets(
        &mut self,
        step_index: usize,
        literal_index: usize,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let tree = if literal.positive {
            &mut self.positive_res_targets
        } else {
            &mut self.negative_res_targets
        };
        tree.insert(
            &literal.left,
            ResolutionTarget {
                step_index,
                literal_index,
                left: true,
            },
            local_context,
            kernel_context,
        );
        tree.insert(
            &literal.right,
            ResolutionTarget {
                step_index,
                literal_index,
                left: false,
            },
            local_context,
            kernel_context,
        );
    }

    /// Indexes a clause so that it becomes available for future proof step generation.
    /// Return its id.
    fn insert(&mut self, step: ProofStep, kernel_context: &KernelContext) -> usize {
        let step_index = self.next_id();
        let clause = &step.clause;
        let local_context = clause.get_local_context();

        // Add resolution targets for the new clause.
        for (i, literal) in clause.literals.iter().enumerate() {
            self.add_resolution_targets(step_index, i, literal, local_context, kernel_context);
        }

        // Store long clauses here. Short clauses will be kept in the literal set.
        if clause.literals.len() > 1 {
            self.long_clauses.insert(clause.clone());
        }

        self.steps.push(step);
        step_index
    }

    pub fn next_id(&self) -> usize {
        self.steps.len()
    }

    // term1 and term2 are specializations of pattern_id.
    // If forwards, the pattern is term1 = term2. Otherwise, it is term2 = term1.
    fn add_to_term_graph(
        &mut self,
        pattern_id: usize,
        inspiration_id: Option<usize>,
        term1: TermId,
        term2: TermId,
        forwards: bool,
        equal: bool,
    ) {
        let (left, right) = if forwards {
            (term1, term2)
        } else {
            (term2, term1)
        };
        if equal {
            self.graph
                .set_terms_equal(left, right, StepId(pattern_id), inspiration_id.map(StepId));
        } else {
            assert!(inspiration_id.is_none());
            self.graph
                .set_terms_not_equal(left, right, StepId(pattern_id));
        }
    }

    /// Inference that is specific to literals.
    fn activate_literal(
        &mut self,
        activated_step: &ProofStep,
        output: &mut Vec<ProofStep>,
        kernel_context: &KernelContext,
    ) {
        let activated_id = self.next_id();
        assert_eq!(activated_step.clause.len(), 1);
        let literal = &activated_step.clause.literals[0];

        // Using the literal as a rewrite target.
        if !literal.has_any_variable() {
            // Add this to the term graph.
            let left = self.graph.insert_term(&literal.left, kernel_context);
            let right = self.graph.insert_term(&literal.right, kernel_context);

            self.add_to_term_graph(activated_id, None, left, right, true, literal.positive);

            // The activated step could be rewritten immediately.
            self.activate_rewrite_target(activated_id, &activated_step, output, kernel_context);
        }

        // Using the literal as a rewrite pattern.
        if literal.positive && !activated_step.rule.is_rewrite() {
            // The activated step could be used as a rewrite pattern immediately.
            self.activate_rewrite_pattern(activated_id, &activated_step, output, kernel_context);

            // Index it so that it can be used as a rewrite pattern in the future.
            self.rewrite_tree.insert_literal(
                activated_id,
                literal,
                activated_step.clause.get_local_context(),
            );
        }

        self.literal_set.insert(
            &literal,
            activated_id,
            activated_step.clause.get_local_context(),
        );
    }

    /// Generate all the inferences that can be made from a given clause, plus some existing clause.
    /// This function does not simplify the inferences, or use the inferences to simplify anything else.
    /// The prover will do all forms of simplification separately.
    /// After generation, this clause is added to the active set.
    /// Returns the id of the new clause, and pairs describing how the generated clauses were proved.
    pub fn activate(
        &mut self,
        activated_step: ProofStep,
        kernel_context: &KernelContext,
    ) -> (usize, Vec<ProofStep>) {
        let mut output = vec![];
        let activated_id = self.next_id();

        // Unification-based inferences don't need to be done on specialization, because
        // they can operate directly on the general form.
        for proof_step in
            ActiveSet::equality_resolution(activated_id, &activated_step, kernel_context)
        {
            output.push(proof_step);
        }

        for proof_step in
            ActiveSet::equality_factoring(activated_id, &activated_step, kernel_context)
        {
            output.push(proof_step);
        }

        for proof_step in ActiveSet::injectivity(activated_id, &activated_step, kernel_context) {
            output.push(proof_step);
        }

        for proof_step in self.boolean_reduction(activated_id, &activated_step, kernel_context) {
            output.push(proof_step);
        }

        for proof_step in self.extensionality(activated_id, &activated_step, kernel_context) {
            output.push(proof_step);
        }

        self.find_resolutions(&activated_step, &mut output, kernel_context);

        if activated_step.clause.len() == 1 {
            self.activate_literal(&activated_step, &mut output, kernel_context);
        }

        self.insert(activated_step, kernel_context);
        (activated_id, output)
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.steps.iter().map(|step| &step.clause)
    }

    /// Find the index of all clauses used to prove the provided step.
    pub fn find_upstream(
        &self,
        step: &ProofStep,
        include_inspiration: bool,
        output: &mut HashSet<usize>,
    ) {
        let mut pending = vec![];
        for i in step.active_dependencies(include_inspiration) {
            pending.push(i);
        }
        while !pending.is_empty() {
            let i = pending.pop().unwrap();
            if output.contains(&i) {
                continue;
            }
            output.insert(i);
            for j in self.get_step(i).active_dependencies(include_inspiration) {
                pending.push(j);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_activate_rewrite_pattern() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c1", "c2", "c3", "c4"], "Bool");

        // Create an active set that knows g0(c3, c4) = c2
        let mut set = ActiveSet::new();
        let clause = kctx.parse_clause("g0(c3, c4) = c2", &[]);
        let mut step = ProofStep::mock_from_clause(clause);
        step.truthiness = Truthiness::Hypothetical;
        set.activate(step, &kctx);

        // We should be able to replace c3 with c1 in "g0(c3, c4) = c2"
        let pattern_clause = kctx.parse_clause("c1 = c3", &[]);
        let pattern_step = ProofStep::mock_from_clause(pattern_clause);
        let mut result = vec![];
        set.activate_rewrite_pattern(1, &pattern_step, &mut result, &kctx);

        assert_eq!(result.len(), 1);
        let expected = kctx.parse_clause("g0(c1, c4) = c2", &[]);
        assert_eq!(result[0].clause, expected);
    }

    #[test]
    fn test_activate_rewrite_target() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c1", "c2", "c3", "c4"], "Bool");

        // Create an active set that knows c1 = c3
        let mut set = ActiveSet::new();
        let clause = kctx.parse_clause("c1 = c3", &[]);
        set.activate(ProofStep::mock_from_clause(clause), &kctx);

        // We want to use g0(c3, c4) = c2 to get g0(c1, c4) = c2.
        let target_clause = kctx.parse_clause("g0(c3, c4) = c2", &[]);
        let mut target_step = ProofStep::mock_from_clause(target_clause);
        target_step.truthiness = Truthiness::Hypothetical;
        let mut result = vec![];
        set.activate_rewrite_target(1, &target_step, &mut result, &kctx);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_equality_resolution() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");

        // x0 != c0 or x0 = c1
        // When x0 unifies with itself, the first literal is eliminated and we get c1 = c0
        let clause = kctx.parse_clause("x0 != c0 or x0 = c1", &["Bool"]);
        let mock_step = ProofStep::mock_from_clause(clause);
        let proof_steps = ActiveSet::equality_resolution(0, &mock_step, &kctx);
        assert_eq!(proof_steps.len(), 1);
        assert!(proof_steps[0].clause.len() == 1);
        assert_eq!(format!("{}", proof_steps[0].clause), "c1 = c0".to_string());
    }

    #[test]
    fn test_mutually_recursive_equality_resolution() {
        // This is a bug we ran into. It shouldn't work
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("c0", "Bool");

        let clause = kctx.parse_clause(
            "g0(x0, g0(x1, g1(x2, c0))) != g0(g0(x2, x1), x0)",
            &["Bool", "Bool", "Bool"],
        );
        let mock_step = ProofStep::mock_from_clause(clause);
        assert!(ActiveSet::equality_resolution(0, &mock_step, &kctx).is_empty());
    }

    #[test]
    fn test_equality_factoring_basic() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        // x0 = c0 or x1 = c0
        // Equality factoring gives us c0 = x0
        let clause = kctx.parse_clause("x0 = c0 or x1 = c0", &["Bool", "Bool"]);
        let mock_step = ProofStep::mock_from_clause(clause);
        let proof_steps = ActiveSet::equality_factoring(0, &mock_step, &kctx);
        let expected = kctx.parse_clause("c0 = x0", &["Bool"]);
        for ps in &proof_steps {
            if ps.clause == expected {
                return;
            }
        }
        panic!("Did not find expected clause");
    }

    #[test]
    fn test_matching_entire_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g2", "(Bool, Bool) -> Bool")
            .parse_constants(&["c3", "c4", "c5", "c6", "c7"], "Bool");

        let mut set = ActiveSet::new();
        // Test that we can match an entire literal against a rewrite rule.
        // Use g2(g0(g0(x0, c4), c5), c6) or g0(x0, c7) != x0
        // When we have g0(c3, c7) = c3, this should resolve to just not g2(...).
        let clause1 = kctx.parse_clause(
            "not g2(g0(g0(x0, c4), c5), c6) or g0(x0, c7) != x0",
            &["Bool"],
        );
        let mut step = ProofStep::mock_from_clause(clause1);
        step.truthiness = Truthiness::Factual;
        set.activate(step, &kctx);

        let clause2 = kctx.parse_clause("g0(c3, c7) = c3", &[]);
        let mut step = ProofStep::mock_from_clause(clause2);
        step.truthiness = Truthiness::Counterfactual;
        let (_, new_clauses) = set.activate(step, &kctx);

        // Find the expected clause in results
        let expected = "not g0_2(g0_0(g0_0(c3, c4), c5), c6)";
        assert!(
            new_clauses
                .iter()
                .any(|ps| ps.clause.to_string() == expected),
            "Expected clause '{}' not found in {:?}",
            expected,
            new_clauses
                .iter()
                .map(|ps| ps.clause.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_equality_factoring_variable_numbering() {
        // This is a bug we ran into
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool");

        let mut set = ActiveSet::new();

        // Nonreflexive rule of less-than
        let clause1 = kctx.parse_clause("not g1(x0, x0)", &["Bool"]);
        set.activate(ProofStep::mock_from_clause(clause1), &kctx);

        // Trichotomy
        let clause2 = kctx.parse_clause("g1(x0, x1) or g1(x1, x0) or x0 = x1", &["Bool", "Bool"]);
        let mock_step = ProofStep::mock_from_clause(clause2);
        let output = ActiveSet::equality_factoring(0, &mock_step, &kctx);
        assert_eq!(output[0].clause.to_string(), "g0_1(x0, x0) or x0 = x0");
    }

    #[test]
    fn test_self_referential_resolution() {
        // This is a bug we ran into. These things should not unify
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("g2", "(Bool, Bool) -> Bool")
            .parse_constant("c0", "Bool");

        let mut set = ActiveSet::new();
        let clause1 = kctx.parse_clause("g2(x0, x0) = c0", &["Bool"]);
        set.activate(ProofStep::mock_from_clause(clause1), &kctx);

        let clause2 = kctx.parse_clause(
            "g2(g2(g1(c0, x0), x0), g2(x1, x1)) != c0",
            &["Bool", "Bool"],
        );
        let mut step = ProofStep::mock_from_clause(clause2);
        step.truthiness = Truthiness::Counterfactual;
        let mut results = vec![];
        set.find_resolutions(&step, &mut results, &kctx);
        assert_eq!(results.len(), 0);
    }

    /// Test that resolution with function variables and polymorphic constants produces
    /// well-typed clauses.
    ///
    /// This tests a bug where resolution between:
    /// - Long clause with function variables (x0, x1: Real -> Real) and value variable (x2: Real)
    ///   containing literal like x0(x2) = x1(x2)
    /// - Short clause with polymorphic constant (g2: T -> T applied to Real)
    ///
    /// The bug: When x1(x2) is unified with g2(Real), the unifier incorrectly allows
    /// x1 = g2 and x2 = Real (a TYPE symbol), even though x2 should be a VALUE of type Real.
    /// This results in the output clause having a type mismatch: the left side has type Real,
    /// but the right side has a complex unevaluated type expression.
    ///
    #[test]
    fn test_resolution_rejects_function_variable_with_polymorphic_type_argument() {
        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Real");

        // g2: (T: Type) -> T (polymorphic constant returning a value of type T)
        kctx.parse_polymorphic_constant("g2", "T: Type", "T");

        // g7: (T: Type) -> Type -> something -> T -> T
        // (a function that takes type params and returns a value)
        kctx.parse_polymorphic_constant("g7", "T: Type, U: Type", "Real -> T -> U");

        // g236: Real -> Real
        kctx.parse_constant("g236", "Real -> Real");

        // c1: Real
        kctx.parse_constant("c1", "Real");

        // g162: (Real -> Real) -> (Real -> Real) -> Real
        // (takes two functions and returns a value)
        kctx.parse_constant("g162", "(Real -> Real) -> (Real -> Real) -> Real");

        // s204: (Real -> Real) -> (Real -> Real) -> Real
        // (similar to g162)
        kctx.parse_constant("s204", "(Real -> Real) -> (Real -> Real) -> Real");

        // g223: (Real -> Real) -> Bool (predicate on functions)
        kctx.parse_constant("g223", "(Real -> Real) -> Bool");

        let mut set = ActiveSet::new();

        // Long clause: x0(g162(s204(x0, x1))) != x1(g162(s204(x0, x1))) or
        //              not g223(x0) or not g223(x1) or x0(x2) = x1(x2)
        // Context: x0: Real -> Real, x1: Real -> Real, x2: Real
        let long_clause = kctx.parse_clause(
            "x0(g162(s204(x0, x1))) != x1(g162(s204(x0, x1))) or not g223(x0) or not g223(x1) or x0(x2) = x1(x2)",
            &["Real -> Real", "Real -> Real", "Real"],
        );
        let mut long_step = ProofStep::mock_from_clause(long_clause);
        long_step.truthiness = Truthiness::Factual;
        set.activate(long_step, &kctx);

        // Short clause: g7(x0, Real, g236(c1), x1) != g2(Real)
        // Context: x0: Type, x1: x0 (value of type x0)
        let short_clause =
            kctx.parse_clause("g7(x0, Real, g236(c1), x1) != g2(Real)", &["Type", "x0"]);
        let mut short_step = ProofStep::mock_from_clause(short_clause);
        short_step.truthiness = Truthiness::Counterfactual;

        let mut results = vec![];
        set.find_resolutions(&short_step, &mut results, &kctx);

        // If resolution succeeds, validate that all result clauses are well-typed
        // BUG: Currently resolution produces ill-typed clauses where the right side
        // of a literal has a complex unevaluated type expression instead of Real
        for (i, ps) in results.iter().enumerate() {
            for (j, lit) in ps.clause.literals.iter().enumerate() {
                let left_type = lit
                    .left
                    .get_type_with_context(ps.clause.get_local_context(), &kctx);
                let right_type = lit
                    .right
                    .get_type_with_context(ps.clause.get_local_context(), &kctx);
                assert_eq!(
                    left_type,
                    right_type,
                    "Resolution with function variables produced ill-typed clause.\n\
                     Result clause {}: {}\n\
                     Literal {}: {}\n\
                     Left type: {:?}\n\
                     Right type: {:?}\n\
                     Context: {:?}",
                    i,
                    ps.clause,
                    j,
                    lit,
                    left_type,
                    right_type,
                    ps.clause.get_local_context().get_var_types()
                );
            }
        }
    }

    /// Test that polymorphic rewriting produces well-typed clauses.
    /// This tests a bug where backwards rewriting a concrete term with a polymorphic pattern
    /// produces a clause where the left and right sides have mismatched types.
    ///
    /// BUG: This test currently fails because the rewrite tree produces ill-typed literals
    /// when backwards rewriting with polymorphic patterns. The rewrite substitutes type
    /// variables (like x0, x1) into positions that expect ground types, resulting in
    /// type mismatches like `g1(g1(Type, x0, ...), T1, ...) = c1` where the left side
    /// has type involving FreeVariables but c1 has a ground type.
    #[test]
    fn test_polymorphic_backwards_rewrite_type_consistency() {
        let mut kctx = KernelContext::new();
        // Use names that don't start with 'T' to avoid collision with type variable syntax
        kctx.parse_datatype("Foo");
        kctx.parse_datatype("Bar");
        // Pair is a parameterized type: Pair[T, U]
        kctx.parse_type_constructor("Pair", 2);

        // g0 = Pair.new: (T: Type) -> (U: Type) -> T -> U -> Pair[T, U]
        kctx.parse_polymorphic_constant("g0", "T: Type, U: Type", "T -> U -> Pair[T, U]");
        // g1 = Pair.first: (T: Type) -> (U: Type) -> Pair[T, U] -> T
        kctx.parse_polymorphic_constant("g1", "T: Type, U: Type", "Pair[T, U] -> T");
        // g2 = Pair.second: (T: Type) -> (U: Type) -> Pair[T, U] -> U
        kctx.parse_polymorphic_constant("g2", "T: Type, U: Type", "Pair[T, U] -> U");
        kctx.parse_constant("c1", "Foo");
        kctx.parse_constant("c2", "Bar");

        let mut set = ActiveSet::new();

        // Add the polymorphic axiom for first: g1(x0, x1, g0(x0, x1, x2, x3)) = x2
        // This is: Pair.first(T, U, Pair.new(T, U, t, u)) = t
        // Context: x0: Type, x1: Type, x2: x0, x3: x1
        let first_axiom = kctx.parse_clause(
            "g1(x0, x1, g0(x0, x1, x2, x3)) = x2",
            &["Type", "Type", "x0", "x1"],
        );
        let mut first_step = ProofStep::mock_from_clause(first_axiom);
        first_step.truthiness = Truthiness::Factual;
        set.activate(first_step, &kctx);

        // Add the polymorphic axiom for second: g2(x0, x1, g0(x0, x1, x2, x3)) = x3
        // This is: Pair.second(T, U, Pair.new(T, U, t, u)) = u
        let second_axiom = kctx.parse_clause(
            "g2(x0, x1, g0(x0, x1, x2, x3)) = x3",
            &["Type", "Type", "x0", "x1"],
        );
        let mut second_step = ProofStep::mock_from_clause(second_axiom);
        second_step.truthiness = Truthiness::Factual;
        set.activate(second_step, &kctx);

        // Now activate a concrete target: Pair.first(Foo, Bar, Pair.new(Foo, Bar, c1, c2)) = c1
        // This triggers backwards rewriting which produces ill-typed clauses
        let target_clause = kctx.parse_clause("g1(Foo, Bar, g0(Foo, Bar, c1, c2)) = c1", &[]);
        let mut target_step = ProofStep::mock_from_clause(target_clause);
        target_step.truthiness = Truthiness::Counterfactual;

        // Use full activate which also does simplification
        let (_, result) = set.activate(target_step, &kctx);

        // Validate all generated clauses - this will catch type mismatches
        for ps in &result {
            ps.clause.validate(&kctx);
        }
    }

    /// Test that resolution is rejected when eliminating a variable whose type
    /// is not provably inhabited.
    ///
    /// Short clause: g1(x0, x1) where x0: Type, x1: x0 (i.e., x1 has type T where T is unconstrained)
    /// Long clause: not g1(x0, x1) or c0
    ///
    /// Resolution would produce: c0
    /// But this is unsound if the type variable T (x0) is not inhabited.
    #[test]
    fn test_resolution_rejects_eliminated_variable_with_uninhabited_type() {
        let mut kctx = KernelContext::new();

        // g1: (T: Type) -> T -> Bool (polymorphic predicate)
        kctx.parse_polymorphic_constant("g1", "T: Type", "T -> Bool");

        // c0: Bool (simple boolean constant)
        kctx.parse_constant("c0", "Bool");

        let mut set = ActiveSet::new();

        // Short clause: g1(x0, x1)
        // Context: x0: Type (the type variable T), x1: x0 (value of type T)
        let short_clause = kctx.parse_clause("g1(x0, x1)", &["Type", "x0"]);
        set.activate(ProofStep::mock_from_clause(short_clause), &kctx);

        // Long clause: not g1(x0, x1) or c0
        // Context: x0: Type, x1: x0
        let long_clause = kctx.parse_clause("not g1(x0, x1) or c0", &["Type", "x0"]);
        let long_step = ProofStep::mock_from_clause(long_clause);

        let mut results = vec![];
        set.find_resolutions(&long_step, &mut results, &kctx);

        // Resolution should be rejected because x1: x0 (a value of type T) is eliminated
        // and x0 (the type T) is an unconstrained type variable, which is not provably inhabited.
        assert!(
            results.is_empty(),
            "Resolution should be rejected when eliminating variable with uninhabited type, got {} results",
            results.len()
        );
    }

    /// Regression test: resolution must reject eliminating a long-clause variable
    /// whose concrete type is not provably inhabited.
    ///
    /// Short clause: not g0(x0), with x0: SetType (inhabited by c0).
    /// Long clause:  g0(g1(x0)), with x0: FiniteSetType (uninhabited).
    ///
    /// If accepted, resolution would derive contradiction from vacuous truth.
    #[test]
    fn test_resolution_rejects_eliminated_long_variable_with_concrete_uninhabited_type() {
        let mut kctx = KernelContext::new();

        // Uninterpreted concrete types.
        kctx.parse_type_constructor("SetType", 0);
        kctx.parse_type_constructor("FiniteSetType", 0);

        // Make SetType inhabited so short-side elimination remains sound.
        kctx.parse_constant("c0", "SetType");

        // Predicates/functions.
        kctx.parse_constant("g0", "SetType -> Bool");
        kctx.parse_constant("g1", "FiniteSetType -> SetType");

        let mut set = ActiveSet::new();

        // Short clause: not g0(x0), context x0: SetType.
        let short_clause = kctx.parse_clause("not g0(x0)", &["SetType"]);
        set.activate(ProofStep::mock_from_clause(short_clause), &kctx);

        // Long clause: g0(g1(x0)), context x0: FiniteSetType.
        // Mark as non-factual so resolution is actually attempted.
        let long_clause = kctx.parse_clause("g0(g1(x0))", &["FiniteSetType"]);
        let mut long_step = ProofStep::mock_from_clause(long_clause);
        long_step.truthiness = Truthiness::Counterfactual;

        let mut results = vec![];
        set.find_resolutions(&long_step, &mut results, &kctx);

        assert!(
            results.is_empty(),
            "Resolution should be rejected when eliminating concrete uninhabited long-clause variables, got {} results",
            results.len()
        );
    }

    /// Test that injectivity rejects clauses where eliminated variables have uninhabited types.
    ///
    /// Clause: g(x0, x1, x2) != g(x0, x1, x3) | c0
    /// Context: x0: Type, x1: x0, x2: Bool, x3: Bool
    /// Injectivity extracts: x2 != x3 | c0
    /// But x0 (Type) and x1 (x0) are eliminated, and x0 is not provably inhabited.
    #[test]
    fn test_injectivity_rejects_eliminated_variable_with_uninhabited_type() {
        let mut kctx = KernelContext::new();

        // g0: (T: Type) -> T -> Bool -> Bool -> Bool
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> Bool -> Bool -> Bool");
        kctx.parse_constant("c0", "Bool");

        // Clause: g0(x0, x1, x2) != g0(x0, x1, x3) or c0
        // Context: x0: Type, x1: x0, x2: Bool, x3: Bool
        // Injectivity extracts: x2 != x3 or c0
        // But x0 (Type) and x1 (x0) are eliminated, and x0 is not provably inhabited.
        let clause = kctx.parse_clause(
            "g0(x0, x1, x2) != g0(x0, x1, x3) or c0",
            &["Type", "x0", "Bool", "Bool"],
        );
        let mock_step = ProofStep::mock_from_clause(clause);
        let results = ActiveSet::injectivity(0, &mock_step, &kctx);

        // Injectivity should be rejected because x0 (Type) and x1 (x0) are eliminated
        // and x0 is not provably inhabited.
        assert!(
            results.is_empty(),
            "Injectivity should be rejected when eliminating variable with uninhabited type, got {} results: {:?}",
            results.len(),
            results.iter().map(|r| r.clause.to_string()).collect::<Vec<_>>()
        );
    }

    /// Test that equality factoring does NOT have the same inhabitedness bug as equality resolution.
    ///
    /// Unlike equality_resolution which completely removes a literal (and can eliminate variables
    /// that only appeared in that literal), equality_factoring preserves the unified term in the
    /// output. Variables in s transfer to u during unification, so they survive.
    ///
    /// This test demonstrates that equality_factoring is safe: it produces valid output clauses
    /// even when the input has variables with potentially uninhabited types.
    #[test]
    fn test_equality_factoring_preserves_uninhabited_type_variables() {
        let mut kctx = KernelContext::new();

        // g0: (T: Type) -> T -> T -> Bool
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T -> Bool");
        kctx.parse_constant("c1", "Bool");
        kctx.parse_constant("c2", "Bool");

        // Clause: g0(x0, x1, x2) = c1 | g0(x0, x2, x1) = c2
        // Context: x0: Type, x1: x0, x2: x0
        // Equality factoring will unify g0(x0, x1, x2) with g0(x0, x2, x1), giving x1 = x2
        // Output: c1 != c2 | g0(x0, x2, x2) = c2
        // Key: x0 (Type) and x2 (x0) both survive - no unsoundness
        let clause = kctx.parse_clause(
            "g0(x0, x1, x2) = c1 or g0(x0, x2, x1) = c2",
            &["Type", "x0", "x0"],
        );
        let mock_step = ProofStep::mock_from_clause(clause);
        let results = ActiveSet::equality_factoring(0, &mock_step, &kctx);

        // Equality factoring should produce results - the inference is valid
        // because x0 (Type variable) survives in the output via g0(x0, x2, x2)
        // The output is still universally quantified over x0: Type
        assert!(
            !results.is_empty(),
            "Equality factoring should produce results (no variables with uninhabited types are eliminated)"
        );

        // Verify that the output clauses still have variables of type x0
        for result in &results {
            let ctx = result.clause.get_local_context();
            // The output should have at least one variable - the surviving x2 of type x0
            assert!(ctx.len() > 0, "Output clause should have variables");
        }
    }

    /// Test that extensionality does NOT have the same inhabitedness bug as equality resolution.
    ///
    /// Extensionality peels trailing variable arguments from f(x, y) = g(x, y) to get f(x) = g(x).
    /// The peeled variable y is eliminated, but the type variable x survives.
    ///
    /// Unlike equality_resolution which can derive something false from something vacuously true,
    /// extensionality is sound even when types are uninhabited because:
    /// - Original: "for all y: x, f(x, y) = g(x, y)" is vacuously true when x is empty
    /// - Result: "f(x) = g(x)" means f(x) and g(x) are extensionally equal functions
    /// - When x is empty, two functions x -> T are extensionally equal (no arguments to differ on)
    #[test]
    fn test_extensionality_sound_with_uninhabited_types() {
        let mut kctx = KernelContext::new();

        // c1, c2: (T: Type) -> T -> Bool
        kctx.parse_polymorphic_constant("c1", "T: Type", "T -> Bool");
        kctx.parse_polymorphic_constant("c2", "T: Type", "T -> Bool");

        // Clause: c1(x0, x1) = c2(x0, x1) where x0: Type, x1: x0
        // Extensionality should peel x1 to get c1(x0) = c2(x0)
        // This is sound because even if x0 is uninhabited, the functions are extensionally equal
        let clause = kctx.parse_clause("c1(x0, x1) = c2(x0, x1)", &["Type", "x0"]);

        if let Some(result_literals) = clause.find_extensionality(&kctx) {
            // Extensionality should work - it's a sound inference
            assert_eq!(result_literals.len(), 1);
            // The result should have fewer variables than the original
            let result_clause = Clause::new(result_literals, clause.get_local_context());
            assert!(
                result_clause.get_local_context().len() < clause.get_local_context().len(),
                "Extensionality should eliminate some variables"
            );
        }
        // Note: find_extensionality might return None due to other constraints,
        // which is fine - we're just checking that IF it works, it's sound.
    }

    /// Test that equality resolution is rejected when eliminating a variable whose type
    /// is not provably inhabited.
    ///
    /// Clause: g0(x0, x1, x2) != g0(x0, x2, x1) or c1
    /// Context: x0: Type, x1: x0, x2: x0
    /// Unification maps x1 ↔ x2, eliminating the negative literal.
    /// Result would be: c1 (all variables eliminated)
    /// But this is unsound if x0 (Type) is not inhabited.
    #[test]
    fn test_equality_resolution_rejects_eliminated_variable_with_uninhabited_type() {
        let mut kctx = KernelContext::new();

        // g0: (T: Type) -> T -> T -> Bool
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T -> Bool");
        kctx.parse_constant("c1", "Bool");

        // Clause: g0(x0, x1, x2) != g0(x0, x2, x1) or c1
        // Context: x0: Type, x1: x0, x2: x0
        let clause = kctx.parse_clause(
            "g0(x0, x1, x2) != g0(x0, x2, x1) or c1",
            &["Type", "x0", "x0"],
        );
        let mock_step = ProofStep::mock_from_clause(clause);
        let results = ActiveSet::equality_resolution(0, &mock_step, &kctx);

        // Should reject because x1, x2 have type x0 (uninhabited), and they're eliminated
        assert!(
            results.is_empty(),
            "Equality resolution should be rejected when eliminating variable with uninhabited type, got {} results",
            results.len()
        );
    }
}
