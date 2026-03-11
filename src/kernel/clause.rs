use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term, TermRef};
use crate::kernel::term_normalization::{normalize_clause_term, normalize_signed_clause_term};

/// A Clause represents a disjunction (an "or") of literals.
/// Type information is stored separately in the TypeStore and SymbolTable,
/// along with a Context that tracks the types of variables in the clause.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub context: LocalContext,
}

pub struct BooleanReductionResult {
    pub clause: Clause,
    pub var_ids: Vec<AtomId>,
    pub pre_norm_context: LocalContext,
}

impl Clause {
    fn normalize_with_var_ids_prefilled(
        literals: Vec<Literal>,
        context: &LocalContext,
        mut var_ids: Vec<AtomId>,
    ) -> (Clause, Vec<AtomId>) {
        // Pair each literal with its initial index, filtering out impossible literals.
        let mut indexed_literals: Vec<(Literal, usize)> = literals
            .into_iter()
            .flat_map(Self::normalize_literals_for_clause)
            .enumerate()
            .filter_map(|(i, lit)| {
                if lit.is_impossible() {
                    None
                } else {
                    Some((lit, i))
                }
            })
            .collect();
        indexed_literals.sort();

        let mut output_literals = vec![];
        for (literal, _input_index) in indexed_literals {
            if !output_literals.is_empty() {
                let last_index = output_literals.len() - 1;
                if literal == output_literals[last_index] {
                    // Duplicate literal, skip it.
                    continue;
                }
            }
            output_literals.push(literal);
        }

        for literal in &mut output_literals {
            literal.normalize_var_ids_with_context(&mut var_ids, context);
        }
        output_literals.sort();
        output_literals.dedup();

        let clause = Clause {
            literals: output_literals,
            context: context.remap(&var_ids),
        };
        (clause, var_ids)
    }

    /// Get the local context for this clause.
    /// This returns the context that stores variable types for this clause.
    pub fn get_local_context(&self) -> &LocalContext {
        &self.context
    }

    /// Creates a new normalized clause.
    pub fn new(literals: Vec<Literal>, context: &LocalContext) -> Clause {
        let mut c = Clause {
            literals,
            context: context.clone(),
        };
        c.normalize();
        c
    }

    /// Creates a new normalized clause, keeping the first `pinned` variables at their
    /// original positions (x0, x1, ..., x_{pinned-1}).
    ///
    /// This is useful for synthetic keys where type variables need to stay consistent
    /// across all clauses in a definition.
    pub(crate) fn new_with_pinned_vars(
        literals: Vec<Literal>,
        context: &LocalContext,
        pinned: usize,
    ) -> Clause {
        let mut c = Clause {
            literals,
            context: context.clone(),
        };
        c.normalize_with_pinned(pinned);
        c
    }

    /// Return a normalized clone of this clause.
    pub fn normalized(&self) -> Clause {
        let mut normalized = self.clone();
        normalized.normalize();
        normalized
    }

    /// Return a normalized clone while keeping all existing local-variable slots fixed.
    pub fn normalized_preserving_locals(&self) -> Clause {
        let pinned = self.get_local_context().len();
        let mut normalized = self.clone();
        normalized.normalize_with_pinned(pinned);
        normalized
    }

    /// Check whether this clause is already in normalized form.
    pub fn is_normalized(&self) -> bool {
        *self == self.normalized()
    }

    /// Check whether this clause is normalized while keeping all existing local-variable slots
    /// fixed in place.
    pub fn is_normalized_preserving_locals(&self) -> bool {
        *self == self.normalized_preserving_locals()
    }

    /// Normalizes literals into a clause, tracking the variable renumbering.
    ///
    /// Returns (clause, var_ids) where var_ids maps new sequential variable IDs
    /// to original variable IDs: var_ids[new_id] = old_id.
    pub(crate) fn normalize_with_var_ids(
        literals: Vec<Literal>,
        context: &LocalContext,
    ) -> (Clause, Vec<AtomId>) {
        Self::normalize_with_var_ids_prefilled(literals, context, vec![])
    }

    /// Sorts literals.
    /// Removes any duplicate or impossible literals.
    /// An empty clause indicates an impossible clause.
    fn normalize(&mut self) {
        self.normalize_with_pinned(0);
    }

    /// Normalizes the clause, keeping the first `pinned` variables at their
    /// original positions (x0, x1, ..., x_{pinned-1}).
    fn normalize_with_pinned(&mut self, pinned: usize) {
        self.literals = self
            .literals
            .drain(..)
            .flat_map(Self::normalize_literals_for_clause)
            .collect();
        self.literals.retain(|lit| !lit.is_impossible());
        self.literals.sort();
        self.literals.dedup();
        self.normalize_var_ids_with_pinned(pinned);
        self.literals.sort();
        self.literals.dedup();
    }

    /// Normalizes the variable IDs in the literals.
    /// This may flip literals, so keep in mind it will break any trace.
    /// Also rebuilds the context to match the renumbered variables.
    fn normalize_var_ids(&mut self) {
        self.normalize_var_ids_with_pinned(0);
    }

    /// Normalizes the variable IDs in the literals, keeping the first `pinned` variables
    /// at their original positions (x0, x1, ..., x_{pinned-1}).
    ///
    /// This is useful for synthetic keys where type variables need to stay consistent
    /// across all clauses in a definition.
    fn normalize_var_ids_with_pinned(&mut self, pinned: usize) {
        // Pre-populate with pinned variable IDs (0, 1, ..., pinned-1)
        let mut var_ids: Vec<AtomId> = (0..pinned as AtomId).collect();
        let input_context = self.context.clone();
        for literal in &mut self.literals {
            literal.normalize_var_ids_with_context(&mut var_ids, &input_context);
        }
        self.context = input_context.remap(&var_ids);
    }

    pub(crate) fn exact_match_key(&self) -> Clause {
        let mut clause = Clause {
            literals: self
                .literals
                .clone()
                .into_iter()
                .flat_map(Self::normalize_literals_for_matching)
                .collect(),
            context: self.context.clone(),
        };
        clause.literals.retain(|lit| !lit.is_impossible());
        clause.literals.sort();
        clause.literals.dedup();
        clause.normalize_var_ids();
        clause
    }

    fn normalize_literals_for_clause(literal: Literal) -> Vec<Literal> {
        let right = normalize_clause_term(&literal.right);
        if right.is_true() {
            let (left, positive) = normalize_signed_clause_term(&literal.left, literal.positive);
            return vec![Literal::from_signed_term(left, positive)];
        }

        vec![Literal::new(
            literal.positive,
            normalize_clause_term(&literal.left),
            right,
        )]
    }

    fn normalize_literals_for_matching(literal: Literal) -> Vec<Literal> {
        let right = normalize_clause_term(&literal.right);
        if right.is_true() {
            return Self::normalize_signed_boolean_term_to_literals(
                &literal.left,
                literal.positive,
            );
        }

        vec![Literal::new(
            literal.positive,
            normalize_clause_term(&literal.left),
            right,
        )]
    }

    fn normalize_signed_boolean_term_to_literals(term: &Term, positive: bool) -> Vec<Literal> {
        if let Some(args) = Self::split_symbol_application(term, Symbol::Not, 1) {
            return Self::normalize_signed_boolean_term_to_literals(&args[0], !positive);
        }

        if positive {
            if let Some(args) = Self::split_symbol_application(term, Symbol::Or, 2) {
                let mut literals =
                    Self::normalize_signed_boolean_term_to_literals(&args[0], positive);
                literals.extend(Self::normalize_signed_boolean_term_to_literals(
                    &args[1], positive,
                ));
                return literals;
            }
        } else if let Some(args) = Self::split_symbol_application(term, Symbol::And, 2) {
            let mut literals = Self::normalize_signed_boolean_term_to_literals(&args[0], positive);
            literals.extend(Self::normalize_signed_boolean_term_to_literals(
                &args[1], positive,
            ));
            return literals;
        }

        let (term, positive) = normalize_signed_clause_term(term, positive);
        vec![Literal::from_signed_term(term, positive)]
    }

    /// Create an impossible clause (empty clause, represents false).
    pub fn impossible() -> Clause {
        Clause {
            literals: vec![],
            context: LocalContext::empty(),
        }
    }

    /// Get the number of literals in this clause.
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if this is an empty (impossible) clause.
    pub fn is_impossible(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if this clause is a tautology (contains a tautological literal or contradictory pair).
    pub fn is_tautology(&self) -> bool {
        // Find the index of the first positive literal
        if let Some(first_pos) = self.literals.iter().position(|x| x.positive) {
            // Check for (!p, p) pairs which cause a tautology
            for neg_literal in &self.literals[0..first_pos] {
                for pos_literal in &self.literals[first_pos..] {
                    if neg_literal.left == pos_literal.left
                        && neg_literal.right == pos_literal.right
                    {
                        return true;
                    }
                }
            }
        }

        self.literals.iter().any(|x| x.is_tautology())
    }

    /// Check if this clause contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    /// Check if this clause contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_scoped_constant())
    }

    /// Count the total number of atoms across all literals.
    pub fn atom_count(&self) -> u32 {
        self.literals.iter().map(|x| x.atom_count()).sum()
    }

    /// Get the least unused variable index.
    pub fn least_unused_variable(&self) -> AtomId {
        self.literals
            .iter()
            .map(|x| x.least_unused_variable())
            .max()
            .unwrap_or(0)
    }

    /// Iterate over all atoms in all literals.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.literals
            .iter()
            .flat_map(|literal| literal.iter_atoms())
    }

    /// Check if this clause contains all literals from another clause.
    pub fn contains(&self, other: &Clause) -> bool {
        for literal in &other.literals {
            if !self.literals.iter().any(|x| x == literal) {
                return false;
            }
        }
        true
    }

    /// Check if any top level term has the given atom as its head.
    pub fn has_head(&self, atom: &Atom) -> bool {
        for literal in &self.literals {
            if literal.left.get_head_atom() == atom || literal.right.get_head_atom() == atom {
                return true;
            }
        }
        false
    }

    /// Compact free-variable IDs without otherwise changing literal shape.
    ///
    /// This does not do full clause normalization: literals are not flipped, simplified,
    /// deduplicated, or re-sorted. It only rewrites the local-variable numbering and rebuilds the
    /// context to match.
    fn compact_var_ids_preserving_literal_shape(&mut self) {
        let mut var_ids = vec![];
        let input_context = self.context.clone();
        for literal in &mut self.literals {
            literal
                .left
                .normalize_var_ids_with_context(&mut var_ids, &input_context);
            literal
                .right
                .normalize_var_ids_with_context(&mut var_ids, &input_context);
        }
        self.context = input_context.remap(&var_ids);
    }

    /// Return a copy with compact free-variable IDs but the same literal shape.
    pub fn compacted_var_ids_preserving_literal_shape(&self) -> Clause {
        let mut clause = self.clone();
        clause.compact_var_ids_preserving_literal_shape();
        clause
    }

    /// Normalize variable IDs for PDT-based matching.
    ///
    /// Variables are numbered by first structural occurrence in the clause terms.
    /// Variables that only appear in type annotations (not in the terms themselves)
    /// get IDs after all structural variables.
    ///
    /// This is used for generalization matching where the PDT matching algorithm
    /// expects the first structurally-occurring variable to be Variable(0).
    pub fn normalize_var_ids_types_last(&mut self) {
        let mut structural_var_ids: Vec<u16> = vec![];
        let input_context = self.context.clone();

        // First pass: collect variable IDs from terms in structural order
        for literal in &self.literals {
            literal
                .left
                .collect_structural_var_ids(&mut structural_var_ids);
            literal
                .right
                .collect_structural_var_ids(&mut structural_var_ids);
        }

        // Second pass: collect variables from context that only appear in types
        // (not in the structural terms)
        let mut type_only_var_ids: Vec<u16> = vec![];
        for var_id in 0..input_context.len() as u16 {
            if !structural_var_ids.contains(&var_id) {
                type_only_var_ids.push(var_id);
            }
        }

        // Third pass: apply the renumbering
        for literal in &mut self.literals {
            literal
                .left
                .apply_var_renumbering(&structural_var_ids, &type_only_var_ids);
            literal
                .right
                .apply_var_renumbering(&structural_var_ids, &type_only_var_ids);
        }

        // Rebuild context: structural vars first (for PDT), then type-only vars
        let mut all_var_ids = structural_var_ids.clone();
        all_var_ids.extend(type_only_var_ids);
        self.context = input_context.remap(&all_var_ids);
    }

    /// Create a clause from literals without normalizing.
    pub fn from_literals_unnormalized(literals: Vec<Literal>, context: &LocalContext) -> Clause {
        Clause {
            literals,
            context: context.clone(),
        }
    }

    /// Validate that all literals have consistent types.
    ///
    /// This validation only runs in test builds or when the "validate" feature is enabled.
    /// It's skipped in production for performance reasons.
    pub fn validate(&self, kernel_context: &KernelContext) {
        #[cfg(not(any(test, feature = "validate")))]
        {
            let _ = kernel_context;
            return;
        }

        #[cfg(any(test, feature = "validate"))]
        {
            // Check for self-referential or forward-referencing types
            // A variable's type can only reference lower-numbered variables
            if !self.context.validate_variable_ordering() {
                let mut msg = format!(
                    "Clause validation failed: variable types have bad ordering. Clause: {}\nContext:\n",
                    self
                );
                for (i, var_type) in self.context.get_var_types().iter().enumerate() {
                    msg.push_str(&format!("  x{}: {:?}\n", i, var_type));
                }
                panic!("{}", msg);
            }

            for literal in &self.literals {
                literal.validate_type(&self.context, kernel_context);

                // Bound variables are allowed under binders (lambda/pi/quantifiers),
                // but not if they escape into top-level term positions.
                if literal.left.has_escaping_bound_variable() {
                    panic!(
                        "Clause validation failed: left side of literal contains escaping bound variable. Literal: {}",
                        literal
                    );
                }
                if literal.right.has_escaping_bound_variable() {
                    panic!(
                        "Clause validation failed: right side of literal contains escaping bound variable. Literal: {}",
                        literal
                    );
                }
            }
        }
    }

    /// Returns a canonical form of this clause with literals in deterministic order,
    /// keeping the first `pinned` variables at their original positions.
    ///
    /// This uses a two-phase approach to ensure alpha-equivalent clauses produce
    /// identical canonical forms:
    /// 1. Sort using stable comparison (treating all free variables as equivalent)
    /// 2. Renumber variables based on order of first appearance
    /// 3. Re-sort using total ordering (now with canonical variable names)
    fn canonicalize_with_pinned(&self, pinned: usize) -> Clause {
        // Phase 1: Sort using stable comparison that treats all free variables as equivalent.
        // This ensures alpha-equivalent clauses get the same initial ordering.
        let mut literals = self.literals.clone();
        literals.sort_by(|a, b| a.stable_cmp(b));

        // Phase 2: Renumber variables based on order of first appearance.
        // Pre-populate with pinned variable IDs (0, 1, ..., pinned-1)
        let mut var_ids: Vec<AtomId> = (0..pinned as AtomId).collect();
        for lit in &mut literals {
            lit.normalize_var_ids_with_context(&mut var_ids, &self.context);
        }
        let new_context = self.context.remap(&var_ids);

        // Phase 3: Re-sort using total ordering. Now that variables are canonical,
        // this produces a deterministic final order.
        literals.sort();

        Clause {
            literals,
            context: new_context,
        }
    }

    /// Returns a canonicalized clone suitable for deterministic keying.
    ///
    /// The first `pinned` variables are kept fixed (x0..x{pinned-1}).
    pub fn key_canonicalized_with_pinned(&self, pinned: usize) -> Clause {
        self.canonicalize_with_pinned(pinned)
    }

    /// Extracts the polarity from all literals.
    /// Returns a clause with all positive literals and a vector of the original polarities.
    pub fn extract_polarity(&self) -> (Clause, Vec<bool>) {
        let mut polarities = Vec::new();
        let mut new_literals = Vec::new();
        for literal in &self.literals {
            let (pos_lit, polarity) = literal.extract_polarity();
            new_literals.push(pos_lit);
            polarities.push(polarity);
        }
        (
            Clause::from_literals_unnormalized(new_literals, &self.context),
            polarities,
        )
    }

    /// Finds all possible injectivity applications for this clause.
    /// Returns the resulting literals for each application.
    pub fn find_injectivities(&self) -> Vec<Vec<Literal>> {
        let mut results = vec![];

        for (i, target) in self.literals.iter().enumerate() {
            // Check if we can apply injectivity to the ith literal.
            if target.positive {
                // Negative literals come before positive ones so we're done
                break;
            }
            if target.left.get_head_atom() != target.right.get_head_atom() {
                continue;
            }
            if target.left.num_args() != target.right.num_args() {
                continue;
            }

            // We can do function elimination when precisely one of the arguments is different.
            let left_args = target.left.args();
            let right_args = target.right.args();
            let mut different_index = None;
            for (j, arg) in left_args.iter().enumerate() {
                if arg != &right_args[j] {
                    if different_index.is_some() {
                        different_index = None;
                        break;
                    }
                    different_index = Some(j);
                }
            }

            if let Some(j) = different_index {
                // Looks like we can eliminate the functions from this literal
                let mut literals = self.literals.clone();
                let (new_literal, _flipped) =
                    Literal::new_with_flip(false, left_args[j].clone(), right_args[j].clone());
                literals[i] = new_literal;
                results.push(literals);
            }
        }

        results
    }

    /// Generates all clauses that can be derived from this clause using injectivity.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn injectivities(&self) -> Vec<Clause> {
        self.find_injectivities()
            .into_iter()
            .map(|literals| Clause::new(literals, &self.context))
            .filter(|clause| !clause.is_tautology())
            .collect()
    }

    /// Finds if extensionality can be applied to this clause.
    /// Returns the resulting literals if extensionality applies.
    ///
    /// For mixed clauses, extensionality is only sound when the peeled variables
    /// do not appear in any of the other literals.
    ///
    /// Lambda-native: We peel arguments from the right only as long as they are
    /// distinct free variables. This allows extensionality to work when leading
    /// arguments are ground constants (like type arguments).
    ///
    /// Example: f(T, x, y) = g(T, x, y) where T is ground, x and y are free vars
    /// → Peels y then x, stops at T → Result: f(T) = g(T)
    pub fn find_extensionality(&self, kernel_context: &KernelContext) -> Option<Vec<Literal>> {
        for (index, literal) in self.literals.iter().enumerate() {
            let Some((new_lit, peeled_vars)) =
                self.find_extensionality_for_literal(literal, kernel_context)
            else {
                continue;
            };

            let peeled_used_elsewhere =
                self.literals
                    .iter()
                    .enumerate()
                    .any(|(other_index, other)| {
                        other_index != index
                            && peeled_vars.iter().any(|var_id| {
                                other.left.has_variable(*var_id)
                                    || other.right.has_variable(*var_id)
                            })
                    });
            if peeled_used_elsewhere {
                continue;
            }

            let mut literals = self.literals.clone();
            literals[index] = new_lit;
            return Some(literals);
        }
        None
    }

    fn find_extensionality_for_literal(
        &self,
        literal: &Literal,
        kernel_context: &KernelContext,
    ) -> Option<(Literal, HashSet<AtomId>)> {
        // Extensionality only applies to positive equality literals
        if !literal.positive {
            return None;
        }

        // Check if this is f(..., x1, x2, ..., xn) = g(..., x1, x2, ..., xn)
        // where the trailing args match and can be peeled via extensionality.
        let (longer, shorter) = if literal.left.num_args() >= literal.right.num_args() {
            (&literal.left, &literal.right)
        } else {
            (&literal.right, &literal.left)
        };

        let longer_args = longer.args();
        let shorter_args = shorter.args();

        // Both sides must be function applications. Terms like lambdas/foralls are not
        // application spines even though `num_args()` can count their nested structure.
        if longer_args.is_empty() || shorter_args.is_empty() {
            return None;
        }

        // Heads must not be variables
        if longer.get_head_atom().is_variable() || shorter.get_head_atom().is_variable() {
            return None;
        }

        // Find the longest matching suffix between longer_args and shorter_args.
        // We compare from the right: longer_args[len-1] vs shorter_args[len-1], etc.
        let mut matching_suffix_len = 0;
        let longer_len = longer_args.len();
        let shorter_len = shorter_args.len();
        while matching_suffix_len < shorter_len {
            let longer_idx = longer_len - 1 - matching_suffix_len;
            let shorter_idx = shorter_len - 1 - matching_suffix_len;
            if longer_args[longer_idx] != shorter_args[shorter_idx] {
                break;
            }
            matching_suffix_len += 1;
        }

        if matching_suffix_len == 0 {
            return None; // No matching suffix at all
        }

        // Find the longest right-suffix of matching args that are distinct free variables.
        // We peel from the right, stopping when we hit a non-variable or a duplicate.
        let mut peel_count = 0;
        let mut peeled_vars: HashSet<AtomId> = HashSet::new();

        for i in 0..matching_suffix_len {
            // Index from the right
            let shorter_idx = shorter_len - 1 - i;
            let arg = &shorter_args[shorter_idx];
            match arg.atomic_variable() {
                Some(var_id) => {
                    // Check this var is distinct from vars we're already peeling
                    if peeled_vars.contains(&var_id) {
                        break; // Duplicate var, stop peeling
                    }

                    // Check var is not in the prefix (non-peeled args) on either side
                    let longer_prefix_end = longer_len - peel_count;
                    let shorter_prefix_end = shorter_len - peel_count;
                    let mut var_in_prefix = false;

                    // Check longer's prefix (all args except peeled suffix)
                    for j in 0..longer_prefix_end {
                        if j < longer_len - matching_suffix_len || j < longer_len - 1 - i {
                            if longer_args[j].has_variable(var_id) {
                                var_in_prefix = true;
                                break;
                            }
                        }
                    }

                    // Also check shorter's prefix
                    if !var_in_prefix {
                        for j in 0..shorter_prefix_end {
                            if j < shorter_idx {
                                if shorter_args[j].has_variable(var_id) {
                                    var_in_prefix = true;
                                    break;
                                }
                            }
                        }
                    }

                    if var_in_prefix {
                        break; // Var appears in prefix, stop peeling
                    }

                    peeled_vars.insert(var_id);
                    peel_count += 1;
                }
                None => break, // Not a variable, stop peeling
            }
        }

        if peel_count == 0 {
            return None; // Can't peel anything
        }

        // Build the new terms by removing only peel_count args from the right
        let new_longer_arg_count = longer_len - peel_count;
        let new_shorter_arg_count = shorter_len - peel_count;

        let new_longer = if new_longer_arg_count == 0 {
            longer.get_head_term()
        } else {
            let args: Vec<_> = longer_args[..new_longer_arg_count]
                .iter()
                .map(|a| a.to_owned())
                .collect();
            Term::new(*longer.get_head_atom(), args)
        };

        let new_shorter = if new_shorter_arg_count == 0 {
            shorter.get_head_term()
        } else {
            let args: Vec<_> = shorter_args[..new_shorter_arg_count]
                .iter()
                .map(|a| a.to_owned())
                .collect();
            Term::new(*shorter.get_head_atom(), args)
        };

        // If the resulting terms are identical, this would be a tautology (f = f)
        if new_longer == new_shorter {
            return None;
        }

        // Check the types are compatible
        let longer_type = new_longer.get_type_with_context(&self.context, kernel_context);
        let shorter_type = new_shorter.get_type_with_context(&self.context, kernel_context);
        if longer_type != shorter_type {
            return None;
        }

        let (new_lit, _) = Literal::new_with_flip(true, new_longer, new_shorter);
        Some((new_lit, peeled_vars))
    }

    /// Generates all clauses that can be derived from this clause using boolean reduction.
    /// Boolean reduction is replacing a boolean equality with a disjunction that it implies.
    /// Returns the resulting literals for each application.
    fn split_symbol_application(term: &Term, symbol: Symbol, arity: usize) -> Option<Vec<Term>> {
        let (head, args) = term.as_ref().split_application_multi()?;
        if args.len() != arity {
            return None;
        }
        match head.as_ref().decompose() {
            Decomposition::Atom(Atom::Symbol(s)) if *s == symbol => Some(args),
            _ => None,
        }
    }

    /// If `term` has shape `exists(T => b0 = t)` or `exists(T => t = b0)` with
    /// a closed witness term `t`, reduce it to the instantiated body.
    ///
    /// This captures the obvious existential-introduction case in `iet` mode
    /// without introducing synthetic skolems.
    fn reduce_exists_with_obvious_witness(term: &Term) -> Option<(Term, Term)> {
        let (_binder_type, body) = term.as_ref().split_exists()?;
        let body = body.to_owned();
        let args = Self::split_symbol_application(&body, Symbol::Eq, 3)?;
        let b0 = Term::atom(Atom::BoundVariable(0));
        let witness = if args[1] == b0 {
            args[2].clone()
        } else if args[2] == b0 {
            args[1].clone()
        } else {
            return None;
        };
        if witness.has_bound_variable() {
            return None;
        }
        let instantiated = body.substitute_bound(0, &witness).shift_bound(0, -1);
        Some((witness, instantiated))
    }

    /// Reduce `exists(T => body)` to `body[choose(T, function(x:T){body})/x]`.
    ///
    /// This is the generic existential-activation path for `iet` mode.
    fn reduce_exists_with_choose(term: &Term) -> Option<Term> {
        let (binder_type, body) = term.as_ref().split_exists()?;
        let binder_type = binder_type.to_owned();
        let body = body.to_owned();
        let predicate = Term::lambda(binder_type.clone(), body.clone());
        let choose_term = Term::atom(Atom::Symbol(Symbol::Choose)).apply(&[binder_type, predicate]);
        Some(body.substitute_bound(0, &choose_term).shift_bound(0, -1))
    }

    /// Reduce a top-level function inequality `f != g` to
    /// `exists(x: A) { f(x) != g(x) }`.
    ///
    /// Repeated applications of boolean reduction can then expose concrete
    /// witness applications via the existing `exists` machinery.
    fn reduce_function_inequality_to_exists(
        literal: &Literal,
        context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<Term> {
        if literal.positive {
            return None;
        }

        let left_type = literal.left.get_type_with_context(context, kernel_context);
        let right_type = literal.right.get_type_with_context(context, kernel_context);
        if left_type != right_type {
            return None;
        }

        let (binder_type, output_type) = left_type.as_ref().split_pi()?;
        let bound = Term::atom(Atom::BoundVariable(0));
        let body = Term::not(Term::eq(
            output_type.to_owned(),
            literal.left.clone().apply(&[bound.clone()]),
            literal.right.clone().apply(&[bound]),
        ));
        Some(Term::exists(binder_type.to_owned(), body))
    }

    /// Reduce `not forall(T => body)` to `exists(T => not body)`.
    fn reduce_negated_forall(term: &Term) -> Option<Term> {
        let (binder_type, body) = term.as_ref().split_forall()?;
        Some(Term::exists(
            binder_type.to_owned(),
            Term::not(body.to_owned()),
        ))
    }

    fn simplify_ite_term(term: &Term) -> Term {
        fn substitute_bound_capture_avoiding(
            term: TermRef<'_>,
            index: u16,
            replacement: &Term,
            depth: u16,
        ) -> Term {
            match term.decompose() {
                Decomposition::Atom(Atom::BoundVariable(i)) if *i == index + depth => {
                    replacement.shift_bound(0, depth as i16)
                }
                Decomposition::Atom(_) => term.to_owned(),
                Decomposition::Application(function, argument) => {
                    let function =
                        substitute_bound_capture_avoiding(function, index, replacement, depth);
                    let argument =
                        substitute_bound_capture_avoiding(argument, index, replacement, depth);
                    function.apply(&[argument])
                }
                Decomposition::Pi(input, output) => {
                    let input = substitute_bound_capture_avoiding(input, index, replacement, depth);
                    let output =
                        substitute_bound_capture_avoiding(output, index, replacement, depth + 1);
                    Term::pi(input, output)
                }
                Decomposition::Lambda(input, body) => {
                    let input = substitute_bound_capture_avoiding(input, index, replacement, depth);
                    let body =
                        substitute_bound_capture_avoiding(body, index, replacement, depth + 1);
                    Term::lambda(input, body)
                }
                Decomposition::ForAll(binder_type, body) => {
                    let binder_type =
                        substitute_bound_capture_avoiding(binder_type, index, replacement, depth);
                    let body =
                        substitute_bound_capture_avoiding(body, index, replacement, depth + 1);
                    Term::forall(binder_type, body)
                }
                Decomposition::Exists(binder_type, body) => {
                    let binder_type =
                        substitute_bound_capture_avoiding(binder_type, index, replacement, depth);
                    let body =
                        substitute_bound_capture_avoiding(body, index, replacement, depth + 1);
                    Term::exists(binder_type, body)
                }
            }
        }

        fn beta_reduce_head_lambda(body: TermRef<'_>, argument: &Term) -> Term {
            // Standard de Bruijn beta reduction:
            // shift(-1, subst(0, shift(1, arg), body))
            let lifted_argument = argument.shift_bound(0, 1);
            let substituted = substitute_bound_capture_avoiding(body, 0, &lifted_argument, 0);
            substituted.shift_bound(0, -1)
        }

        fn recurse(term: &Term) -> Term {
            let rebuilt = match term.as_ref().decompose() {
                Decomposition::Atom(_) => term.clone(),
                Decomposition::Application(function, argument) => {
                    let function = recurse(&function.to_owned());
                    let argument = recurse(&argument.to_owned());
                    function.apply(&[argument])
                }
                Decomposition::Pi(input, output) => {
                    let input = recurse(&input.to_owned());
                    let output = recurse(&output.to_owned());
                    Term::pi(input, output)
                }
                Decomposition::Lambda(input, body) => {
                    let input = recurse(&input.to_owned());
                    let body = recurse(&body.to_owned());
                    Term::lambda(input, body)
                }
                Decomposition::ForAll(binder_type, body) => {
                    let binder_type = recurse(&binder_type.to_owned());
                    let body = recurse(&body.to_owned());
                    Term::forall(binder_type, body)
                }
                Decomposition::Exists(binder_type, body) => {
                    let binder_type = recurse(&binder_type.to_owned());
                    let body = recurse(&body.to_owned());
                    Term::exists(binder_type, body)
                }
            };

            // Beta-reduce a head lambda application: (function(x) { body })(arg) -> body[arg/x]
            if let Decomposition::Application(function, argument) = rebuilt.as_ref().decompose() {
                if let Decomposition::Lambda(_, body) = function.decompose() {
                    let reduced = beta_reduce_head_lambda(body, &argument.to_owned());
                    return recurse(&reduced);
                }
            }

            if let Some(args) = Clause::split_symbol_application(&rebuilt, Symbol::Ite, 4) {
                if args[1].is_true() {
                    return args[2].clone();
                }
                if args[1] == Term::new_false() {
                    return args[3].clone();
                }
                if args[2] == args[3] {
                    return args[2].clone();
                }
            }
            rebuilt
        }

        recurse(term)
    }

    fn with_replaced_literal(
        &self,
        index: usize,
        replacements: Vec<Vec<Literal>>,
    ) -> Vec<Vec<Literal>> {
        let mut out = Vec::with_capacity(replacements.len());
        for mut replacement_literals in replacements {
            let mut literals = self.literals[..index].to_vec();
            literals.append(&mut replacement_literals);
            literals.extend_from_slice(&self.literals[index + 1..]);
            out.push(literals);
        }
        out
    }

    fn normalize_boolean_reduction(
        literals: Vec<Literal>,
        context: LocalContext,
        pinned_old_var_count: usize,
    ) -> BooleanReductionResult {
        let (_, default_var_ids) = Clause::normalize_with_var_ids(literals.clone(), &context);
        let pinned_old_vars: Vec<AtomId> = default_var_ids
            .iter()
            .copied()
            .filter(|id| (*id as usize) < pinned_old_var_count)
            .collect();
        let (clause, var_ids) =
            Clause::normalize_with_var_ids_prefilled(literals, &context, pinned_old_vars);
        BooleanReductionResult {
            clause,
            var_ids,
            pre_norm_context: context,
        }
    }

    fn with_replaced_literal_and_context(
        &self,
        index: usize,
        replacements: Vec<Vec<Literal>>,
        context: &LocalContext,
    ) -> Vec<BooleanReductionResult> {
        self.with_replaced_literal(index, replacements)
            .into_iter()
            .map(|literals| {
                Self::normalize_boolean_reduction(literals, context.clone(), self.context.len())
            })
            .collect()
    }

    fn reduce_negated_exists(term: &Term, context: &LocalContext) -> Option<(Term, LocalContext)> {
        let (binder_type, body) = term.as_ref().split_exists()?;
        let mut output_context = context.clone();
        let fresh_var = output_context.push_type(binder_type.to_owned()) as AtomId;
        let replacement = Term::new_variable(fresh_var);
        let reduced = body
            .to_owned()
            .substitute_bound(0, &replacement)
            .shift_bound(0, -1);
        Some((reduced, output_context))
    }

    pub fn find_boolean_reductions(
        &self,
        kernel_context: &KernelContext,
    ) -> Vec<BooleanReductionResult> {
        let bool_type = Term::bool_type();

        let mut answer = vec![];

        for i in 0..self.literals.len() {
            let literal = &self.literals[i];

            // Reduce signed boolean constants:
            // true / not false are tautological literals (drop this reduction path),
            // false / not true are impossible literals and can be removed from the disjunction.
            if literal.is_signed_term()
                && (literal.left.is_true() || literal.left == Term::new_false())
            {
                let literal_is_true = if literal.left.is_true() {
                    literal.positive
                } else {
                    !literal.positive
                };
                if !literal_is_true {
                    // A false literal in a disjunction can be removed.
                    // If it was the only literal, this yields the empty (impossible) clause.
                    answer.extend(self.with_replaced_literal_and_context(
                        i,
                        vec![vec![]],
                        &self.context,
                    ));
                }
                continue;
            }

            // General reduction for if-then-else terms:
            // ite(T, true, t, e)  -> t
            // ite(T, false, t, e) -> e
            // ite(T, c, t, t)     -> t
            let reduced_left = Self::simplify_ite_term(&literal.left);
            if reduced_left != literal.left {
                let reduced_lit =
                    Literal::new(literal.positive, reduced_left, literal.right.clone());
                answer.extend(self.with_replaced_literal_and_context(
                    i,
                    vec![vec![reduced_lit]],
                    &self.context,
                ));
            }
            let reduced_right = Self::simplify_ite_term(&literal.right);
            if reduced_right != literal.right {
                let reduced_lit =
                    Literal::new(literal.positive, literal.left.clone(), reduced_right);
                answer.extend(self.with_replaced_literal_and_context(
                    i,
                    vec![vec![reduced_lit]],
                    &self.context,
                ));
            }

            // Branch reduction for equalities/inequalities with ITE:
            // ite(T, c, t, e) = v   -> (not c or t = v) and (c or e = v)
            // ite(T, c, t, e) != v  -> (not c or t != v) and (c or e != v)
            if let Some(args) = Self::split_symbol_application(&literal.left, Symbol::Ite, 4) {
                let condition = args[1].clone();
                let then_lit =
                    Literal::new(literal.positive, args[2].clone(), literal.right.clone());
                let else_lit =
                    Literal::new(literal.positive, args[3].clone(), literal.right.clone());
                let replacements = vec![
                    vec![Literal::negative(condition.clone()), then_lit],
                    vec![Literal::positive(condition), else_lit],
                ];
                answer.extend(self.with_replaced_literal_and_context(
                    i,
                    replacements,
                    &self.context,
                ));
            }
            if let Some(args) = Self::split_symbol_application(&literal.right, Symbol::Ite, 4) {
                let condition = args[1].clone();
                let then_lit =
                    Literal::new(literal.positive, literal.left.clone(), args[2].clone());
                let else_lit =
                    Literal::new(literal.positive, literal.left.clone(), args[3].clone());
                let replacements = vec![
                    vec![Literal::negative(condition.clone()), then_lit],
                    vec![Literal::positive(condition), else_lit],
                ];
                answer.extend(self.with_replaced_literal_and_context(
                    i,
                    replacements,
                    &self.context,
                ));
            }

            if let Some(reduced) =
                Self::reduce_function_inequality_to_exists(literal, &self.context, kernel_context)
            {
                answer.extend(self.with_replaced_literal_and_context(
                    i,
                    vec![vec![Literal::positive(reduced)]],
                    &self.context,
                ));
            }

            if literal
                .left
                .get_type_with_context(&self.context, kernel_context)
                != bool_type
            {
                continue;
            }
            if literal.right.is_true() {
                if let Some(args) = Self::split_symbol_application(&literal.left, Symbol::Not, 1) {
                    let reduced = self.with_replaced_literal_and_context(
                        i,
                        vec![vec![Literal::from_signed_term(
                            args[0].clone(),
                            !literal.positive,
                        )]],
                        &self.context,
                    );
                    answer.extend(reduced);
                    continue;
                }

                if let Some(args) = Self::split_symbol_application(&literal.left, Symbol::Eq, 3) {
                    let eq_left = args[1].clone();
                    let eq_right = args[2].clone();
                    let reduced_lit = if literal.positive {
                        Literal::equals(eq_left, eq_right)
                    } else {
                        Literal::not_equals(eq_left, eq_right)
                    };
                    answer.extend(self.with_replaced_literal_and_context(
                        i,
                        vec![vec![reduced_lit]],
                        &self.context,
                    ));
                    continue;
                }

                if self.literals.len() > 1 && literal.positive && literal.left.as_ref().is_exists()
                {
                    continue;
                }

                if literal.positive {
                    if let Some((_witness, reduced)) =
                        Self::reduce_exists_with_obvious_witness(&literal.left)
                    {
                        answer.extend(self.with_replaced_literal_and_context(
                            i,
                            vec![vec![Literal::positive(reduced)]],
                            &self.context,
                        ));
                        continue;
                    }
                    if let Some(reduced) = Self::reduce_exists_with_choose(&literal.left) {
                        answer.extend(self.with_replaced_literal_and_context(
                            i,
                            vec![vec![Literal::positive(reduced)]],
                            &self.context,
                        ));
                        continue;
                    }
                } else if let Some(reduced) = Self::reduce_negated_forall(&literal.left) {
                    answer.extend(self.with_replaced_literal_and_context(
                        i,
                        vec![vec![Literal::positive(reduced)]],
                        &self.context,
                    ));
                    continue;
                } else if let Some((reduced, output_context)) =
                    Self::reduce_negated_exists(&literal.left, &self.context)
                {
                    answer.extend(self.with_replaced_literal_and_context(
                        i,
                        vec![vec![Literal::negative(reduced)]],
                        &output_context,
                    ));
                    continue;
                }

                if let Some(args) = Self::split_symbol_application(&literal.left, Symbol::And, 2) {
                    let left = args[0].clone();
                    let right = args[1].clone();
                    let replacements = if literal.positive {
                        vec![
                            vec![Literal::positive(left)],
                            vec![Literal::positive(right)],
                        ]
                    } else {
                        vec![vec![Literal::negative(left), Literal::negative(right)]]
                    };
                    answer.extend(self.with_replaced_literal_and_context(
                        i,
                        replacements,
                        &self.context,
                    ));
                    continue;
                }

                if let Some(args) = Self::split_symbol_application(&literal.left, Symbol::Or, 2) {
                    let left = args[0].clone();
                    let right = args[1].clone();
                    let replacements = if literal.positive {
                        vec![vec![Literal::positive(left), Literal::positive(right)]]
                    } else {
                        vec![
                            vec![Literal::negative(left)],
                            vec![Literal::negative(right)],
                        ]
                    };
                    answer.extend(self.with_replaced_literal_and_context(
                        i,
                        replacements,
                        &self.context,
                    ));
                    continue;
                }
                continue;
            }
            // We make two copies since there are two ways to do it
            let mut first = self.literals[..i].to_vec();
            let mut second = self.literals[..i].to_vec();
            if literal.positive {
                first.push(Literal::positive(literal.left.clone()));
                first.push(Literal::negative(literal.right.clone()));
                second.push(Literal::negative(literal.left.clone()));
                second.push(Literal::positive(literal.right.clone()));
            } else {
                first.push(Literal::negative(literal.left.clone()));
                first.push(Literal::negative(literal.right.clone()));
                second.push(Literal::positive(literal.left.clone()));
                second.push(Literal::positive(literal.right.clone()));
            }
            first.extend_from_slice(&self.literals[i + 1..]);
            second.extend_from_slice(&self.literals[i + 1..]);
            answer.push(Self::normalize_boolean_reduction(
                first,
                self.context.clone(),
                self.context.len(),
            ));
            answer.push(Self::normalize_boolean_reduction(
                second,
                self.context.clone(),
                self.context.len(),
            ));
        }
        answer
    }

    /// Generates all clauses that can be derived from this clause using boolean reduction.
    /// This is a convenience method that returns just the normalized clauses.
    pub fn boolean_reductions(&self, kernel_context: &KernelContext) -> Vec<Clause> {
        self.find_boolean_reductions(kernel_context)
            .into_iter()
            .map(|reduction| reduction.clause)
            .collect()
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.literals.is_empty() {
            write!(f, "<empty>")
        } else {
            for (i, literal) in self.literals.iter().enumerate() {
                if i > 0 {
                    write!(f, " or ")?;
                }
                write!(f, "{}", literal)?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::atom::Atom;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;
    use crate::kernel::types::GroundTypeId;
    use crate::module::ModuleId;

    /// Test that extensionality doesn't match clauses without function applications.
    /// This prevents infinite recursion when extensionality produces the same clause.
    #[test]
    fn test_extensionality_rejects_atomic_terms() {
        let kernel_context = KernelContext::new();

        // Create a clause like "g0 = x0" (global constant equals variable)
        let g0 = Term::atom(Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)));
        let x0 = Term::atom(Atom::FreeVariable(0));
        let literal = Literal::equals(g0, x0);

        let some_type = Term::ground_type(GroundTypeId::test(2));
        let context = LocalContext::from_types(vec![some_type]);
        let clause = Clause::from_literals_unnormalized(vec![literal], &context);

        // Extensionality should not match this clause since both terms are atomic
        assert!(
            clause.find_extensionality(&kernel_context).is_none(),
            "Extensionality should not match atomic terms"
        );
    }

    /// Test that extensionality rejects tautologies like f(x0) = f(x0).
    /// Even after peeling x0, the result would be f = f which is useless.
    #[test]
    fn test_extensionality_rejects_tautology() {
        let kernel_context = KernelContext::new();

        // Create a clause like "f(x0) = f(x0)" (identical terms)
        let x0 = Term::atom(Atom::FreeVariable(0));
        let f_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x0.clone()],
        );
        let literal = Literal::equals(f_x0.clone(), f_x0);

        let some_type = Term::ground_type(GroundTypeId::test(2));
        let context = LocalContext::from_types(vec![some_type]);
        let clause = Clause::from_literals_unnormalized(vec![literal], &context);

        // Extensionality should reject this since it would produce a tautology
        assert!(
            clause.find_extensionality(&kernel_context).is_none(),
            "Extensionality should reject tautologies"
        );
    }

    /// Test that extensionality works with ground prefix (like type arguments).
    /// g0(c0, x) = g1(c0, x) where c0 is ground constant, x is free var → g0(c0) = g1(c0)
    #[test]
    fn test_extensionality_with_ground_prefix() {
        let mut kctx = KernelContext::new();
        // c0 is a ground constant, g0 and g1 are functions that take Bool, Bool -> Bool
        kctx.parse_constant("c0", "Bool")
            .parse_constant("g0", "Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool");

        // Create clause: g0(c0, x0) = g1(c0, x0)
        let clause = kctx.parse_clause("g0(c0, x0) = g1(c0, x0)", &["Bool"]);

        // Extensionality should work, peeling x0 but keeping c0
        let result = clause.find_extensionality(&kctx);
        assert!(
            result.is_some(),
            "Extensionality should work with ground prefix"
        );

        // Result should be g0(c0) = g1(c0)
        let result_lits = result.unwrap();
        assert_eq!(result_lits.len(), 1);
        let result_lit = &result_lits[0];
        // Both sides should have 1 argument (c0)
        assert_eq!(result_lit.left.num_args(), 1);
        assert_eq!(result_lit.right.num_args(), 1);
    }

    /// Test that extensionality works with same head but different prefix.
    /// g2(c0, x) = g2(c1, x) where c0, c1 are constants, x is free var -> g2(c0) = g2(c1)
    #[test]
    fn test_extensionality_same_head_different_prefix() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool")
            .parse_constant("c1", "Bool")
            .parse_constant("g2", "Bool -> Bool -> Bool");

        // Create clause: g2(c0, x0) = g2(c1, x0)
        let clause = kctx.parse_clause("g2(c0, x0) = g2(c1, x0)", &["Bool"]);

        // Extensionality should work, peeling x0 to derive g2(c0) = g2(c1)
        let result = clause.find_extensionality(&kctx);
        assert!(
            result.is_some(),
            "Extensionality should work with same head but different prefix"
        );

        // Result should be g2(c0) = g2(c1)
        let result_lits = result.unwrap();
        assert_eq!(result_lits.len(), 1);
        let result_lit = &result_lits[0];
        // Both sides should have 1 argument
        assert_eq!(result_lit.left.num_args(), 1);
        assert_eq!(result_lit.right.num_args(), 1);
        // The heads should be the same (both g2)
        assert_eq!(
            result_lit.left.get_head_atom(),
            result_lit.right.get_head_atom()
        );
    }

    #[test]
    fn test_extensionality_with_guard_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool")
            .parse_constant("c1", "Bool")
            .parse_constant("g0", "Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool");

        let clause = kctx.parse_clause("not c1 or g0(c0, x0) = g1(c0, x0)", &["Bool"]);
        let result = clause.find_extensionality(&kctx);
        assert!(
            result.is_some(),
            "Extensionality should work when peeled variables do not appear in the guard"
        );

        let ext_clause = Clause::new(result.unwrap(), clause.get_local_context());
        let expected = kctx.parse_clause("not c1 or g0(c0) = g1(c0)", &[]);
        assert_eq!(ext_clause, expected);
    }

    #[test]
    fn test_extensionality_rejects_guard_with_peeled_var() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool")
            .parse_constant("g0", "Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool")
            .parse_constant("g2", "Bool -> Bool");

        let clause = kctx.parse_clause("not g2(x0) or g0(c0, x0) = g1(c0, x0)", &["Bool"]);
        assert!(
            clause.find_extensionality(&kctx).is_none(),
            "Extensionality must not peel variables that still appear in another literal"
        );
    }

    /// Test that extensionality rejects duplicate variables.
    /// g0(x, x) = g1(x, x) must NOT derive g0 = g1.
    #[test]
    fn test_extensionality_rejects_duplicate_variables() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool");

        // Create clause: g0(x0, x0) = g1(x0, x0) using x0 for both positions
        let clause = kctx.parse_clause("g0(x0, x0) = g1(x0, x0)", &["Bool"]);

        // Extensionality should NOT fully peel because x0 appears twice
        let result = clause.find_extensionality(&kctx);

        // If extensionality applies, verify it doesn't peel down to g0 = g1
        if let Some(result_lits) = result {
            let result_lit = &result_lits[0];
            // Should NOT be g0 = g1 (both with 0 args)
            assert!(
                result_lit.left.num_args() > 0 || result_lit.right.num_args() > 0,
                "Extensionality should not derive g0 = g1 from g0(x, x) = g1(x, x)"
            );
        }
        // If it returns None, that's also acceptable (conservative behavior)
    }

    /// Test that normalize_with_var_ids correctly preserves variable types when
    /// literals are reordered during sorting. This reproduces a bug where
    /// variable types were getting shuffled incorrectly.
    #[test]
    fn test_normalize_with_var_ids_preserves_types() {
        // Create a clause with mixed types:
        // not f(x0, x1, x2) or x2
        // where x0: Foo, x1: Foo, x2: Bool
        //
        // After sorting, the literals may be reordered. The variable renumbering
        // should correctly track which type belongs to which new variable ID.

        let type_foo = Term::ground_type(GroundTypeId::test(2)); // Some non-Bool type
        let type_bool = Term::ground_type(GroundTypeId::test(1)); // Bool

        // x0 and x1 are Foo, x2 is Bool
        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        let x2 = Term::atom(Atom::FreeVariable(2));

        // Create f(x0, x1, x2) - a function application
        let f_args = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x0.clone(), x1.clone(), x2.clone()],
        );

        // Literal 1: not f(x0, x1, x2) = true (negative Bool equality)
        let lit1 = Literal::new(false, f_args.clone(), Term::new_true());

        // Literal 2: x2 = true (positive Bool equality)
        let lit2 = Literal::new(true, x2.clone(), Term::new_true());

        // Context: x0:Foo, x1:Foo, x2:Bool
        let context =
            LocalContext::from_types(vec![type_foo.clone(), type_foo.clone(), type_bool.clone()]);

        // Normalize the clause
        let (clause, _var_ids) = Clause::normalize_with_var_ids(vec![lit1, lit2], &context);

        // After normalization, check the output context:
        // Should have 3 variables with types Foo, Foo, Bool
        // The order may vary but the types should be consistent
        assert_eq!(clause.context.len(), 3);

        // Count how many Foo and Bool types we have
        let mut foo_count = 0;
        let mut bool_count = 0;
        for i in 0..clause.context.len() {
            match clause.context.get_var_type(i) {
                Some(t) if *t == type_foo => foo_count += 1,
                Some(t) if *t == type_bool => bool_count += 1,
                _ => panic!("Unexpected type in context"),
            }
        }
        assert_eq!(foo_count, 2, "Should have 2 Foo variables");
        assert_eq!(bool_count, 1, "Should have 1 Bool variable");

        // Specifically check that the literal that is just a variable (from lit2)
        // has the correct Bool type in the context
        for lit in &clause.literals {
            if lit.left.is_atomic() {
                if let Atom::FreeVariable(var_id) = lit.left.get_head_atom() {
                    let var_type = clause.context.get_var_type(*var_id as usize).unwrap();
                    assert_eq!(
                        *var_type, type_bool,
                        "Variable in atomic Bool literal should have Bool type, got {:?}",
                        var_type
                    );
                }
            }
        }
    }

    /// Test that validation catches applying a Bool to a Bool (c0(c1) where both are Bool).
    #[test]
    #[should_panic(expected = "Function type expected")]
    fn test_validation_catches_bool_applied_to_bool() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");
        // c0 and c1 are both Bool, so c0(c1) is invalid - can't apply Bool to Bool
        kctx.parse_clause("c0(c1)", &[]);
    }

    /// Test that validation catches type mismatches in literals (left and right have different types).
    #[test]
    #[should_panic(expected = "Literal type mismatch")]
    fn test_validation_catches_literal_type_mismatch() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("c0", "Bool");
        // g0 is Bool -> Bool, c0 is Bool, so g0 = c0 is a type mismatch
        kctx.parse_clause("g0 = c0", &[]);
    }

    /// Test that validation catches missing variable types in context.
    #[test]
    #[should_panic(expected = "variable x0 not found")]
    fn test_validation_catches_missing_variable_type() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");
        // x0 is used but no variable types provided
        kctx.parse_clause("x0 = c0", &[]);
    }

    /// Test that valid clauses pass validation.
    #[test]
    fn test_valid_clause_passes_validation() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constants(&["c0", "c1"], "Bool");
        // g0(c0) is Bool -> Bool applied to Bool = Bool, c1 is Bool, so this is valid
        let clause = kctx.parse_clause("g0(c0) = c1", &[]);
        assert_eq!(clause.literals.len(), 1);
    }

    /// Test that extensionality works with asymmetric arities.
    /// g0(c0, c1, x0) = g1(c0, x0) where c0, c1 are ground constants, x0 is free var
    /// The trailing x0 matches on both sides, so we should be able to peel x0:
    /// g0(c0, c1) = g1(c0)
    #[test]
    fn test_extensionality_asymmetric_arities() {
        let mut kctx = KernelContext::new();
        // c0 and c1 are ground type constants (like type parameters T and Nat)
        // g0 takes 3 args: T, Nat, value -> result
        // g1 takes 2 args: T, value -> result
        kctx.parse_constant("c0", "Bool")
            .parse_constant("c1", "Bool")
            .parse_constant("g0", "Bool -> Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool");

        // Create clause: g0(c0, c1, x0) = g1(c0, x0)
        // This represents: intersection_family(T, Nat, seq) = seq_intersection(T, seq)
        let clause = kctx.parse_clause("g0(c0, c1, x0) = g1(c0, x0)", &["Bool"]);

        // Extensionality should work: x0 is a free variable at the end of both sides
        let result = clause.find_extensionality(&kctx);
        assert!(
            result.is_some(),
            "Extensionality should work with asymmetric arities when trailing args match"
        );

        // Result should be g0(c0, c1) = g1(c0)
        let result_lits = result.unwrap();
        assert_eq!(result_lits.len(), 1);
        let result_lit = &result_lits[0];
        // g0 side should have 2 args (c0, c1)
        // g1 side should have 1 arg (c0)
        let (longer, shorter) = if result_lit.left.num_args() >= result_lit.right.num_args() {
            (&result_lit.left, &result_lit.right)
        } else {
            (&result_lit.right, &result_lit.left)
        };
        assert_eq!(longer.num_args(), 2, "g0 should have 2 args after peeling");
        assert_eq!(shorter.num_args(), 1, "g1 should have 1 arg after peeling");
    }

    #[test]
    fn test_boolean_reduction_signed_and_splits_clause() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");

        let a = kctx.parse_term("c0");
        let b = kctx.parse_term("c1");
        let clause = Clause::new(
            vec![Literal::positive(Term::and(a.clone(), b.clone()))],
            &LocalContext::empty(),
        );
        let reductions = clause.boolean_reductions(&kctx);

        let expected_a = Clause::new(vec![Literal::positive(a)], &LocalContext::empty());
        let expected_b = Clause::new(vec![Literal::positive(b)], &LocalContext::empty());
        assert!(
            reductions.contains(&expected_a),
            "expected reduction to include {}",
            expected_a
        );
        assert!(
            reductions.contains(&expected_b),
            "expected reduction to include {}",
            expected_b
        );
    }

    #[test]
    fn test_boolean_reduction_signed_not_flips_sign() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        let a = kctx.parse_term("c0");
        let clause = Clause::new(
            vec![Literal::positive(Term::not(a.clone()))],
            &LocalContext::empty(),
        );
        let reductions = clause.boolean_reductions(&kctx);

        let expected = Clause::new(vec![Literal::negative(a)], &LocalContext::empty());
        assert_eq!(clause, expected);
        assert!(reductions.is_empty());
    }

    #[test]
    fn test_boolean_reduction_eq_signed_to_equality_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");

        let left = kctx.parse_term("c0");
        let right = kctx.parse_term("c1");
        let eq_term = Term::eq(Term::bool_type(), left.clone(), right.clone());

        let positive_clause = Clause::new(
            vec![Literal::positive(eq_term.clone())],
            &LocalContext::empty(),
        );
        let positive_reductions = positive_clause.boolean_reductions(&kctx);
        let expected_positive = Clause::new(
            vec![Literal::equals(left.clone(), right.clone())],
            &LocalContext::empty(),
        );
        assert!(
            positive_reductions.contains(&expected_positive),
            "expected reduction to include {}",
            expected_positive
        );

        let negative_clause = Clause::new(vec![Literal::negative(eq_term)], &LocalContext::empty());
        let negative_reductions = negative_clause.boolean_reductions(&kctx);
        let expected_negative = Clause::new(
            vec![Literal::not_equals(left, right)],
            &LocalContext::empty(),
        );
        assert!(
            negative_reductions.contains(&expected_negative),
            "expected reduction to include {}",
            expected_negative
        );
    }

    #[test]
    fn test_boolean_reduction_exists_eq_self_witness() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        let exists_term = Term::exists(
            Term::bool_type(),
            Term::eq(
                Term::bool_type(),
                Term::atom(Atom::BoundVariable(0)),
                kctx.parse_term("c0"),
            ),
        );
        let clause = Clause::new(vec![Literal::positive(exists_term)], &LocalContext::empty());
        let reductions = clause.boolean_reductions(&kctx);
        let has_non_exists_reduction = reductions.iter().any(|clause| {
            clause
                .literals
                .iter()
                .all(|lit| !lit.left.as_ref().is_exists() && !lit.right.as_ref().is_exists())
        });
        assert!(
            has_non_exists_reduction,
            "expected at least one reduction to eliminate the exists term"
        );
    }

    #[test]
    fn test_boolean_reduction_exists_eq_var_witness() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        let exists_term = Term::exists(
            Term::bool_type(),
            Term::eq(
                Term::bool_type(),
                Term::atom(Atom::BoundVariable(0)),
                Term::new_variable(0),
            ),
        );
        let context = LocalContext::from_types(vec![Term::bool_type()]);
        let clause = Clause::new(vec![Literal::positive(exists_term)], &context);
        let reductions = clause.boolean_reductions(&kctx);
        let has_non_exists_reduction = reductions.iter().any(|clause| {
            clause
                .literals
                .iter()
                .all(|lit| !lit.left.as_ref().is_exists() && !lit.right.as_ref().is_exists())
        });
        assert!(
            has_non_exists_reduction,
            "expected at least one reduction to eliminate the exists term"
        );
    }

    #[test]
    fn test_boolean_reduction_positive_exists_in_disjunction_stays_inline() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "g0"], "Bool");

        let exists_term = Term::exists(Term::bool_type(), kctx.parse_term("g0"));
        let clause = Clause::new(
            vec![
                Literal::positive(kctx.parse_term("c0")),
                Literal::positive(exists_term),
            ],
            &LocalContext::empty(),
        );

        assert!(
            clause.boolean_reductions(&kctx).is_empty(),
            "positive exists should not reduce when it is only one disjunct among others"
        );
    }

    #[test]
    fn test_boolean_reduction_negated_exists_opens_to_free_variable() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool");

        let exists_term = Term::exists(
            Term::bool_type(),
            kctx.parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        let clause = Clause::new(vec![Literal::negative(exists_term)], &LocalContext::empty());
        let expected = Clause::new(
            vec![Literal::negative(
                kctx.parse_term("g0").apply(&[Term::new_variable(0)]),
            )],
            &LocalContext::from_types(vec![Term::bool_type()]),
        );
        assert_eq!(clause.boolean_reductions(&kctx), vec![expected]);
    }

    #[test]
    fn test_boolean_reduction_not_exists_reduces_once_then_stops() {
        let kctx = KernelContext::new();
        let exists_term = Term::exists(Term::bool_type(), Term::new_true());
        let clause = Clause::new(
            vec![Literal::positive(Term::not(exists_term.clone()))],
            &LocalContext::empty(),
        );

        let expected = Clause::new(vec![Literal::negative(exists_term)], &LocalContext::empty());
        assert_eq!(clause, expected);

        let first = clause.boolean_reductions(&kctx);
        assert_eq!(first, vec![Clause::impossible()]);
        assert!(Clause::impossible().boolean_reductions(&kctx).is_empty());
    }

    #[test]
    fn test_boolean_reduction_negated_forall_becomes_exists_negated_body() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool");

        let forall_term = Term::forall(
            Term::bool_type(),
            kctx.parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        let clause = Clause::new(vec![Literal::negative(forall_term)], &LocalContext::empty());
        let expected_clause = Clause::new(
            vec![Literal::positive(Term::exists(
                Term::bool_type(),
                Term::not(
                    kctx.parse_term("g0")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                ),
            ))],
            &LocalContext::empty(),
        );
        assert_eq!(clause, expected_clause);

        let choose = Term::choose(
            Term::bool_type(),
            Term::lambda(
                Term::bool_type(),
                Term::not(
                    kctx.parse_term("g0")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                ),
            ),
        );
        let expected_reduction = Clause::new(
            vec![Literal::negative(kctx.parse_term("g0").apply(&[choose]))],
            &LocalContext::empty(),
        );
        assert_eq!(clause.boolean_reductions(&kctx), vec![expected_reduction]);
    }

    #[test]
    fn test_boolean_reduction_negated_forall_normalizes_resulting_exists_body() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool");

        let body = Term::not(Term::and(
            Term::atom(Atom::BoundVariable(0)),
            kctx.parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        ));
        let forall_term = Term::forall(Term::bool_type(), body);
        let clause = Clause::new(vec![Literal::negative(forall_term)], &LocalContext::empty());
        let expected_clause = Clause::new(
            vec![Literal::positive(Term::exists(
                Term::bool_type(),
                Term::and(
                    Term::atom(Atom::BoundVariable(0)),
                    kctx.parse_term("g0")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                ),
            ))],
            &LocalContext::empty(),
        );
        assert_eq!(clause, expected_clause);

        let choose = Term::choose(
            Term::bool_type(),
            Term::lambda(
                Term::bool_type(),
                Term::and(
                    Term::atom(Atom::BoundVariable(0)),
                    kctx.parse_term("g0")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                ),
            ),
        );
        let expected_reduction = Clause::new(
            vec![Literal::positive(Term::and(
                choose.clone(),
                kctx.parse_term("g0").apply(&[choose]),
            ))],
            &LocalContext::empty(),
        );
        assert_eq!(clause.boolean_reductions(&kctx), vec![expected_reduction]);
    }

    #[test]
    fn test_boolean_reduction_function_inequality_becomes_exists() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["g0", "g1"], "Bool -> Bool");

        let clause = Clause::new(
            vec![Literal::not_equals(
                kctx.parse_term("g0"),
                kctx.parse_term("g1"),
            )],
            &LocalContext::empty(),
        );
        let expected = Clause::new(
            vec![Literal::positive(Term::exists(
                Term::bool_type(),
                Term::not(Term::eq(
                    Term::bool_type(),
                    kctx.parse_term("g0")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                    kctx.parse_term("g1")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                )),
            ))],
            &LocalContext::empty(),
        );

        assert_eq!(clause.boolean_reductions(&kctx), vec![expected]);
    }

    #[test]
    fn test_boolean_reduction_function_inequality_composes_with_exists() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["g0", "g1"], "Bool -> Bool");

        let start = Clause::new(
            vec![Literal::not_equals(
                kctx.parse_term("g0"),
                kctx.parse_term("g1"),
            )],
            &LocalContext::empty(),
        );
        let first = start.boolean_reductions(&kctx);
        assert_eq!(first.len(), 1, "expected function inequality -> exists");

        let second = first[0].boolean_reductions(&kctx);
        assert_eq!(second.len(), 1, "expected exists -> choose witness");

        let choose = Term::choose(
            Term::bool_type(),
            Term::lambda(
                Term::bool_type(),
                Term::not(Term::eq(
                    Term::bool_type(),
                    kctx.parse_term("g0")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                    kctx.parse_term("g1")
                        .apply(&[Term::atom(Atom::BoundVariable(0))]),
                )),
            ),
        );
        let expected_second = Clause::new(
            vec![Literal::negative(Term::eq(
                Term::bool_type(),
                kctx.parse_term("g0").apply(&[choose.clone()]),
                kctx.parse_term("g1").apply(&[choose.clone()]),
            ))],
            &LocalContext::empty(),
        );
        assert_eq!(second, vec![expected_second.clone()]);

        let third = expected_second.boolean_reductions(&kctx);
        let expected_third = Clause::new(
            vec![Literal::not_equals(
                kctx.parse_term("g0").apply(&[choose.clone()]),
                kctx.parse_term("g1").apply(&[choose]),
            )],
            &LocalContext::empty(),
        );
        assert_eq!(third, vec![expected_third]);
    }

    #[test]
    fn test_boolean_reduction_negative_signed_not_becomes_positive_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool");

        let inner = kctx.parse_term("g0").apply(&[Term::new_variable(0)]);
        let clause = Clause::new(
            vec![Literal::negative(Term::not(inner.clone()))],
            &LocalContext::from_types(vec![Term::bool_type()]),
        );
        let expected = Clause::new(
            vec![Literal::positive(inner)],
            &LocalContext::from_types(vec![Term::bool_type()]),
        );

        assert_eq!(clause, expected);
        assert!(clause.boolean_reductions(&kctx).is_empty());
    }

    #[test]
    fn test_boolean_reduction_negated_exists_surfaces_to_clause_level() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool");
        kctx.parse_constant("g1", "Bool -> Bool");

        let outer_var = Term::new_variable(0);
        let exists_term = Term::exists(
            Term::bool_type(),
            kctx.parse_term("g1")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        let clause = Clause::new(
            vec![
                Literal::positive(kctx.parse_term("g0").apply(&[outer_var.clone()])),
                Literal::negative(exists_term),
            ],
            &LocalContext::from_types(vec![Term::bool_type()]),
        );
        let expected = Clause::from_literals_unnormalized(
            vec![
                Literal::negative(kctx.parse_term("g1").apply(&[Term::new_variable(1)])),
                Literal::positive(kctx.parse_term("g0").apply(&[outer_var])),
            ],
            &LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]),
        );
        assert_eq!(clause.boolean_reductions(&kctx), vec![expected]);
    }

    #[test]
    fn test_reduction_collapses_ite_with_equal_branches_in_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2"], "Bool");

        let cond = kctx.parse_term("c0");
        let x = kctx.parse_term("c1");
        let y = kctx.parse_term("c2");
        let ite = Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
            Term::bool_type(),
            cond,
            x.clone(),
            x.clone(),
        ]);

        let clause = Clause::new(
            vec![Literal::equals(ite, y.clone())],
            &LocalContext::empty(),
        );
        let reductions = clause.boolean_reductions(&kctx);
        let expected = Clause::new(vec![Literal::equals(x, y)], &LocalContext::empty());
        assert!(
            reductions.contains(&expected),
            "expected reduction to include {}",
            expected
        );
    }

    #[test]
    fn test_reduction_collapses_ite_with_true_condition_in_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2"], "Bool");

        let x = kctx.parse_term("c1");
        let y = kctx.parse_term("c2");
        let ite = Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
            Term::bool_type(),
            Term::new_true(),
            x.clone(),
            y.clone(),
        ]);

        let clause = Clause::new(
            vec![Literal::equals(ite, y.clone())],
            &LocalContext::empty(),
        );
        let reductions = clause.boolean_reductions(&kctx);
        let expected = Clause::new(vec![Literal::equals(x, y)], &LocalContext::empty());
        assert!(
            reductions.contains(&expected),
            "expected reduction to include {}",
            expected
        );
    }

    #[test]
    fn test_reduction_splits_ite_equality_into_branch_clauses() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3"], "Bool");

        let cond = kctx.parse_term("c0");
        let then_branch = kctx.parse_term("c1");
        let else_branch = kctx.parse_term("c2");
        let target = kctx.parse_term("c3");
        let ite = Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
            Term::bool_type(),
            cond.clone(),
            then_branch.clone(),
            else_branch.clone(),
        ]);

        let clause = Clause::new(
            vec![Literal::equals(ite, target.clone())],
            &LocalContext::empty(),
        );
        let reductions = clause.boolean_reductions(&kctx);

        let then_clause = Clause::new(
            vec![
                Literal::negative(cond.clone()),
                Literal::equals(then_branch, target.clone()),
            ],
            &LocalContext::empty(),
        );
        let else_clause = Clause::new(
            vec![
                Literal::positive(cond),
                Literal::equals(else_branch, target),
            ],
            &LocalContext::empty(),
        );

        assert!(
            reductions.contains(&then_clause),
            "expected reduction to include {}",
            then_clause
        );
        assert!(
            reductions.contains(&else_clause),
            "expected reduction to include {}",
            else_clause
        );
    }

    #[test]
    fn test_boolean_reduction_outputs_normalized_clauses() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("g1", "(Bool, Bool, Bool, Bool, Bool) -> Bool");

        let x0 = Term::new_variable(0);
        let x1 = Term::new_variable(1);
        let x2 = Term::new_variable(2);
        let x3 = Term::new_variable(3);
        let x4 = Term::new_variable(4);
        let nested_ite = Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
            Term::bool_type(),
            kctx.parse_term("g0").apply(&[x0.clone()]),
            x1.clone(),
            Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
                Term::bool_type(),
                kctx.parse_term("g0").apply(&[x2.clone()]),
                x3,
                x4.clone(),
            ]),
        ]);
        let target = kctx.parse_term("g1").apply(&[
            x0.clone(),
            x1,
            x2.clone(),
            Term::new_variable(3),
            x4.clone(),
        ]);

        let clause = Clause::new(
            vec![Literal::equals(nested_ite, target.clone())],
            &LocalContext::from_types(vec![
                Term::bool_type(),
                Term::bool_type(),
                Term::bool_type(),
                Term::bool_type(),
                Term::bool_type(),
            ]),
        );

        assert!(
            clause
                .boolean_reductions(&kctx)
                .iter()
                .all(|reduction| { reduction.is_normalized_preserving_locals() }),
            "expected all boolean-reduction outputs to be normalized"
        );
    }

    #[test]
    fn test_beta_reduction_under_binder_is_capture_avoiding() {
        // forall(Bool => (lambda(Bool => lambda(Bool => b1)))(b0))
        // should beta-reduce to:
        // forall(Bool => lambda(Bool => b1))
        // where b1 still refers to the outer forall binder.
        let lambda = Term::lambda(
            Term::bool_type(),
            Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(1))),
        );
        let applied = lambda.apply(&[Term::atom(Atom::BoundVariable(0))]);
        let term = Term::forall(Term::bool_type(), applied);

        let reduced = Clause::simplify_ite_term(&term);
        let expected = Term::forall(
            Term::bool_type(),
            Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(1))),
        );

        assert_eq!(reduced, expected);
    }
}
