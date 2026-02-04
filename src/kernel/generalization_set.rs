use std::cmp::Ordering;
use std::vec;

use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pdt::Pdt;
use crate::kernel::term::{Decomposition, TermRef};

/// The GeneralizationSet stores general clauses in a way that allows us to quickly check whether
/// a new clause is a specialization of an existing one.
#[derive(Clone)]
pub struct GeneralizationSet {
    /// Stores an id for each clause.
    tree: Pdt<usize>,
}

impl GeneralizationSet {
    pub fn new() -> GeneralizationSet {
        GeneralizationSet { tree: Pdt::new() }
    }

    /// Inserts a clause into the set, reordering it in every way that is KBO-nonincreasing.
    pub fn insert(&mut self, mut clause: Clause, id: usize, kernel_context: &KernelContext) {
        let mut generalized = vec![];
        all_generalized_forms(&mut clause, 0, &mut generalized, kernel_context);
        for c in generalized {
            self.tree.insert_clause(&c, id);
        }
    }

    pub fn find_generalization(
        &self,
        clause: Clause,
        kernel_context: &KernelContext,
    ) -> Option<usize> {
        let special = specialized_form(clause, kernel_context);
        if let Some(id) = self.tree.find_clause(&special, kernel_context) {
            return Some(*id);
        }
        None
    }
}

/// Compare two literals in a substitution-invariant way.
/// First compares left terms, then right terms if left terms are equal.
fn sub_invariant_literal_cmp(
    lit1: &Literal,
    lit2: &Literal,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Option<Ordering> {
    // First compare the left terms
    let left_cmp = sub_invariant_term_cmp(
        lit1.left.as_ref(),
        !lit1.positive,
        lit2.left.as_ref(),
        !lit2.positive,
        local_context,
        kernel_context,
    );
    match left_cmp {
        Some(Ordering::Equal) => {
            // If left terms are equal, compare right terms
            sub_invariant_term_cmp(
                lit1.right.as_ref(),
                !lit1.positive,
                lit2.right.as_ref(),
                !lit2.positive,
                local_context,
                kernel_context,
            )
        }
        other => other,
    }
}

/// Stable under variable substitution, like KBO, but hopefully closer to total in practice.
/// Specifically, if two terms are comparable, they must stay comparable under substitution.
/// If two terms are not comparable, anything goes under substitution.
///
/// Returns Greater if self > other.
/// Returns Less if other > self.
/// Returns None if they are not comparable.
/// Returns Equal if they are actually equal.
///
/// Concrete terms should always be orderable.
pub fn sub_invariant_term_cmp(
    left: TermRef,
    left_neg: bool,
    right: TermRef,
    right_neg: bool,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Option<Ordering> {
    // Compare the signs first, because signs are completely stable under substitution.
    // This ensures positive/negative literals sort consistently regardless of type variables.
    let neg_cmp = left_neg.cmp(&right_neg);
    if neg_cmp != Ordering::Equal {
        return Some(neg_cmp);
    }

    // If either term is a variable, we can't compare them in a substitution-invariant way.
    if left.get_head_atom().is_variable() || right.get_head_atom().is_variable() {
        return None;
    }

    // Compare the term types, but only if neither type involves a free variable.
    // If either type contains a FreeVariable, the comparison is not stable
    // under substitution (because FreeVariable ordering differs from Symbol ordering).
    // BoundVariables are stable - they only appear in type signatures (like dependent types)
    // and don't change during variable substitution.
    let left_type = left.get_type_with_context(local_context, kernel_context);
    let right_type = right.get_type_with_context(local_context, kernel_context);
    if left_type.has_free_variable() || right_type.has_free_variable() {
        // Types involve free variables, comparison not stable under substitution
        return None;
    }
    let type_cmp = left_type.cmp(&right_type);
    if type_cmp != Ordering::Equal {
        return Some(type_cmp);
    }

    // Use decompose to recursively compare
    match (left.decompose(), right.decompose()) {
        (Decomposition::Atom(l_atom), Decomposition::Atom(r_atom)) => Some(l_atom.cmp(r_atom)),
        (Decomposition::Application(l_func, l_arg), Decomposition::Application(r_func, r_arg)) => {
            // Need to check for variables in function and argument parts
            // Since we already checked that top-level heads aren't variables,
            // but we still need to recurse properly
            match sub_invariant_term_cmp(
                l_func,
                false,
                r_func,
                false,
                local_context,
                kernel_context,
            ) {
                Some(Ordering::Equal) => sub_invariant_term_cmp(
                    l_arg,
                    false,
                    r_arg,
                    false,
                    local_context,
                    kernel_context,
                ),
                x => x,
            }
        }
        (Decomposition::Pi(l_input, l_output), Decomposition::Pi(r_input, r_output)) => {
            // Compare Pi types recursively
            match sub_invariant_term_cmp(
                l_input,
                false,
                r_input,
                false,
                local_context,
                kernel_context,
            ) {
                Some(Ordering::Equal) => sub_invariant_term_cmp(
                    l_output,
                    false,
                    r_output,
                    false,
                    local_context,
                    kernel_context,
                ),
                x => x,
            }
        }
        // Atom vs Application mismatch - shouldn't happen with equal heads and same num_args
        // But could happen with different structure, return based on which is simpler
        (Decomposition::Atom(_), Decomposition::Application(_, _)) => Some(Ordering::Less),
        (Decomposition::Application(_, _), Decomposition::Atom(_)) => Some(Ordering::Greater),
        // Pi vs other structures
        (Decomposition::Pi(_, _), _) => Some(Ordering::Less),
        (_, Decomposition::Pi(_, _)) => Some(Ordering::Greater),
    }
}

/// The generalized and specialized forms relate to each other.
/// When we specialize a clause and put it into the specialized form, it must match
/// one of the generalized forms.
/// The "form" includes both the order of the literals and the direction of each literal.
///
/// Call with zero to start the recursion. First we check all directions of the literals.
/// The start index is the first one to consider swapping.
fn all_generalized_forms(
    base_clause: &mut Clause,
    start_index: usize,
    output: &mut Vec<Clause>,
    kernel_context: &KernelContext,
) {
    if start_index >= base_clause.literals.len() {
        // We have a complete clause, so we can move on to the reordering stage.
        all_generalized_orders(base_clause, output, kernel_context);
        return;
    }
    let literal = &base_clause.literals[start_index];
    let local_context = base_clause.get_local_context();
    // Ignore literal sign in this stage
    let cmp = sub_invariant_term_cmp(
        literal.left.as_ref(),
        true,
        literal.right.as_ref(),
        true,
        local_context,
        kernel_context,
    );
    if cmp != Some(Ordering::Less) {
        // The pre-existing direction is okay.
        all_generalized_forms(base_clause, start_index + 1, output, kernel_context);
    }
    if cmp == None || cmp == Some(Ordering::Less) {
        // The swapped direction is okay.
        base_clause.literals[start_index].flip();
        all_generalized_forms(base_clause, start_index + 1, output, kernel_context);
        base_clause.literals[start_index].flip();
    }
}

/// Generate all orders of the provided clause that are a valid generalized form.
fn all_generalized_orders(
    base_clause: &Clause,
    output: &mut Vec<Clause>,
    kernel_context: &KernelContext,
) {
    let local_context = base_clause.get_local_context();

    // Helper function to generate all permutations recursively
    fn generate_permutations(
        literals: &[Literal],
        current: &mut Vec<Literal>,
        used: &mut Vec<bool>,
        output: &mut Vec<Clause>,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        // Base case: we've built a complete permutation
        if current.len() == literals.len() {
            let mut clause = Clause::from_literals_unnormalized(current.clone(), local_context);
            clause.normalize_var_ids_types_last();
            output.push(clause);
            return;
        }

        // Try each unused literal as the next element
        for i in 0..literals.len() {
            if used[i] {
                continue;
            }

            // Check if this literal can be the next one in a non-increasing order
            if let Some(last) = current.last() {
                let cmp =
                    sub_invariant_literal_cmp(last, &literals[i], local_context, kernel_context);
                if cmp == Some(Ordering::Less) {
                    continue;
                }
            }

            // Mark this literal as used
            used[i] = true;
            current.push(literals[i].clone());

            // Recurse
            generate_permutations(
                literals,
                current,
                used,
                output,
                local_context,
                kernel_context,
            );

            // Backtrack
            current.pop();
            used[i] = false;
        }
    }

    let mut current = Vec::new();
    let mut used = vec![false; base_clause.literals.len()];
    generate_permutations(
        &base_clause.literals,
        &mut current,
        &mut used,
        output,
        local_context,
        kernel_context,
    );
}

/// Put this clause into the "specialized" form.
/// This should only be called on concrete clauses.
fn specialized_form(mut clause: Clause, kernel_context: &KernelContext) -> Clause {
    let local_context = clause.get_local_context().clone();

    // First, ensure each literal has the larger term on the left
    for literal in &mut clause.literals {
        let cmp = sub_invariant_term_cmp(
            literal.left.as_ref(),
            true,
            literal.right.as_ref(),
            true,
            &local_context,
            kernel_context,
        )
        .expect("Concrete terms should always be comparable");
        if cmp == Ordering::Less {
            // The right term is larger, so swap
            literal.flip();
        }
    }

    // Then, sort the literals using our comparison function
    // Since this is for concrete clauses, we can unwrap the comparison
    clause.literals.sort_by(|a, b| {
        let cmp = sub_invariant_literal_cmp(a, b, &local_context, kernel_context)
            .expect("Concrete literals should always be comparable");
        cmp.reverse() // Reverse to get non-increasing order
    });

    clause.normalize_var_ids_no_flip();
    clause
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::ModuleId;

    #[test]
    fn test_clause_set_basic_generalization() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert a general clause: c0(x0, c5) or c1(x0)
        let general_clause = kctx.parse_clause("c0(x0, c5) or c1(x0)", &["Bool"]);
        clause_set.insert(general_clause, 1, &kctx);

        // Test that a specialized version is recognized (x0 -> c6)
        let special_clause = kctx.parse_clause("c1(c6) or c0(c6, c5)", &[]);
        let result = clause_set.find_generalization(special_clause, &kctx);
        assert_eq!(result, Some(1), "Should find the generalization");
    }

    #[test]
    fn test_clause_set_reordered_literals() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c1(x0) or c0(x0, c5)
        let clause = kctx.parse_clause("c1(x0) or c0(x0, c5)", &["Bool"]);
        clause_set.insert(clause, 2, &kctx);

        // Test that reordered specializations are recognized (x0 -> c6)
        let special1 = kctx.parse_clause("c0(c6, c5) or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(2));

        // Another reordering (x0 -> c7)
        let special2 = kctx.parse_clause("c1(c7) or c0(c7, c5)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(2));
    }

    #[test]
    fn test_clause_set_flipped_equality() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6", "c7"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: x0 = c5 or c1(x0)
        let clause = kctx.parse_clause("x0 = c5 or c1(x0)", &["Bool"]);
        clause_set.insert(clause, 3, &kctx);

        // Test that flipped equalities are recognized (x0 -> c6)
        let special = kctx.parse_clause("c6 = c5 or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(3));

        // Also test with the equality already flipped (x0 -> c7)
        let special2 = kctx.parse_clause("c5 = c7 or c1(c7)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(3));
    }

    #[test]
    fn test_clause_set_no_generalization() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert a specific clause: c0(c5, c6) or c1(c7)
        let clause = kctx.parse_clause("c0(c5, c6) or c1(c7)", &[]);
        clause_set.insert(clause, 4, &kctx);

        // Test clauses that should NOT have generalizations
        let no_match1 = kctx.parse_clause("c0(c5, c7) or c1(c7)", &[]);
        assert_eq!(clause_set.find_generalization(no_match1, &kctx), None);

        let no_match2 = kctx.parse_clause("c0(c6, c5) or c1(c7)", &[]);
        assert_eq!(clause_set.find_generalization(no_match2, &kctx), None);
    }

    #[test]
    fn test_clause_set_multiple_variables() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c0(x0, x1) or c0(x1, x0)
        let clause = kctx.parse_clause("c0(x0, x1) or c0(x1, x0)", &["Bool", "Bool"]);
        clause_set.insert(clause, 5, &kctx);

        // Test various specializations (x0 -> c5, x1 -> c6)
        let special1 = kctx.parse_clause("c0(c5, c6) or c0(c6, c5)", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(5));

        // Reordered (x0 -> c7, x1 -> c8)
        let special2 = kctx.parse_clause("c0(c8, c7) or c0(c7, c8)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(5));

        // This should NOT match because the variable pattern is different
        let no_match = kctx.parse_clause("c0(c5, c6) or c0(c7, c8)", &[]);
        assert_eq!(clause_set.find_generalization(no_match, &kctx), None);
    }

    #[test]
    fn test_clause_set_single_literal() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert single literal clauses
        let clause1 = kctx.parse_clause("c0(x0, c5)", &["Bool"]);
        clause_set.insert(clause1, 6, &kctx);

        let clause2 = kctx.parse_clause("x0 = c5", &["Bool"]);
        clause_set.insert(clause2, 7, &kctx);

        // Test specializations
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c0(c6, c5)", &[]), &kctx),
            Some(6)
        );
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c6 = c5", &[]), &kctx),
            Some(7)
        );
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c5 = c6", &[]), &kctx),
            Some(7)
        );
    }

    #[test]
    fn test_clause_set_negated_literals() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c5 = x0 or x1 != c6
        let clause = kctx.parse_clause("c5 = x0 or x1 != c6", &["Bool", "Bool"]);
        clause_set.insert(clause, 1, &kctx);

        // Test that it matches correct specializations
        let special1 = kctx.parse_clause("c5 = c7 or c8 != c6", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(1));

        let special2 = kctx.parse_clause("c7 != c6 or c5 = c7", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));

        let special3 = kctx.parse_clause("c5 = c8 or c6 != c8", &[]);
        assert_eq!(clause_set.find_generalization(special3, &kctx), Some(1));
    }

    #[test]
    fn test_clause_set_no_positive_negative_confusion() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert a clause with a positive literal
        let positive_clause = kctx.parse_clause("x0 = c5", &["Bool"]);
        clause_set.insert(positive_clause, 1, &kctx);

        // Insert a clause with a negative literal
        let negative_clause = kctx.parse_clause("x0 != c6", &["Bool"]);
        clause_set.insert(negative_clause, 2, &kctx);

        // Test that positive matches positive
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c7 = c5", &[]), &kctx),
            Some(1)
        );

        // Test that negative matches negative
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c8 != c6", &[]), &kctx),
            Some(2)
        );

        // Test that positive does NOT match negative
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c7 != c5", &[]), &kctx),
            None
        );

        // Test that negative does NOT match positive
        assert_eq!(
            clause_set.find_generalization(kctx.parse_clause("c8 = c6", &[]), &kctx),
            None
        );
    }

    #[test]
    fn test_clause_set_mixed_positive_negative() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: not c1(x0) or c0(x0, x1) or x1 != c5
        let clause = kctx.parse_clause("not c1(x0) or c0(x0, x1) or x1 != c5", &["Bool", "Bool"]);
        clause_set.insert(clause, 1, &kctx);

        // Test various specializations
        let special1 = kctx.parse_clause("not c1(c6) or c0(c6, c7) or c7 != c5", &[]);
        assert_eq!(clause_set.find_generalization(special1, &kctx), Some(1));

        let special2 = kctx.parse_clause("c0(c8, c9) or c9 != c5 or not c1(c8)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));

        // Test that wrong signs don't match
        let wrong1 = kctx.parse_clause("c1(c6) or c0(c6, c7) or c7 != c5", &[]);
        assert_eq!(clause_set.find_generalization(wrong1, &kctx), None);

        let wrong2 = kctx.parse_clause("not c1(c6) or not c0(c6, c7) or c7 != c5", &[]);
        assert_eq!(clause_set.find_generalization(wrong2, &kctx), None);
    }

    #[test]
    fn test_clause_set_all_negative() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c5", "c6", "c7", "c8"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: x0 != c5 or x1 != c6 or x0 != x1
        let clause = kctx.parse_clause("x0 != c5 or x1 != c6 or x0 != x1", &["Bool", "Bool"]);
        clause_set.insert(clause, 1, &kctx);

        let special = kctx.parse_clause("c7 != c5 or c8 != c6 or c7 != c8", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(1));

        let special2 = kctx.parse_clause("c7 != c8 or c7 != c5 or c8 != c6", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));
    }

    #[test]
    fn test_clause_set_boolean_negation() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6", "c7"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: not c0(x0, c5) or c1(x0)
        let clause = kctx.parse_clause("not c0(x0, c5) or c1(x0)", &["Bool"]);
        clause_set.insert(clause, 1, &kctx);

        let special = kctx.parse_clause("not c0(c6, c5) or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(1));

        let special2 = kctx.parse_clause("c1(c7) or not c0(c7, c5)", &[]);
        assert_eq!(clause_set.find_generalization(special2, &kctx), Some(1));

        // Test that signs matter
        let wrong = kctx.parse_clause("c0(c6, c5) or c1(c6)", &[]);
        assert_eq!(clause_set.find_generalization(wrong, &kctx), None);
    }

    #[test]
    fn test_clause_set_compound_generalization() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c5", "c6", "c7"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert: c0(c5, x0) = x0
        let general = kctx.parse_clause("c0(c5, x0) = x0", &["Bool"]);
        clause_set.insert(general, 1, &kctx);

        // Specialization: c0(c5, c0(c6, c7)) = c0(c6, c7)
        let special = kctx.parse_clause("c0(c5, c0(c6, c7)) = c0(c6, c7)", &[]);
        assert_eq!(clause_set.find_generalization(special, &kctx), Some(1));
    }

    #[test]
    fn test_clause_set_with_applied_variable() {
        // Test GeneralizationSet with applied variables (variables in function position).
        // Pattern: not x0(c5) or x0(x1) where x0: Bool -> Bool, x1: Bool
        // Query: not c1(c5) or c1(c6) where c1: Bool -> Bool
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool") // placeholder
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4", "c5", "c6"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // x0: Bool -> Bool, x1: Bool
        let pattern = kctx.parse_clause("not x0(c5) or x0(x1)", &["Bool -> Bool", "Bool"]);
        clause_set.insert(pattern, 42, &kctx);

        let query = kctx.parse_clause("not c1(c5) or c1(c6)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(found, Some(42), "Should match clause with applied variable");
    }

    #[test]
    fn test_clause_set_with_higher_order_function() {
        // Test with higher-order function type (Bool -> Bool, Bool) -> Bool
        // Pattern: not f(x0, x1) or x0(x1) where f: (Bool -> Bool, Bool) -> Bool
        // Query: not f(c1, c5) or c1(c5)
        let mut kctx = KernelContext::new();
        // c0: (Bool -> Bool, Bool) -> Bool (higher order function)
        kctx.parse_constant("c0", "(Bool -> Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c2", "c3", "c4", "c5", "c6"], "Bool");

        let mut clause_set = GeneralizationSet::new();

        // x0: Bool -> Bool, x1: Bool
        let pattern = kctx.parse_clause("not c0(x0, x1) or x0(x1)", &["Bool -> Bool", "Bool"]);
        clause_set.insert(pattern, 42, &kctx);

        let query = kctx.parse_clause("not c0(c1, c5) or c1(c5)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(42),
            "Should match pattern with higher-order function"
        );
    }

    #[test]
    fn test_clause_set_rejects_sign_mismatch() {
        // Test that signs are properly checked
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool -> Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constant("c5", "Bool");

        let mut clause_set = GeneralizationSet::new();

        // Insert pattern with POSITIVE first literal, x0: Bool -> Bool, x1: Bool
        let pattern = kctx.parse_clause("c0(x0, x1) or x0(x1)", &["Bool -> Bool", "Bool"]);
        clause_set.insert(pattern, 42, &kctx);

        // Query with NEGATIVE first literal
        let query = kctx.parse_clause("not c0(c1, c5) or c1(c5)", &[]);
        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(found, None, "Should NOT match when signs are different");
    }

    /// This test covers a case with curried function applications.
    /// The pattern has a variable f: (Bool, Bool) -> Bool that gets applied to
    /// s(f) twice (where s: ((Bool, Bool) -> Bool) -> Bool), like f(s(f), s(f)).
    ///
    /// The query substitutes f with a curried application g(a) where:
    /// - g: A -> (Bool, Bool) -> Bool
    /// - a: A (some constant type)
    ///
    /// This tests that the pattern tree correctly matches:
    ///   pattern: f(s(f), s(f)) or r(f)
    ///   query:   g(a)(s(g(a)), s(g(a))) or r(g(a))
    ///
    /// Both are curried in term representation, so:
    ///   pattern: (f(s(f)))(s(f)) or r(f)
    ///   query:   ((g(a))(s(g(a))))(s(g(a))) or r(g(a))
    #[test]
    fn test_clause_set_curried_function_substitution() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;

        let mut kctx = KernelContext::new();
        // A is a constant type to simulate a type parameter
        kctx.parse_datatype("A")
            // g0 takes A and returns a binary Bool function (like lte_from with type param)
            .parse_constant("g0", "A -> (Bool, Bool) -> Bool")
            // s0 is a selector: given a binary function, returns a Bool (like Synthetic)
            .parse_constant("s0", "((Bool, Bool) -> Bool) -> Bool")
            // c0 is a predicate on binary functions (like is_reflexive)
            .parse_constant("c0", "((Bool, Bool) -> Bool) -> Bool")
            // c1 is a constant of type A (like the type argument)
            .parse_constant("c1", "A");

        let mut clause_set = GeneralizationSet::new();

        // Pattern: not f(s0(f), s0(f)) or c0(f)
        // where f: (Bool, Bool) -> Bool (variable x0)
        let pattern = kctx.parse_clause(
            "not x0(s0(x0), s0(x0)) or c0(x0)",
            &["(Bool, Bool) -> Bool"],
        );
        clause_set.insert(pattern.clone(), 99, &kctx);

        // Build query manually: not g0(c1)(s0(g0(c1)), s0(g0(c1))) or c0(g0(c1))
        // Symbols: g0 = GlobalConstant(0), s0 = Synthetic(0), c0 = ScopedConstant(0), c1 = ScopedConstant(1)
        let g0_atom = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0));
        let s0_atom = Atom::Symbol(Symbol::Synthetic(ModuleId(0), 0));
        let c0_atom = Atom::Symbol(Symbol::ScopedConstant(0));
        let c1_atom = Atom::Symbol(Symbol::ScopedConstant(1));
        let c1_term = Term::atom(c1_atom);

        // g0(c1) - a function (Bool, Bool) -> Bool
        let g0_c1 = Term::new(g0_atom, vec![c1_term.clone()]);

        // s0(g0(c1)) - a Bool
        let s0_g0_c1 = Term::new(s0_atom, vec![g0_c1.clone()]);

        // g0(c1)(s0(g0(c1)), s0(g0(c1))) = g0(c1, s0(g0(c1)), s0(g0(c1))) in curried form
        // This is g0 applied to c1, then to s0(g0(c1)), then to s0(g0(c1))
        let g0_c1_s0_s0 = Term::new(
            g0_atom,
            vec![c1_term.clone(), s0_g0_c1.clone(), s0_g0_c1.clone()],
        );

        // c0(g0(c1))
        let c0_g0_c1 = Term::new(c0_atom, vec![g0_c1.clone()]);

        // Build the literals:
        // Literal 1: not g0(c1, s0(g0(c1)), s0(g0(c1))) = true
        let lit1 = Literal {
            positive: false,
            left: g0_c1_s0_s0,
            right: Term::new_true(),
        };

        // Literal 2: c0(g0(c1)) = true
        let lit2 = Literal {
            positive: true,
            left: c0_g0_c1,
            right: Term::new_true(),
        };

        let query = Clause::from_literals_unnormalized(vec![lit1, lit2], &LocalContext::empty());

        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(99),
            "Should match pattern when f is substituted with curried application g0(c1)"
        );
    }

    /// Similar to the above test, but now the function takes TWO curried applications
    /// before becoming a binary function. lte_from(Type)(lt) has two applications.
    ///
    /// Pattern: not f(s0(f), s0(f)) or c0(f)
    /// Query: not g0(Type)(c1)(s0(g0(Type)(c1)), s0(g0(Type)(c1))) or c0(g0(Type)(c1))
    ///
    /// Where Type is an actual Type symbol.
    #[test]
    fn test_clause_set_with_type_symbol_argument() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::kernel::types::GroundTypeId;

        let mut kctx = KernelContext::new();
        // T is a type (like a type parameter bound in the environment)
        kctx.parse_datatype("T")
            // g0 takes a Type, then another arg of that type, and returns (T, T) -> Bool
            // This simulates: forall T. A -> (T, T) -> Bool
            .parse_constant("g0", "T -> T -> (T, T) -> Bool")
            // s0 is a selector: given a binary function, returns a T
            .parse_constant("s0", "((T, T) -> Bool) -> T")
            // c0 is a predicate on binary functions (like is_reflexive)
            .parse_constant("c0", "((T, T) -> Bool) -> Bool")
            // c1 is a constant of type T
            .parse_constant("c1", "T");

        let mut clause_set = GeneralizationSet::new();

        // Pattern: not f(s0(f), s0(f)) or c0(f)
        // where f: (T, T) -> Bool (variable x0)
        let pattern = kctx.parse_clause("not x0(s0(x0), s0(x0)) or c0(x0)", &["(T, T) -> Bool"]);
        clause_set.insert(pattern.clone(), 99, &kctx);

        // Build query: not g0(Type)(c1)(s0(...), s0(...)) or c0(g0(Type)(c1))
        // g0 = GlobalConstant(0), s0 = Synthetic(0), c0 = ScopedConstant(0), c1 = ScopedConstant(1)
        // Type = Type(GroundTypeId(0)) which is the type T
        let g0_atom = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0));
        let s0_atom = Atom::Symbol(Symbol::Synthetic(ModuleId(0), 0));
        let c0_atom = Atom::Symbol(Symbol::ScopedConstant(0));
        let c1_atom = Atom::Symbol(Symbol::ScopedConstant(1));
        let type_atom = Atom::Symbol(Symbol::Type(GroundTypeId::test(0))); // T as a type symbol

        let type_term = Term::atom(type_atom);
        let c1_term = Term::atom(c1_atom);

        // g0(Type)(c1) = g0(Type, c1) - a function (T, T) -> Bool
        // This mirrors lte_from(Type)(lt)
        let g0_type_c1 = Term::new(g0_atom, vec![type_term.clone(), c1_term.clone()]);

        // s0(g0(Type)(c1)) - a T
        let s0_g0_type_c1 = Term::new(s0_atom, vec![g0_type_c1.clone()]);

        // g0(Type)(c1)(s0(...), s0(...)) = g0(Type, c1, s0(...), s0(...))
        let g0_type_c1_s0_s0 = Term::new(
            g0_atom,
            vec![
                type_term.clone(),
                c1_term.clone(),
                s0_g0_type_c1.clone(),
                s0_g0_type_c1.clone(),
            ],
        );

        // c0(g0(Type)(c1))
        let c0_g0_type_c1 = Term::new(c0_atom, vec![g0_type_c1.clone()]);

        // Build the literals:
        let lit1 = Literal {
            positive: false,
            left: g0_type_c1_s0_s0,
            right: Term::new_true(),
        };

        let lit2 = Literal {
            positive: true,
            left: c0_g0_type_c1,
            right: Term::new_true(),
        };

        let query = Clause::from_literals_unnormalized(vec![lit1, lit2], &LocalContext::empty());

        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(99),
            "Should match pattern when f is substituted with g0(Type)(c1)"
        );
    }

    /// This test matches a scenario with type arguments:
    /// - The predicate (is_reflexive) takes a Type argument as well
    /// - Pattern: not f(s0(f), s0(f)) or g1(Type)(f)
    /// - Query: not g0(Type)(c1)(s0(...), s0(...)) or g1(Type)(g0(Type)(c1))
    #[test]
    fn test_clause_set_predicate_with_type_arg() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::kernel::types::GroundTypeId;

        let mut kctx = KernelContext::new();
        // T is a type (like a type parameter bound in the environment)
        kctx.parse_datatype("T")
            // g0 (lte_from): Type -> T -> (T, T) -> Bool
            .parse_constant("g0", "T -> T -> (T, T) -> Bool")
            // g1 (is_reflexive): Type -> ((T, T) -> Bool) -> Bool
            .parse_constant("g1", "T -> ((T, T) -> Bool) -> Bool")
            // s0: ((T, T) -> Bool) -> T
            .parse_constant("s0", "((T, T) -> Bool) -> T")
            // c1 is lt: T -> T -> Bool (after type application, it's (T, T) -> Bool)
            .parse_constant("c1", "T -> T -> Bool");

        let mut clause_set = GeneralizationSet::new();

        // Pattern: not f(s0(f), s0(f)) or g1(Type)(f)
        // where f: (T, T) -> Bool (variable x0)
        // But we need the pattern to be g1(Type)(x0), not just g1(x0)
        // We'll need to construct this manually
        let type_atom = Atom::Symbol(Symbol::Type(GroundTypeId::test(0)));
        let type_term = Term::atom(type_atom);
        let g1_atom = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1));
        let s0_atom = Atom::Symbol(Symbol::Synthetic(ModuleId(0), 0));
        let x0_term = Term::new_variable(0);

        // First literal: not x0(s0(x0), s0(x0))
        let s0_x0 = Term::new(s0_atom, vec![x0_term.clone()]);
        let x0_s0_s0 = x0_term.apply(&[s0_x0.clone(), s0_x0.clone()]);
        let lit1_pattern = Literal {
            positive: false,
            left: x0_s0_s0,
            right: Term::new_true(),
        };

        // Second literal: g1(Type)(x0) = g1(Type, x0)
        let g1_type_x0 = Term::new(g1_atom, vec![type_term.clone(), x0_term.clone()]);
        let lit2_pattern = Literal {
            positive: true,
            left: g1_type_x0,
            right: Term::new_true(),
        };

        // The variable type for x0
        let var_type = kctx.parse_type("(T, T) -> Bool");
        let pattern_context = LocalContext::from_types(vec![var_type]);
        let pattern =
            Clause::from_literals_unnormalized(vec![lit1_pattern, lit2_pattern], &pattern_context);
        clause_set.insert(pattern.clone(), 99, &kctx);

        // Build query: not g0(Type)(c1)(s0(...), s0(...)) or g1(Type)(g0(Type)(c1))
        let g0_atom = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0));
        let c1_atom = Atom::Symbol(Symbol::ScopedConstant(1));
        let c1_term = Term::atom(c1_atom);

        // g0(Type)(c1) = g0(Type, c1)
        let g0_type_c1 = Term::new(g0_atom, vec![type_term.clone(), c1_term.clone()]);

        // s0(g0(Type)(c1))
        let s0_g0 = Term::new(s0_atom, vec![g0_type_c1.clone()]);

        // g0(Type, c1, s0(...), s0(...))
        let g0_type_c1_s0_s0 = Term::new(
            g0_atom,
            vec![
                type_term.clone(),
                c1_term.clone(),
                s0_g0.clone(),
                s0_g0.clone(),
            ],
        );

        // g1(Type, g0(Type, c1))
        let g1_type_g0 = Term::new(g1_atom, vec![type_term.clone(), g0_type_c1.clone()]);

        let lit1_query = Literal {
            positive: false,
            left: g0_type_c1_s0_s0,
            right: Term::new_true(),
        };

        let lit2_query = Literal {
            positive: true,
            left: g1_type_g0,
            right: Term::new_true(),
        };

        let query = Clause::from_literals_unnormalized(
            vec![lit1_query, lit2_query],
            &LocalContext::empty(),
        );

        let found = clause_set.find_generalization(query, &kctx);
        assert_eq!(
            found,
            Some(99),
            "Should match pattern with g1(Type)(f) against g1(Type)(g0(Type)(c1))"
        );
    }

    /// This test reproduces the exact failing case from complex.ac line 157.
    ///
    /// The pattern (mul_three_re theorem) is:
    /// g217(g92(T7, g92(T7, x0, x1), x2)) = g90(T6, g90(T6, g90(T6, g92(T6, g92(T6, g217(x0), g217(x1)), g217(x2)), ...), ...), ...)
    ///
    /// The query is the same but with c1, c2, c3 instead of x0, x1, x2.
    ///
    /// Symbols:
    /// - g90 = GlobalConstant(90) - some combining function (like add)
    /// - g92 = GlobalConstant(92) - another combining function (like mul)
    /// - g217 = GlobalConstant(217) - a selector (like .re)
    /// - g218 = GlobalConstant(218) - another selector (like .im)
    /// - T6 = Type(GroundTypeId(6)) - Real type
    /// - T7 = Type(GroundTypeId(7)) - Complex type
    #[test]
    fn test_exact_mul_three_re_failure() {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::kernel::types::GroundTypeId;

        // Create a kernel context with the types we need
        let mut kctx = KernelContext::new();
        // Add datatypes to get the GroundTypeIds we need (0-7)
        // We need T6 (Real) and T7 (Complex)
        kctx.parse_datatype("T0"); // GroundTypeId(0)
        kctx.parse_datatype("T1"); // GroundTypeId(1)
        kctx.parse_datatype("T2"); // GroundTypeId(2)
        kctx.parse_datatype("T3"); // GroundTypeId(3)
        kctx.parse_datatype("T4"); // GroundTypeId(4)
        kctx.parse_datatype("T5"); // GroundTypeId(5)
        kctx.parse_datatype("T6"); // GroundTypeId(6) - Real
        kctx.parse_datatype("T7"); // GroundTypeId(7) - Complex

        // Build the types manually using Term::pi() and Term::type_sort()
        // The actual types from the failing case:
        // GlobalConstant(90): (Type -> (b0 -> (b1 -> b2))) where b0 is the bound type
        // GlobalConstant(92): (Type -> (b0 -> (b1 -> b2)))
        // GlobalConstant(217): (T7 -> T6)
        // GlobalConstant(218): (T7 -> T6)

        let type_sort = Term::type_sort();
        let t6_type = Term::ground_type(GroundTypeId::test(6));
        let t7_type = Term::ground_type(GroundTypeId::test(7));

        // For polymorphic types: Type -> (T -> (T -> T))
        // With De Bruijn indices, references to the outer Type binding must be shifted
        // as we go deeper into nested Pis:
        // - At depth 1 (first arg): BoundVar(0) refers to Type
        // - At depth 2 (second arg): BoundVar(1) refers to Type (shifted by 1)
        // - At depth 3 (output): BoundVar(2) refers to Type (shifted by 2)
        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));
        let b2 = Term::atom(Atom::BoundVariable(2));

        // g90/g92 type: Pi(Type, Pi(b0, Pi(b1, b2)))
        // This is Type -> T -> T -> T where T is the type argument
        let polymorphic_binary_type = Term::pi(
            type_sort.clone(),
            Term::pi(b0.clone(), Term::pi(b1.clone(), b2.clone())),
        );

        // g217/g218 type: T7 -> T6
        let selector_type = Term::pi(t7_type.clone(), t6_type.clone());

        // Add global constants with proper types
        // g0 = polymorphic add (like g90)
        kctx.symbol_table
            .add_global_constant(polymorphic_binary_type.clone());
        // g1 = polymorphic mul (like g92)
        kctx.symbol_table
            .add_global_constant(polymorphic_binary_type.clone());
        // g2 = re selector (like g217)
        kctx.symbol_table.add_global_constant(selector_type.clone());
        // g3 = im selector (like g218)
        kctx.symbol_table.add_global_constant(selector_type.clone());

        // Add scoped constants c0, c1, c2 of type T7
        kctx.symbol_table.add_scoped_constant(t7_type.clone());
        kctx.symbol_table.add_scoped_constant(t7_type.clone());
        kctx.symbol_table.add_scoped_constant(t7_type.clone());

        let mut clause_set = GeneralizationSet::new();

        // Atoms using GlobalConstant indices from above
        let g90 = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)); // add_r (like g90)
        let g92 = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1)); // mul_c (like g92)
        let g217 = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 2)); // re (like g217)
        let g218 = Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 3)); // im (like g218)

        // Type symbols used as term arguments (T6=Real, T7=Complex)
        let t6 = Term::atom(Atom::Symbol(Symbol::Type(GroundTypeId::test(6))));
        let t7 = Term::atom(Atom::Symbol(Symbol::Type(GroundTypeId::test(7))));

        // Variables
        let x0 = Term::new_variable(0);
        let x1 = Term::new_variable(1);
        let x2 = Term::new_variable(2);

        // Constants for the query
        let c1 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        let c2 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(1)));
        let c3 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(2)));

        // Helper to build g92(T6, a, b)
        let mk_g92_t6 =
            |a: Term, b: Term| -> Term { Term::new(g92.clone(), vec![t6.clone(), a, b]) };

        // Helper to build g92(T7, a, b)
        let mk_g92_t7 =
            |a: Term, b: Term| -> Term { Term::new(g92.clone(), vec![t7.clone(), a, b]) };

        // Helper to build g90(T6, a, b)
        let mk_g90_t6 =
            |a: Term, b: Term| -> Term { Term::new(g90.clone(), vec![t6.clone(), a, b]) };

        // Helper to build g217(a)
        let mk_g217 = |a: Term| -> Term { Term::new(g217.clone(), vec![a]) };

        // Helper to build g218(a)
        let mk_g218 = |a: Term| -> Term { Term::new(g218.clone(), vec![a]) };

        // Build the pattern RHS (the big g90 expression):
        // g90(T6, g90(T6, g90(T6,
        //   g92(T6, g92(T6, g217(x0), g217(x1)), g217(x2)),
        //   g92(T6, g92(T6, g217(x0), g218(x1)), g218(x2))),
        //   g92(T6, g92(T6, g218(x0), g217(x1)), g218(x2))),
        //   g92(T6, g92(T6, g218(x0), g218(x1)), g217(x2)))

        // Innermost terms for pattern
        let p_part1 = mk_g92_t6(
            mk_g92_t6(mk_g217(x0.clone()), mk_g217(x1.clone())),
            mk_g217(x2.clone()),
        );
        let p_part2 = mk_g92_t6(
            mk_g92_t6(mk_g217(x0.clone()), mk_g218(x1.clone())),
            mk_g218(x2.clone()),
        );
        let p_part3 = mk_g92_t6(
            mk_g92_t6(mk_g218(x0.clone()), mk_g217(x1.clone())),
            mk_g218(x2.clone()),
        );
        let p_part4 = mk_g92_t6(
            mk_g92_t6(mk_g218(x0.clone()), mk_g218(x1.clone())),
            mk_g217(x2.clone()),
        );

        let p_rhs = mk_g90_t6(mk_g90_t6(mk_g90_t6(p_part1, p_part2), p_part3), p_part4);

        // Pattern LHS: g217(g92(T7, g92(T7, x0, x1), x2))
        let p_lhs = mk_g217(mk_g92_t7(mk_g92_t7(x0.clone(), x1.clone()), x2.clone()));

        // Create pattern clause with variables of type T7 (Complex)
        let complex_type = Term::atom(Atom::Symbol(Symbol::Type(GroundTypeId::test(7))));
        let local_ctx = LocalContext::from_types(vec![
            complex_type.clone(),
            complex_type.clone(),
            complex_type.clone(),
        ]);
        let pattern_lit = Literal::new(true, p_lhs.clone(), p_rhs.clone());
        let pattern_clause = Clause::new(vec![pattern_lit], &local_ctx);

        clause_set.insert(pattern_clause, 42, &kctx);

        // Now build the query with constants c1, c2, c3
        let q_part1 = mk_g92_t6(
            mk_g92_t6(mk_g217(c1.clone()), mk_g217(c2.clone())),
            mk_g217(c3.clone()),
        );
        let q_part2 = mk_g92_t6(
            mk_g92_t6(mk_g217(c1.clone()), mk_g218(c2.clone())),
            mk_g218(c3.clone()),
        );
        let q_part3 = mk_g92_t6(
            mk_g92_t6(mk_g218(c1.clone()), mk_g217(c2.clone())),
            mk_g218(c3.clone()),
        );
        let q_part4 = mk_g92_t6(
            mk_g92_t6(mk_g218(c1.clone()), mk_g218(c2.clone())),
            mk_g217(c3.clone()),
        );

        let q_rhs = mk_g90_t6(mk_g90_t6(mk_g90_t6(q_part1, q_part2), q_part3), q_part4);

        // Query LHS: g217(g92(T7, g92(T7, c1, c2), c3))
        let q_lhs = mk_g217(mk_g92_t7(mk_g92_t7(c1.clone(), c2.clone()), c3.clone()));

        let query_lit = Literal::new(true, q_lhs.clone(), q_rhs.clone());
        let query_clause = Clause::new(vec![query_lit], &LocalContext::empty());

        let found = clause_set.find_generalization(query_clause, &kctx);
        assert_eq!(
            found,
            Some(42),
            "Should match pattern with x0->c1, x1->c2, x2->c3"
        );
    }

    /// Test that type variables in patterns don't break generalization matching.
    ///
    /// This test captures a bug where type-aware variable normalization causes
    /// pattern matching to fail. The issue is:
    ///
    /// Pattern: `x1 != x2 or g0(x0, x1, x2)` where x0: Type, x1: x0, x2: x0
    /// Query: `c1 != c1 or g0(T0, c1, c1)` where c1: T0
    ///
    /// The structural order puts x1 first (in the inequality), but type-aware
    /// normalization puts x0 first (since x1's type depends on x0), causing
    /// x1 to get renumbered to Variable(1) instead of Variable(0).
    ///
    /// The PDT matching algorithm expects Variable(0) at the first term position,
    /// so the match fails.
    #[test]
    fn test_type_variable_ordering() {
        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T0" to avoid conflict with type variable naming convention
        // ("T0" would be parsed as FreeVariable(0) in type positions)
        kctx.parse_datatype("Foo");

        // g0: Type -> T -> T -> Bool (polymorphic predicate)
        kctx.parse_polymorphic_constant("g0", "T: Type", "(T, T) -> Bool");

        // c1, c2: Foo (concrete values)
        kctx.parse_constant("c1", "Foo");
        kctx.parse_constant("c2", "Foo");

        let mut clause_set = GeneralizationSet::new();

        // Pattern clause: x1 != x2 or g0(x0, x1, x2)
        // where x0: Type, x1: x0, x2: x0
        //
        // Structurally, x1 appears first (in the inequality left side).
        // But type-aware normalization will renumber x0 first since x1's type is x0.
        let pattern_clause = kctx.parse_clause("x1 != x2 or g0(x0, x1, x2)", &["Type", "x0", "x0"]);
        clause_set.insert(pattern_clause, 42, &kctx);

        // Query clause: c1 != c2 or g0(Foo, c1, c2)
        let query_clause = kctx.parse_clause("c1 != c2 or g0(Foo, c1, c2)", &[]);

        // This should match! The pattern generalizes the query with:
        // x0 -> T0, x1 -> c1, x2 -> c2
        let found = clause_set.find_generalization(query_clause, &kctx);
        assert_eq!(
            found,
            Some(42),
            "Pattern with type variable should match concrete query"
        );
    }

    /// Test that typeclass-constrained variables (like R: Ring) get higher IDs
    /// than value variables, similar to type variables (T: Type).
    ///
    /// This is the same scenario as test_type_variable_ordering but with
    /// a typeclass constraint instead of Type.
    #[test]
    fn test_typeclass_variable_ordering() {
        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Int");
        kctx.parse_typeclass("Ring");
        kctx.parse_instance("Int", "Ring");

        // g0: Ring -> R -> R -> Bool (polymorphic predicate with typeclass constraint)
        kctx.parse_polymorphic_constant("g0", "R: Ring", "(R, R) -> Bool");

        // c1, c2: Int (concrete values)
        kctx.parse_constant("c1", "Int");
        kctx.parse_constant("c2", "Int");

        let mut clause_set = GeneralizationSet::new();

        // Pattern clause: x1 != x2 or g0(x0, x1, x2)
        // where x0: Ring, x1: x0, x2: x0
        //
        // Structurally, x1 appears first (in the inequality left side).
        // But type-aware normalization would renumber x0 first since x1's type is x0.
        let pattern_clause = kctx.parse_clause("x1 != x2 or g0(x0, x1, x2)", &["Ring", "x0", "x0"]);
        clause_set.insert(pattern_clause, 42, &kctx);

        // Query clause: c1 != c2 or g0(Int, c1, c2)
        let query_clause = kctx.parse_clause("c1 != c2 or g0(Int, c1, c2)", &[]);

        // This should match! The pattern generalizes the query with:
        // x0 -> Int, x1 -> c1, x2 -> c2
        let found = clause_set.find_generalization(query_clause, &kctx);
        assert_eq!(
            found,
            Some(42),
            "Pattern with typeclass variable should match concrete query"
        );
    }
}
