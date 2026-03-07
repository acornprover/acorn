//! Core inference rules used in theorem proving:
//! - Equality Resolution (ER)
//! - Equality Factoring (EF)

use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::unifier::{Scope, Unifier};
use crate::kernel::variable_map::VariableMap;

fn is_boolean_equality(
    literal: &Literal,
    context: &LocalContext,
    kernel_context: &KernelContext,
) -> bool {
    literal.left.get_type_with_context(context, kernel_context)
        == crate::kernel::term::Term::bool_type()
}

/// Finds all possible equality resolutions for a clause.
///
/// Equality resolution applies when a clause contains a negative literal `s != t`
/// where `s` and `t` can be unified. The literal is then removed from the clause.
///
/// Returns a vector of (literals, output_context, input_var_map) tuples.
/// The literals are the result after removing the resolved literal and applying the unifier.
/// The output_context contains types for variables in the resulting literals.
/// The input_var_map maps input clause variables to output terms.
pub fn find_equality_resolutions(
    clause: &Clause,
    kernel_context: &KernelContext,
) -> Vec<(Vec<Literal>, LocalContext, VariableMap)> {
    let mut results = vec![];

    for i in 0..clause.literals.len() {
        let literal = &clause.literals[i];
        if literal.positive {
            // Negative literals come before positive ones, so we're done
            break;
        }

        // The variables are in the same scope, which we will call "left".
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, clause.get_local_context());
        if !unifier.unify(Scope::LEFT, &literal.left, Scope::LEFT, &literal.right) {
            continue;
        }

        // We can do equality resolution
        let mut new_literals = vec![];
        for (j, lit) in clause.literals.iter().enumerate() {
            if j != i {
                let (new_lit, _) = unifier.apply_to_literal(Scope::LEFT, lit);
                new_literals.push(new_lit);
            }
        }

        // Get the output context and variable map from the unifier
        let (all_maps, output_context) = unifier.into_maps_with_context();
        let mut input_var_map = VariableMap::new();
        for (scope, map) in all_maps {
            if scope == Scope::LEFT {
                input_var_map = map;
            }
        }

        results.push((new_literals, output_context, input_var_map));
    }

    results
}

/// Generates all clauses that can be derived from a clause using equality resolution.
/// This is a convenience function that returns just the normalized clauses.
pub fn equality_resolutions(clause: &Clause, kernel_context: &KernelContext) -> Vec<Clause> {
    find_equality_resolutions(clause, kernel_context)
        .into_iter()
        .map(|(literals, context, _)| Clause::new(literals, &context))
        .filter(|c| !c.is_tautology())
        .collect()
}

/// Finds all possible equality factorings for a clause.
///
/// Equality factoring applies when a clause has two positive literals that can
/// be partially unified. It creates a new clause with an additional negative literal.
///
/// Returns a vector of (literals, output_context, input_var_map) tuples.
/// The literals are the result of factoring before normalization.
/// The output_context contains types for variables in the resulting literals.
/// The input_var_map maps input clause variables to output terms.
pub fn find_equality_factorings(
    clause: &Clause,
    kernel_context: &KernelContext,
) -> Vec<(Vec<Literal>, LocalContext, VariableMap)> {
    let mut results = vec![];

    // The first literal must be positive for equality factoring
    if clause.literals.is_empty() || !clause.literals[0].positive {
        return results;
    }

    let st_literal = &clause.literals[0];
    if is_boolean_equality(st_literal, clause.get_local_context(), kernel_context) {
        return results;
    }

    for (_, s, t) in st_literal.both_term_pairs() {
        for i in 1..clause.literals.len() {
            let uv_literal = &clause.literals[i];
            if !uv_literal.positive {
                continue;
            }
            if is_boolean_equality(uv_literal, clause.get_local_context(), kernel_context) {
                continue;
            }

            for (_, u, v) in uv_literal.both_term_pairs() {
                let mut unifier = Unifier::new(3, kernel_context);
                unifier.set_input_context(Scope::LEFT, clause.get_local_context());
                if !unifier.unify(Scope::LEFT, s, Scope::LEFT, u) {
                    continue;
                }

                // Create the factored terms.
                let mut literals = vec![];
                let (tv_lit, _) = Literal::new_with_flip(
                    false,
                    unifier.apply(Scope::LEFT, t),
                    unifier.apply(Scope::LEFT, v),
                );
                let (uv_out, _) = Literal::new_with_flip(
                    true,
                    unifier.apply(Scope::LEFT, u),
                    unifier.apply(Scope::LEFT, v),
                );

                literals.push(tv_lit);
                literals.push(uv_out);

                for j in 1..clause.literals.len() {
                    if i != j {
                        let (new_lit, _) =
                            unifier.apply_to_literal(Scope::LEFT, &clause.literals[j]);
                        literals.push(new_lit);
                    }
                }

                // Get the output context and variable map from the unifier
                let (all_maps, output_context) = unifier.into_maps_with_context();
                let mut input_var_map = VariableMap::new();
                for (scope, map) in all_maps {
                    if scope == Scope::LEFT {
                        input_var_map = map;
                    }
                }

                results.push((literals, output_context, input_var_map));
            }
        }
    }

    results
}

/// Generates all clauses that can be derived from a clause using equality factoring.
/// This is a convenience function that returns just the normalized clauses.
pub fn equality_factorings(clause: &Clause, kernel_context: &KernelContext) -> Vec<Clause> {
    find_equality_factorings(clause, kernel_context)
        .into_iter()
        .map(|(literals, output_context, _)| Clause::new(literals, &output_context))
        .filter(|c| !c.is_tautology())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::kernel_context::KernelContext;

    #[test]
    fn test_equality_factoring_skips_boolean_literals() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");

        let clause = context.parse_clause("c0 or c1", &[]);
        assert!(equality_factorings(&clause, &context).is_empty());
    }

    #[test]
    fn test_equality_factoring_still_works_on_non_boolean_equalities() {
        let mut context = KernelContext::new();
        context.parse_datatype("Foo");
        context.parse_constants(&["c0", "c1", "c2"], "Foo");

        let clause = context.parse_clause("c0 = c1 or c0 = c2", &[]);
        assert!(!equality_factorings(&clause, &context).is_empty());
    }
}
