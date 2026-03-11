//! Kernel term normalization is the base normalization layer for semantic terms.
//!
//! The normalization model has three distinct operations:
//!
//! 1. Term normalization
//!    This module owns the recursive, structure-preserving normalization of [`Term`]s.
//!    It must normalize every subterm of a normalized term.
//! 2. Theorem lowering
//!    This is a stronger top-level transformation that opens leading universal binders
//!    and lowers clause-shaped propositions to clauses. It does not belong in this file.
//! 3. Clause normalization
//!    This normalizes already-open clauses, including literal ordering, deduplication,
//!    and best-effort free-variable renumbering. It builds on term normalization but
//!    does not belong in this file.
//!
//! The global normalization requirements are:
//!
//! - Every `ProofStep` must have its clause normalized.
//! - In a normalized term or clause, every subterm must also be normalized.
//! - For certificates, serializing a `(clause, var_map)` pair and then deserializing it
//!   must recover the exact same `(clause, var_map)` pair.
//! - Normalization canonicalizes the built-in commutative operators `=`, `and`, and `or`
//!   up to commutativity only.
//! - Clause normalization may deterministically renumber free variables to a preferred
//!   numbering, but this is best-effort only.
//! - Normalization must be idempotent.
//!
//! This file is the source of truth for the term-normalization part of that contract.
use crate::kernel::atom::Atom;
use crate::kernel::clause::Clause;
use crate::kernel::literal::Literal;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term, TermRef};

fn split_symbol_application(term: &Term, symbol: Symbol, arity: usize) -> Option<Vec<Term>> {
    let (head, args) = term.as_ref().split_application_multi()?;
    if args.len() != arity {
        return None;
    }
    match head.get_head_atom() {
        Atom::Symbol(s) if *s == symbol => Some(args),
        _ => None,
    }
}

fn normalize_term_children(term: &Term) -> Term {
    match term.as_ref().decompose() {
        Decomposition::Atom(_) => term.clone(),
        Decomposition::Application(function, argument) => {
            let function = normalize_term(&function.to_owned());
            let argument = normalize_term(&argument.to_owned());
            function.apply(&[argument])
        }
        Decomposition::Pi(input, output) => {
            let input = normalize_term(&input.to_owned());
            let output = normalize_term(&output.to_owned());
            Term::pi(input, output)
        }
        Decomposition::Lambda(input, body) => {
            let input = normalize_term(&input.to_owned());
            let body = normalize_term(&body.to_owned());
            Term::lambda(input, body)
        }
        Decomposition::ForAll(binder_type, body) => {
            let binder_type = normalize_term(&binder_type.to_owned());
            let body = normalize_term(&body.to_owned());
            Term::forall(binder_type, body)
        }
        Decomposition::Exists(binder_type, body) => {
            let binder_type = normalize_term(&binder_type.to_owned());
            let body = normalize_term(&body.to_owned());
            Term::exists(binder_type, body)
        }
    }
}

fn beta_reduce_term_children(term: &Term) -> Term {
    match term.as_ref().decompose() {
        Decomposition::Atom(_) => term.clone(),
        Decomposition::Application(function, argument) => {
            let function = beta_reduce_subterms(&function.to_owned());
            let argument = beta_reduce_subterms(&argument.to_owned());
            function.apply(&[argument])
        }
        Decomposition::Pi(input, output) => {
            let input = beta_reduce_subterms(&input.to_owned());
            let output = beta_reduce_subterms(&output.to_owned());
            Term::pi(input, output)
        }
        Decomposition::Lambda(input, body) => {
            let input = beta_reduce_subterms(&input.to_owned());
            let body = beta_reduce_subterms(&body.to_owned());
            Term::lambda(input, body)
        }
        Decomposition::ForAll(binder_type, body) => {
            let binder_type = beta_reduce_subterms(&binder_type.to_owned());
            let body = beta_reduce_subterms(&body.to_owned());
            Term::forall(binder_type, body)
        }
        Decomposition::Exists(binder_type, body) => {
            let binder_type = beta_reduce_subterms(&binder_type.to_owned());
            let body = beta_reduce_subterms(&body.to_owned());
            Term::exists(binder_type, body)
        }
    }
}

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
            let function = substitute_bound_capture_avoiding(function, index, replacement, depth);
            let argument = substitute_bound_capture_avoiding(argument, index, replacement, depth);
            function.apply(&[argument])
        }
        Decomposition::Pi(input, output) => {
            let input = substitute_bound_capture_avoiding(input, index, replacement, depth);
            let output = substitute_bound_capture_avoiding(output, index, replacement, depth + 1);
            Term::pi(input, output)
        }
        Decomposition::Lambda(input, body) => {
            let input = substitute_bound_capture_avoiding(input, index, replacement, depth);
            let body = substitute_bound_capture_avoiding(body, index, replacement, depth + 1);
            Term::lambda(input, body)
        }
        Decomposition::ForAll(binder_type, body) => {
            let binder_type =
                substitute_bound_capture_avoiding(binder_type, index, replacement, depth);
            let body = substitute_bound_capture_avoiding(body, index, replacement, depth + 1);
            Term::forall(binder_type, body)
        }
        Decomposition::Exists(binder_type, body) => {
            let binder_type =
                substitute_bound_capture_avoiding(binder_type, index, replacement, depth);
            let body = substitute_bound_capture_avoiding(body, index, replacement, depth + 1);
            Term::exists(binder_type, body)
        }
    }
}

fn beta_reduce_head_lambda_application(term: &Term) -> Option<Term> {
    let Decomposition::Application(function, argument) = term.as_ref().decompose() else {
        return None;
    };
    let Decomposition::Lambda(_, body) = function.decompose() else {
        return None;
    };

    // Standard de Bruijn beta reduction:
    // shift(-1, subst(0, shift(1, arg), body))
    let lifted_argument = argument.to_owned().shift_bound(0, 1);
    let substituted = substitute_bound_capture_avoiding(body, 0, &lifted_argument, 0);
    Some(substituted.shift_bound(0, -1))
}

fn cancel_double_negation(term: &Term) -> Option<Term> {
    let args = split_symbol_application(term, Symbol::Not, 1)?;
    let inner_args = split_symbol_application(&args[0], Symbol::Not, 1)?;
    Some(inner_args[0].clone())
}

fn normalize_fully_applied_eq(term: &Term) -> Option<Term> {
    let args = split_symbol_application(term, Symbol::Eq, 3)?;
    let eq_type = args[0].clone();
    let left = args[1].clone();
    let right = args[2].clone();
    if left <= right {
        return None;
    }
    Some(Term::eq(eq_type, right, left))
}

/// Recursively beta-reduces head lambda applications within an arbitrary term.
pub fn beta_reduce_subterms(term: &Term) -> Term {
    let normalized = beta_reduce_term_children(term);
    if let Some(reduced) = beta_reduce_head_lambda_application(&normalized) {
        return beta_reduce_subterms(&reduced);
    }
    normalized
}

/// Recursively beta-reduces head lambda applications within every literal of a clause.
pub fn beta_reduce_clause_subterms(clause: &Clause) -> Clause {
    let literals = clause
        .literals
        .iter()
        .map(|literal| Literal {
            positive: literal.positive,
            left: beta_reduce_subterms(&literal.left),
            right: beta_reduce_subterms(&literal.right),
        })
        .collect();
    Clause::from_literals_unnormalized(literals, clause.get_local_context())
}

/// Recursively normalizes a kernel term.
///
/// This:
/// - beta-reduces head lambda applications
/// - cancels `not not`
/// - orders fully applied equality terms
/// - recurses under quantifier bodies
/// - preserves `not`, `and`, `or`, `forall`, and `exists` structure
///
/// Polarity-sensitive top-level decomposition still belongs in clausification,
/// so theorem normalization can flatten shapes like `not (a and b)` into a clause
/// without pushing `not` through connectives everywhere.
pub fn normalize_term(term: &Term) -> Term {
    let normalized = normalize_term_children(term);
    if let Some(reduced) = beta_reduce_head_lambda_application(&normalized) {
        return normalize_term(&reduced);
    }
    let normalized = cancel_double_negation(&normalized).unwrap_or(normalized);
    normalize_fully_applied_eq(&normalized).unwrap_or(normalized)
}

/// Compatibility wrapper while callers migrate to `normalize_term`.
pub fn normalize_boolean_subterms(term: &Term) -> Term {
    normalize_term(term)
}

#[cfg(test)]
mod tests {
    use super::{beta_reduce_clause_subterms, normalize_boolean_subterms, normalize_term};
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;

    #[test]
    fn test_normalize_boolean_subterms_cancels_double_negation() {
        let atom = Term::parse("c0");
        let term = Term::not(Term::not(atom.clone()));
        assert_eq!(normalize_term(&term), atom);
    }

    #[test]
    fn test_normalize_boolean_subterms_beta_reduces_head_lambda_application() {
        let body = Term::not(Term::not(Term::atom(Atom::BoundVariable(0))));
        let term = Term::lambda(Term::bool_type(), body).apply(&[Term::parse("c0")]);
        assert_eq!(normalize_term(&term), Term::parse("c0"));
    }

    #[test]
    fn test_normalize_boolean_subterms_beta_reduces_capture_avoiding() {
        let term = Term::lambda(
            Term::bool_type(),
            Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(1))),
        )
        .apply(&[Term::parse("c0")]);
        let expected = Term::lambda(Term::bool_type(), Term::parse("c0"));
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_beta_reduce_clause_subterms_reduces_literal_terms() {
        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(
                Term::lambda(
                    Term::bool_type(),
                    Term::not(Term::not(Term::atom(Atom::BoundVariable(0)))),
                )
                .apply(&[Term::parse("c0")]),
            )],
            &LocalContext::empty(),
        );

        let reduced = beta_reduce_clause_subterms(&clause);

        assert_eq!(
            reduced,
            Clause::from_literals_unnormalized(
                vec![Literal::positive(Term::not(Term::not(Term::parse("c0"))))],
                &LocalContext::empty(),
            )
        );
    }

    #[test]
    fn test_normalize_boolean_subterms_preserves_connective_shape() {
        let c0 = Term::parse("c0");
        let c1 = Term::parse("c1");
        let term = Term::not(Term::and(c0.clone(), Term::not(Term::not(c1.clone()))));
        let expected = Term::not(Term::and(c0, c1));
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_preserves_quantifier_heads() {
        let bound = Term::atom(Atom::BoundVariable(0));
        let predicate = Term::parse("c0").apply(&[bound.clone()]);
        let term = Term::not(Term::exists(
            Term::bool_type(),
            Term::not(Term::not(Term::and(bound.clone(), predicate.clone()))),
        ));
        let expected = Term::not(Term::exists(Term::bool_type(), Term::and(bound, predicate)));
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_recurses_under_quantifier_bodies() {
        let bound = Term::atom(Atom::BoundVariable(0));
        let predicate = Term::parse("c0").apply(&[bound.clone()]);
        let term = Term::forall(
            Term::bool_type(),
            Term::not(Term::not(Term::and(bound.clone(), predicate.clone()))),
        );
        let expected = Term::forall(Term::bool_type(), Term::and(bound, predicate));
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_recurses_inside_non_formula_terms() {
        let term = Term::parse("c0").apply(&[Term::not(Term::not(Term::and(
            Term::parse("c1"),
            Term::parse("c2"),
        )))]);
        let expected = Term::parse("c0").apply(&[Term::and(Term::parse("c1"), Term::parse("c2"))]);
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_leaves_other_builtins_alone() {
        let term = Term::atom(Atom::Symbol(Symbol::Eq)).apply(&[
            Term::bool_type(),
            Term::not(Term::not(Term::and(Term::parse("c0"), Term::parse("c1")))),
            Term::parse("c2"),
        ]);
        let expected = Term::atom(Atom::Symbol(Symbol::Eq)).apply(&[
            Term::bool_type(),
            Term::and(Term::parse("c0"), Term::parse("c1")),
            Term::parse("c2"),
        ]);
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_orders_fully_applied_eq() {
        let term = Term::eq(Term::bool_type(), Term::parse("c1"), Term::parse("c0"));
        let expected = Term::eq(Term::bool_type(), Term::parse("c0"), Term::parse("c1"));
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_wrapper_matches_normalize_term() {
        let term = Term::not(Term::not(Term::eq(
            Term::bool_type(),
            Term::parse("c1"),
            Term::parse("c0"),
        )));
        assert_eq!(normalize_boolean_subterms(&term), normalize_term(&term));
    }
}
