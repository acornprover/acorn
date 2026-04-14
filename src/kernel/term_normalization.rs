//! Kernel term normalization is only one part of the surface/kernel contract.
//!
//! The full model is documented in `docs/normalization.md`. At a high level, the conceptual
//! layer transitions are:
//!
//! - `parse: String -> Expression`
//! - `elaborate: Expression -> AcornValue`
//! - `lower_term: AcornValue -> Term`
//! - `lower_theorem: theorem-shaped AcornValue -> Vec<Clause>`
//! - `lower_proposition: proposition-shaped AcornValue -> Vec<Clause>`
//! - `lower_clause: clause-shaped AcornValue -> Clause`
//! - `quote_term: Term -> AcornValue`
//! - `quote_clause: Clause -> AcornValue`
//!
//! These names describe contracts, not necessarily one public Rust function per line.
//!
//! This file owns only the recursive, structure-preserving normalization of [`Term`]s.
//! It must normalize every subterm of a normalized term.
//!
//! It does not own:
//!
//! - theorem lowering (`lower_theorem`)
//! - proposition lowering (`lower_proposition`)
//! - clause lowering (`lower_clause`)
//! - clause normalization
//! - surface quoting or code generation
//!
//! The system-wide exact roundtrip contract is for normalized clauses:
//!
//! - `lower_clause(quote_clause(c)) == c`
//!
//! Theorem lowering and proposition lowering are semantic lowerings and are not required to be
//! exact inverses of quoting.
//!
//! The global requirements are:
//!
//! - Every `ProofStep` must have its clause normalized.
//! - In a normalized term or clause, every subterm must also be normalized.
//! - For certificates, the generic clause in a `(clause, var_map)` claim must be normalized.
//! - For certificates, each mapped term in a claim `var_map` must be term-normalized.
//! - Parsing a non-normalized certificate claim must normalize into that canonical
//!   `(clause, var_map)` object rather than preserving a merely display-equivalent surface shape.
//! - For certificates, serializing a `(clause, var_map)` pair and then deserializing it
//!   must recover the exact same normalized generic `(clause, var_map)` pair.
//! - `claim-with-args` is only surface syntax for that canonical certificate object:
//!   its generic body must follow `quote_clause`, and its mapped value arguments must
//!   follow the usual quoted-term form.
//! - Normalization canonicalizes the built-in commutative operators `=`, `and`, and `or`
//!   up to commutativity only.
//! - Clause normalization may deterministically renumber free variables to a preferred
//!   numbering, but this is best-effort only.
//! - Normalization must be idempotent.
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

fn references_bound_range(term: TermRef<'_>, start: u16, end: u16, depth: u16) -> bool {
    match term.decompose() {
        Decomposition::Atom(Atom::BoundVariable(i)) => *i >= start + depth && *i < end + depth,
        Decomposition::Atom(_) => false,
        Decomposition::Application(function, argument) => {
            references_bound_range(function, start, end, depth)
                || references_bound_range(argument, start, end, depth)
        }
        Decomposition::Pi(input, output) => {
            references_bound_range(input, start, end, depth)
                || references_bound_range(output, start, end, depth + 1)
        }
        Decomposition::Lambda(input, body) => {
            references_bound_range(input, start, end, depth)
                || references_bound_range(body, start, end, depth + 1)
        }
        Decomposition::ForAll(binder_type, body) => {
            references_bound_range(binder_type, start, end, depth)
                || references_bound_range(body, start, end, depth + 1)
        }
        Decomposition::Exists(binder_type, body) => {
            references_bound_range(binder_type, start, end, depth)
                || references_bound_range(body, start, end, depth + 1)
        }
    }
}

fn eta_reduce_single_lambda(term: &Term) -> Option<Term> {
    let (_input_type, body) = term.as_ref().split_lambda()?;
    let (function, args) = body.split_application_multi()?;
    let (last_arg, prefix_args) = args.split_last()?;
    if *last_arg != Term::atom(Atom::BoundVariable(0)) {
        return None;
    }
    if references_bound_range(function.as_ref(), 0, 1, 0) {
        return None;
    }
    if prefix_args
        .iter()
        .any(|arg| references_bound_range(arg.as_ref(), 0, 1, 0))
    {
        return None;
    }

    Some(function.apply(prefix_args).shift_bound(1, -1))
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
    let already_ordered = match (left.atomic_variable(), right.atomic_variable()) {
        (Some(left_var), Some(right_var)) => left_var <= right_var,
        _ => left <= right,
    };
    if already_ordered {
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

/// Recursively term-normalizes every literal subterm of a clause.
///
/// This applies the standard kernel term normalizer to each side of each literal, without doing
/// any clause-level cleanup such as literal deduplication or variable renumbering.
pub fn normalize_clause_subterms(clause: &Clause) -> Clause {
    let literals = clause
        .literals
        .iter()
        .map(|literal| Literal {
            positive: literal.positive,
            left: normalize_term(&literal.left),
            right: normalize_term(&literal.right),
        })
        .collect();
    Clause::from_literals_unnormalized(literals, clause.get_local_context())
}

/// Recursively normalizes a kernel term.
///
/// This:
/// - beta-reduces head lambda applications
/// - eta-reduces lambdas that only forward their bound variable
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
    if let Some(reduced) = eta_reduce_single_lambda(&normalized) {
        return normalize_term(&reduced);
    }
    let normalized = cancel_double_negation(&normalized).unwrap_or(normalized);
    normalize_fully_applied_eq(&normalized).unwrap_or(normalized)
}

/// Normalize a term for clause normalization while interpreting it under a target boolean polarity.
///
/// This is the shared polarity-aware term rewriting used by clause normalization.
/// It pushes `not` through the built-in boolean connectives and quantifiers, while
/// preserving the historical clause-normalization behavior.
pub(crate) fn normalize_clause_term_with_polarity(term: &Term, positive: bool) -> Term {
    if let Some(args) = split_symbol_application(term, Symbol::Not, 1) {
        return normalize_clause_term_with_polarity(&args[0], !positive);
    }

    if let Some(args) = split_symbol_application(term, Symbol::And, 2) {
        let left = normalize_clause_term_with_polarity(&args[0], positive);
        let right = normalize_clause_term_with_polarity(&args[1], positive);
        return if positive {
            Term::and(left, right)
        } else {
            Term::or(left, right)
        };
    }

    if let Some(args) = split_symbol_application(term, Symbol::Or, 2) {
        let left = normalize_clause_term_with_polarity(&args[0], positive);
        let right = normalize_clause_term_with_polarity(&args[1], positive);
        return if positive {
            Term::or(left, right)
        } else {
            Term::and(left, right)
        };
    }

    match term.as_ref().decompose() {
        Decomposition::ForAll(binder_type, body) => {
            let binder_type = normalize_clause_term(&binder_type.to_owned());
            let body = normalize_clause_term_with_polarity(&body.to_owned(), positive);
            if positive {
                Term::forall(binder_type, body)
            } else {
                Term::exists(binder_type, body)
            }
        }
        Decomposition::Exists(binder_type, body) => {
            let binder_type = normalize_clause_term(&binder_type.to_owned());
            let body = normalize_clause_term_with_polarity(&body.to_owned(), positive);
            if positive {
                Term::exists(binder_type, body)
            } else {
                Term::forall(binder_type, body)
            }
        }
        Decomposition::Atom(_) => {
            if positive {
                term.clone()
            } else {
                Term::not(term.clone())
            }
        }
        Decomposition::Application(function, argument) => {
            let function = normalize_clause_term(&function.to_owned());
            let argument = normalize_clause_term(&argument.to_owned());
            let rebuilt = function.apply(&[argument]);
            let rebuilt = normalize_fully_applied_eq(&rebuilt).unwrap_or(rebuilt);
            if positive {
                rebuilt
            } else {
                Term::not(rebuilt)
            }
        }
        Decomposition::Pi(input, output) => {
            let input = normalize_clause_term(&input.to_owned());
            let output = normalize_clause_term(&output.to_owned());
            let rebuilt = Term::pi(input, output);
            if positive {
                rebuilt
            } else {
                Term::not(rebuilt)
            }
        }
        Decomposition::Lambda(input, body) => {
            let input = normalize_clause_term(&input.to_owned());
            let body = normalize_clause_term(&body.to_owned());
            let rebuilt = Term::lambda(input, body);
            if positive {
                rebuilt
            } else {
                Term::not(rebuilt)
            }
        }
    }
}

/// Normalize a term for clause normalization under positive polarity.
pub(crate) fn normalize_clause_term(term: &Term) -> Term {
    normalize_clause_term_with_polarity(term, true)
}

/// Normalize a signed boolean term for clause normalization, possibly changing both the term
/// and its sign.
pub(crate) fn normalize_signed_clause_term(term: &Term, positive: bool) -> (Term, bool) {
    if let Some(args) = split_symbol_application(term, Symbol::Not, 1) {
        return normalize_signed_clause_term(&args[0], !positive);
    }

    if let Some(args) = split_symbol_application(term, Symbol::Or, 2) {
        let left = normalize_clause_term_with_polarity(&args[0], false);
        let right = normalize_clause_term_with_polarity(&args[1], false);
        return (Term::and(left, right), !positive);
    }

    (normalize_clause_term(term), positive)
}

/// Compatibility wrapper while callers migrate to `normalize_term`.
pub fn normalize_boolean_subterms(term: &Term) -> Term {
    normalize_term(term)
}

#[cfg(test)]
mod tests {
    use super::{
        beta_reduce_clause_subterms, normalize_boolean_subterms, normalize_clause_subterms,
        normalize_clause_term_with_polarity, normalize_signed_clause_term, normalize_term,
    };
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
    fn test_normalize_boolean_subterms_eta_reduces_simple_lambda() {
        let term = Term::lambda(
            Term::bool_type(),
            Term::parse("c0").apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        assert_eq!(normalize_term(&term), Term::parse("c0"));
    }

    #[test]
    fn test_normalize_boolean_subterms_eta_reduces_nested_lambdas() {
        let term = Term::lambda(
            Term::bool_type(),
            Term::lambda(
                Term::bool_type(),
                Term::parse("c0").apply(&[
                    Term::atom(Atom::BoundVariable(1)),
                    Term::atom(Atom::BoundVariable(0)),
                ]),
            ),
        );
        assert_eq!(normalize_term(&term), Term::parse("c0"));
    }

    #[test]
    fn test_normalize_boolean_subterms_eta_reduction_preserves_outer_binders() {
        let term = Term::lambda(
            Term::bool_type(),
            Term::lambda(
                Term::bool_type(),
                Term::lambda(
                    Term::bool_type(),
                    Term::parse("c0").apply(&[
                        Term::parse("c1").apply(&[Term::atom(Atom::BoundVariable(2))]),
                        Term::atom(Atom::BoundVariable(1)),
                        Term::atom(Atom::BoundVariable(0)),
                    ]),
                ),
            ),
        );
        let expected = Term::lambda(
            Term::bool_type(),
            Term::parse("c0")
                .apply(&[Term::parse("c1").apply(&[Term::atom(Atom::BoundVariable(0))])]),
        );
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_eta_reduction_requires_forwarding_shape() {
        let term = Term::lambda(
            Term::bool_type(),
            Term::parse("c0").apply(&[
                Term::atom(Atom::BoundVariable(0)),
                Term::atom(Atom::BoundVariable(0)),
            ]),
        );
        assert_eq!(normalize_term(&term), term);
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
    fn test_normalize_clause_subterms_applies_full_term_normalization() {
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

        let normalized = normalize_clause_subterms(&clause);

        assert_eq!(
            normalized,
            Clause::from_literals_unnormalized(
                vec![Literal::positive(Term::parse("c0"))],
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
    fn test_normalize_boolean_subterms_orders_fully_applied_eq_free_variables() {
        let term = Term::eq(
            Term::bool_type(),
            Term::new_variable(2),
            Term::new_variable(1),
        );
        let expected = Term::eq(
            Term::bool_type(),
            Term::new_variable(1),
            Term::new_variable(2),
        );
        assert_eq!(normalize_term(&term), expected);
    }

    #[test]
    fn test_normalize_term_with_polarity_pushes_negation_through_or() {
        let term = Term::or(Term::parse("c0"), Term::parse("c1"));
        let expected = Term::and(Term::not(Term::parse("c0")), Term::not(Term::parse("c1")));
        assert_eq!(normalize_clause_term_with_polarity(&term, false), expected);
    }

    #[test]
    fn test_normalize_signed_term_rewrites_signed_or() {
        let term = Term::or(Term::parse("c0"), Term::parse("c1"));
        let expected = Term::and(Term::not(Term::parse("c0")), Term::not(Term::parse("c1")));
        assert_eq!(normalize_signed_clause_term(&term, true), (expected, false));
    }

    #[test]
    fn test_normalize_term_with_polarity_orders_fully_applied_eq() {
        let term = Term::eq(Term::bool_type(), Term::parse("c1"), Term::parse("c0"));
        let expected = Term::eq(Term::bool_type(), Term::parse("c0"), Term::parse("c1"));
        assert_eq!(normalize_clause_term_with_polarity(&term, true), expected);
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
