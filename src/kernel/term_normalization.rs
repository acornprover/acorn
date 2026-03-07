use crate::kernel::atom::Atom;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term};

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
            let function = normalize_boolean_subterms(&function.to_owned());
            let argument = normalize_boolean_subterms(&argument.to_owned());
            function.apply(&[argument])
        }
        Decomposition::Pi(input, output) => {
            let input = normalize_boolean_subterms(&input.to_owned());
            let output = normalize_boolean_subterms(&output.to_owned());
            Term::pi(input, output)
        }
        Decomposition::Lambda(input, body) => {
            let input = normalize_boolean_subterms(&input.to_owned());
            let body = normalize_boolean_subterms(&body.to_owned());
            Term::lambda(input, body)
        }
        Decomposition::ForAll(binder_type, body) => {
            let binder_type = normalize_boolean_subterms(&binder_type.to_owned());
            let body = normalize_boolean_subterms(&body.to_owned());
            Term::forall(binder_type, body)
        }
        Decomposition::Exists(binder_type, body) => {
            let binder_type = normalize_boolean_subterms(&binder_type.to_owned());
            let body = normalize_boolean_subterms(&body.to_owned());
            Term::exists(binder_type, body)
        }
    }
}

fn cancel_double_negation(term: &Term) -> Option<Term> {
    let args = split_symbol_application(term, Symbol::Not, 1)?;
    let inner_args = split_symbol_application(&args[0], Symbol::Not, 1)?;
    Some(inner_args[0].clone())
}

/// Recursively normalizes boolean-valued subterms within an arbitrary term.
///
/// This:
/// - cancels `not not`
/// - recurses under quantifier bodies
/// - preserves `not`, `and`, `or`, `forall`, and `exists` structure
///
/// Polarity-sensitive top-level decomposition still belongs in clausification,
/// so theorem normalization can flatten shapes like `not (a and b)` into a clause
/// without pushing `not` through connectives everywhere.
pub fn normalize_boolean_subterms(term: &Term) -> Term {
    let normalized = normalize_term_children(term);
    cancel_double_negation(&normalized).unwrap_or(normalized)
}

#[cfg(test)]
mod tests {
    use super::normalize_boolean_subterms;
    use crate::kernel::atom::Atom;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;

    #[test]
    fn test_normalize_boolean_subterms_cancels_double_negation() {
        let atom = Term::parse("c0");
        let term = Term::not(Term::not(atom.clone()));
        assert_eq!(normalize_boolean_subterms(&term), atom);
    }

    #[test]
    fn test_normalize_boolean_subterms_preserves_connective_shape() {
        let c0 = Term::parse("c0");
        let c1 = Term::parse("c1");
        let term = Term::not(Term::and(c0.clone(), Term::not(Term::not(c1.clone()))));
        let expected = Term::not(Term::and(c0, c1));
        assert_eq!(normalize_boolean_subterms(&term), expected);
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
        assert_eq!(normalize_boolean_subterms(&term), expected);
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
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_recurses_inside_non_formula_terms() {
        let term = Term::parse("c0").apply(&[Term::not(Term::not(Term::and(
            Term::parse("c1"),
            Term::parse("c2"),
        )))]);
        let expected = Term::parse("c0").apply(&[Term::and(Term::parse("c1"), Term::parse("c2"))]);
        assert_eq!(normalize_boolean_subterms(&term), expected);
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
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }
}
