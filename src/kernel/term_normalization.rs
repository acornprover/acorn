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

fn is_boolean_formula_head(term: &Term) -> bool {
    split_symbol_application(term, Symbol::Not, 1).is_some()
        || split_symbol_application(term, Symbol::And, 2).is_some()
        || split_symbol_application(term, Symbol::Or, 2).is_some()
        || matches!(
            term.as_ref().decompose(),
            Decomposition::ForAll(_, _) | Decomposition::Exists(_, _)
        )
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
            let body = normalize_boolean_formula(&body.to_owned(), true);
            Term::forall(binder_type, body)
        }
        Decomposition::Exists(binder_type, body) => {
            let binder_type = normalize_boolean_subterms(&binder_type.to_owned());
            let body = normalize_boolean_formula(&body.to_owned(), true);
            Term::exists(binder_type, body)
        }
    }
}

fn normalize_boolean_formula(term: &Term, positive: bool) -> Term {
    if let Some(args) = split_symbol_application(term, Symbol::Not, 1) {
        return normalize_boolean_formula(&args[0], !positive);
    }

    if let Some(args) = split_symbol_application(term, Symbol::And, 2) {
        let left = normalize_boolean_formula(&args[0], positive);
        let right = normalize_boolean_formula(&args[1], positive);
        return if positive {
            Term::and(left, right)
        } else {
            Term::or(left, right)
        };
    }

    if let Some(args) = split_symbol_application(term, Symbol::Or, 2) {
        let left = normalize_boolean_formula(&args[0], positive);
        let right = normalize_boolean_formula(&args[1], positive);
        return if positive {
            Term::or(left, right)
        } else {
            Term::and(left, right)
        };
    }

    let normalized = normalize_term_children(term);
    if positive {
        normalized
    } else {
        Term::not(normalized)
    }
}

/// Recursively normalizes boolean-valued subterms within an arbitrary term.
///
/// This:
/// - pushes `not` through `and` and `or`
/// - cancels `not not`
/// - recurses under quantifier bodies
/// - preserves `forall` and `exists` heads
pub fn normalize_boolean_subterms(term: &Term) -> Term {
    if is_boolean_formula_head(term) {
        normalize_boolean_formula(term, true)
    } else {
        normalize_term_children(term)
    }
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
    fn test_normalize_boolean_subterms_pushes_not_through_connectives() {
        let c0 = Term::parse("c0");
        let c1 = Term::parse("c1");
        let c2 = Term::parse("c2");
        let term = Term::not(Term::and(
            c0.clone(),
            Term::or(Term::not(c1.clone()), c2.clone()),
        ));
        let expected = Term::or(c0.clone().not(), Term::and(c1, c2.not()));
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_preserves_quantifier_heads() {
        let bound = Term::atom(Atom::BoundVariable(0));
        let predicate = Term::parse("c0").apply(&[bound.clone()]);
        let term = Term::not(Term::exists(
            Term::bool_type(),
            Term::not(Term::and(bound.clone(), predicate.clone())),
        ));
        let expected = Term::not(Term::exists(
            Term::bool_type(),
            Term::or(Term::not(bound), Term::not(predicate)),
        ));
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_recurses_under_quantifier_bodies() {
        let bound = Term::atom(Atom::BoundVariable(0));
        let predicate = Term::parse("c0").apply(&[bound.clone()]);
        let term = Term::forall(
            Term::bool_type(),
            Term::not(Term::and(bound.clone(), predicate.clone())),
        );
        let expected = Term::forall(
            Term::bool_type(),
            Term::or(Term::not(bound), Term::not(predicate)),
        );
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }

    #[test]
    fn test_normalize_boolean_subterms_recurses_inside_non_formula_terms() {
        let term =
            Term::parse("c0").apply(&[Term::not(Term::and(Term::parse("c1"), Term::parse("c2")))]);
        let expected = Term::parse("c0").apply(&[Term::or(
            Term::not(Term::parse("c1")),
            Term::not(Term::parse("c2")),
        )]);
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }

    trait NotTerm {
        fn not(self) -> Term;
    }

    impl NotTerm for Term {
        fn not(self) -> Term {
            Term::not(self)
        }
    }

    #[test]
    fn test_normalize_boolean_subterms_leaves_other_builtins_alone() {
        let term = Term::atom(Atom::Symbol(Symbol::Eq)).apply(&[
            Term::bool_type(),
            Term::not(Term::and(Term::parse("c0"), Term::parse("c1"))),
            Term::parse("c2"),
        ]);
        let expected = Term::atom(Atom::Symbol(Symbol::Eq)).apply(&[
            Term::bool_type(),
            Term::or(Term::not(Term::parse("c0")), Term::not(Term::parse("c1"))),
            Term::parse("c2"),
        ]);
        assert_eq!(normalize_boolean_subterms(&term), expected);
    }
}
