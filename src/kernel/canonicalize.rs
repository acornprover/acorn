use crate::kernel::atom::Atom;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term};

/// Canonicalize a term for feature-gated term canonicalization.
///
/// This pass is intentionally logical (not clausification):
/// - Pushes negation inward to negation normal form (NNF) over ForAll/Exists/And/Or/Not.
/// - Canonicalizes `and`/`or` up to associativity + commutativity (flatten + sort).
/// - Canonicalizes `eq` up to commutativity (sort value arguments).
/// - Does not renumber variables.
pub fn canonicalize_term(term: &Term) -> Term {
    canonicalize_with_polarity(term, false)
}

fn canonicalize_with_polarity(term: &Term, negated: bool) -> Term {
    match term.as_ref().decompose() {
        Decomposition::Atom(_) => {
            if negated {
                mk_not(term.clone())
            } else {
                term.clone()
            }
        }
        Decomposition::Application(_, _) => canonicalize_application(term, negated),
        Decomposition::Pi(input, output) => {
            let result = Term::pi(
                canonicalize_with_polarity(&input.to_owned(), false),
                canonicalize_with_polarity(&output.to_owned(), false),
            );
            if negated {
                mk_not(result)
            } else {
                result
            }
        }
        Decomposition::Lambda(input, body) => {
            let result = Term::lambda(
                canonicalize_with_polarity(&input.to_owned(), false),
                canonicalize_with_polarity(&body.to_owned(), false),
            );
            if negated {
                mk_not(result)
            } else {
                result
            }
        }
        Decomposition::ForAll(binder_type, body) => {
            let canonical_binder = canonicalize_with_polarity(&binder_type.to_owned(), false);
            if negated {
                Term::exists(
                    canonical_binder,
                    canonicalize_with_polarity(&body.to_owned(), true),
                )
            } else {
                Term::forall(
                    canonical_binder,
                    canonicalize_with_polarity(&body.to_owned(), false),
                )
            }
        }
        Decomposition::Exists(binder_type, body) => {
            let canonical_binder = canonicalize_with_polarity(&binder_type.to_owned(), false);
            if negated {
                Term::forall(
                    canonical_binder,
                    canonicalize_with_polarity(&body.to_owned(), true),
                )
            } else {
                Term::exists(
                    canonical_binder,
                    canonicalize_with_polarity(&body.to_owned(), false),
                )
            }
        }
    }
}

fn canonicalize_application(term: &Term, negated: bool) -> Term {
    let Some((head, args)) = term.as_ref().split_application_multi() else {
        panic!("application decomposition should always split");
    };

    let head_symbol = match head.as_ref().decompose() {
        Decomposition::Atom(Atom::Symbol(symbol)) => Some(*symbol),
        _ => None,
    };

    match (head_symbol, args.len()) {
        (Some(Symbol::Not), 1) => canonicalize_with_polarity(&args[0], !negated),
        (Some(Symbol::And), 2) => {
            canonicalize_binary_connective(&args[0], &args[1], Symbol::And, Symbol::Or, negated)
        }
        (Some(Symbol::Or), 2) => {
            canonicalize_binary_connective(&args[0], &args[1], Symbol::Or, Symbol::And, negated)
        }
        (Some(Symbol::Eq), 3) => {
            let eq_type = canonicalize_with_polarity(&args[0], false);
            let mut left = canonicalize_with_polarity(&args[1], false);
            let mut right = canonicalize_with_polarity(&args[2], false);
            if right < left {
                std::mem::swap(&mut left, &mut right);
            }
            let result = mk_symbol_application(Symbol::Eq, vec![eq_type, left, right]);
            if negated {
                mk_not(result)
            } else {
                result
            }
        }
        _ => {
            let canonical_head = canonicalize_with_polarity(&head, false);
            let canonical_args: Vec<Term> = args
                .iter()
                .map(|arg| canonicalize_with_polarity(arg, false))
                .collect();
            let result = canonical_head.apply(&canonical_args);
            if negated {
                mk_not(result)
            } else {
                result
            }
        }
    }
}

fn canonicalize_binary_connective(
    left: &Term,
    right: &Term,
    positive_symbol: Symbol,
    negated_symbol: Symbol,
    negated: bool,
) -> Term {
    let (target_symbol, child_negated) = if negated {
        (negated_symbol, true)
    } else {
        (positive_symbol, false)
    };

    let mut parts = vec![];
    flatten_connective(
        target_symbol,
        canonicalize_with_polarity(left, child_negated),
        &mut parts,
    );
    flatten_connective(
        target_symbol,
        canonicalize_with_polarity(right, child_negated),
        &mut parts,
    );
    parts.sort();
    build_associative(target_symbol, parts)
}

fn split_symbol_application(term: &Term) -> Option<(Symbol, Vec<Term>)> {
    let (head, args) = term.as_ref().split_application_multi()?;
    match head.as_ref().decompose() {
        Decomposition::Atom(Atom::Symbol(symbol)) => Some((*symbol, args)),
        _ => None,
    }
}

fn flatten_connective(symbol: Symbol, term: Term, out: &mut Vec<Term>) {
    if let Some((head_symbol, args)) = split_symbol_application(&term) {
        if head_symbol == symbol && args.len() == 2 {
            let mut args = args.into_iter();
            let left = args.next().unwrap();
            let right = args.next().unwrap();
            flatten_connective(symbol, left, out);
            flatten_connective(symbol, right, out);
            return;
        }
    }
    out.push(term);
}

fn build_associative(symbol: Symbol, terms: Vec<Term>) -> Term {
    let mut iter = terms.into_iter();
    let first = iter
        .next()
        .expect("associative connective should have at least one term");
    iter.fold(first, |acc, next| {
        mk_symbol_application(symbol, vec![acc, next])
    })
}

fn mk_symbol_application(symbol: Symbol, args: Vec<Term>) -> Term {
    Term::atom(Atom::Symbol(symbol)).apply(&args)
}

fn mk_not(term: Term) -> Term {
    mk_symbol_application(Symbol::Not, vec![term])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::atom::Atom;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;
    use crate::module::ModuleId;

    fn x(i: u16) -> Term {
        Term::new_variable(i)
    }

    fn b(i: u16) -> Term {
        Term::atom(Atom::BoundVariable(i))
    }

    fn not(term: Term) -> Term {
        Term::atom(Atom::Symbol(Symbol::Not)).apply(&[term])
    }

    fn and(left: Term, right: Term) -> Term {
        Term::atom(Atom::Symbol(Symbol::And)).apply(&[left, right])
    }

    fn or(left: Term, right: Term) -> Term {
        Term::atom(Atom::Symbol(Symbol::Or)).apply(&[left, right])
    }

    fn eq(ty: Term, left: Term, right: Term) -> Term {
        Term::atom(Atom::Symbol(Symbol::Eq)).apply(&[ty, left, right])
    }

    fn is_nnf(term: &Term) -> bool {
        match term.as_ref().decompose() {
            Decomposition::Atom(_) => true,
            Decomposition::Pi(input, output)
            | Decomposition::Lambda(input, output)
            | Decomposition::ForAll(input, output)
            | Decomposition::Exists(input, output) => {
                is_nnf(&input.to_owned()) && is_nnf(&output.to_owned())
            }
            Decomposition::Application(_, _) => {
                let Some((head, args)) = term.as_ref().split_application_multi() else {
                    return false;
                };
                if matches!(
                    head.as_ref().decompose(),
                    Decomposition::Atom(Atom::Symbol(Symbol::Not))
                ) {
                    if args.len() != 1 {
                        return false;
                    }
                    match args[0].as_ref().decompose() {
                        Decomposition::ForAll(_, _) | Decomposition::Exists(_, _) => return false,
                        Decomposition::Application(_, _) => {
                            if let Some((symbol, _)) = split_symbol_application(&args[0]) {
                                if matches!(symbol, Symbol::Not | Symbol::And | Symbol::Or) {
                                    return false;
                                }
                            }
                        }
                        _ => {}
                    }
                }
                is_nnf(&head) && args.iter().all(is_nnf)
            }
        }
    }

    #[test]
    fn test_eq_commutative_canonicalization() {
        let term = eq(Term::bool_type(), x(2), x(0));
        let expected = eq(Term::bool_type(), x(0), x(2));
        assert_eq!(canonicalize_term(&term), expected);
    }

    #[test]
    fn test_and_associative_commutative_canonicalization() {
        let term = and(and(x(2), x(0)), x(1));
        let expected = and(and(x(0), x(1)), x(2));
        assert_eq!(canonicalize_term(&term), expected);
    }

    #[test]
    fn test_not_pushes_through_and() {
        let term = not(and(x(1), x(0)));
        let expected = or(not(x(0)), not(x(1)));
        assert_eq!(canonicalize_term(&term), expected);
    }

    #[test]
    fn test_not_pushes_through_quantifiers_without_renumbering() {
        let inner = and(b(1), b(0));
        let term = not(Term::forall(
            Term::bool_type(),
            Term::exists(Term::bool_type(), inner),
        ));
        let expected = Term::exists(
            Term::bool_type(),
            Term::forall(Term::bool_type(), or(not(b(0)), not(b(1)))),
        );
        assert_eq!(canonicalize_term(&term), expected);
    }

    #[test]
    fn test_nonlogical_head_stays_wrapped_by_not() {
        let f = Term::atom(Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 7)));
        let term = not(f.apply(&[and(x(1), x(0))]));
        let expected = not(f.apply(&[and(x(0), x(1))]));
        assert_eq!(canonicalize_term(&term), expected);
    }

    #[test]
    fn test_output_is_nnf_for_complex_formula() {
        let term = not(or(
            and(x(2), x(0)),
            Term::forall(Term::bool_type(), and(b(0), x(1))),
        ));
        let canonical = canonicalize_term(&term);
        assert!(is_nnf(&canonical), "term is not in nnf: {}", canonical);
    }
}
