use std::fmt;
use std::vec;

use crate::kernel::clause::Clause;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::Term;

/// A CNF (Conjunctive Normal Form) formula represented as a vector of clauses,
/// where each clause is a vector of literals.
///
/// An empty CNF (no clauses) represents "true".
/// A CNF containing an empty clause represents "false".
///
/// Note that these clauses are different from the "Clause" object because they are not
/// individually normalized. Variable ids have the same meaning across all clauses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cnf(Vec<Vec<Literal>>);

impl Cnf {
    /// Creates a new CNF from a vector of clauses.
    fn new(clauses: Vec<Vec<Literal>>) -> Self {
        Cnf(clauses)
    }

    /// Creates an empty CNF representing "true".
    pub fn true_value() -> Self {
        Cnf(vec![])
    }

    pub fn is_true_value(&self) -> bool {
        self.0.is_empty()
    }

    /// Creates a CNF with an empty clause representing "false".
    pub fn false_value() -> Self {
        Cnf(vec![vec![]])
    }

    pub fn is_false_value(&self) -> bool {
        self.0.len() == 1 && self.0[0].is_empty()
    }

    pub fn validate(&self) {
        for lits in &self.0 {
            for lit in lits {
                if !lit.is_normalized() {
                    panic!("Cnf contains non-normalized literal: {}", lit);
                }
            }
        }
    }

    /// Creates a CNF from a single literal.
    pub fn from_literal(literal: Literal) -> Self {
        if literal.is_true_value() {
            Self::true_value()
        } else if literal.is_false_value() {
            Self::false_value()
        } else {
            Cnf(vec![vec![literal]])
        }
    }

    /// The 'and' of two CNF formulas.
    /// Simply concatenates the clauses from both formulas.
    pub fn and(mut self, other: Cnf) -> Self {
        self.0.extend(other.0);
        self
    }

    pub fn and_all(formulas: impl Iterator<Item = Cnf>) -> Self {
        let mut result = Cnf::true_value();
        for formula in formulas {
            result = result.and(formula);
        }
        result
    }

    /// The 'or' of two CNF formulas.
    /// Applies the distributive law: (A ∧ B) ∨ (C ∧ D) = (A ∨ C) ∧ (A ∨ D) ∧ (B ∨ C) ∧ (B ∨ D)
    pub fn or(self, other: Cnf) -> Self {
        let mut result_clauses = vec![];
        for left_clause in &self.0 {
            for right_clause in &other.0 {
                let mut combined_clause = left_clause.clone();
                combined_clause.extend(right_clause.clone());
                result_clauses.push(combined_clause);
            }
        }
        Cnf(result_clauses)
    }

    pub fn or_all(formulas: impl Iterator<Item = Cnf>) -> Self {
        let mut result = Cnf::false_value();
        for formula in formulas {
            result = result.or(formula);
        }
        result
    }

    // Note that this causes exponential blowup.
    // Think of the input formula as And(Or(...)).
    // To negate it, it's Negate(And(Or(...))), which is equivalent to Or(And(Negate(...))).
    pub fn negate(&self) -> Cnf {
        Cnf::or_all(
            self.0.iter().map(|clause| {
                Cnf::and_all(clause.iter().map(|lit| Cnf::from_literal(lit.negate())))
            }),
        )
    }

    pub fn into_iter(self) -> impl Iterator<Item = Vec<Literal>> {
        self.0.into_iter()
    }

    pub fn into_clauses(self, local_context: &LocalContext) -> Vec<Clause> {
        self.0
            .into_iter()
            .filter(|literals| !literals.iter().any(|l| l.is_tautology()))
            .map(|literals| Clause::new(literals, local_context))
            .collect()
    }

    /// Converts CNF to clauses, keeping the first `pinned` variables at their
    /// original positions (x0, x1, ..., x_{pinned-1}).
    ///
    /// This is used when the first locals are pinned type parameters and must stay
    /// consistent across all clauses from one polymorphic statement. Variable
    /// renumbering during normalization could otherwise swap type-parameter
    /// references inside function types.
    pub fn into_clauses_with_pinned(
        self,
        local_context: &LocalContext,
        pinned: usize,
    ) -> Vec<Clause> {
        self.0
            .into_iter()
            .filter(|literals| !literals.iter().any(|l| l.is_tautology()))
            .map(|literals| Clause::new_with_pinned_vars(literals, local_context, pinned))
            .collect()
    }

    // Plain "true" or "false" are zero literals, not a single literal.
    fn is_single_literal(&self) -> bool {
        self.0.len() == 1 && self.0[0].len() == 1
    }

    fn into_single_literal(self) -> Literal {
        assert!(self.is_single_literal());
        self.0
            .into_iter()
            .next()
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
    }

    pub fn is_literal(&self) -> bool {
        self.is_true_value() || self.is_false_value() || self.is_single_literal()
    }

    pub fn as_literal(&self) -> Option<&Literal> {
        if self.is_single_literal() {
            Some(&self.0[0][0])
        } else {
            None
        }
    }

    // If these CNFs each represent a single signed term, and they are negations of each other,
    // return this term's signed term form.
    pub fn match_negated(&self, other: &Cnf) -> Option<(&Term, bool)> {
        let (self_term, self_sign) = self.as_signed_term()?;
        let (other_term, other_sign) = other.as_signed_term()?;
        if self_term == other_term && self_sign != other_sign {
            Some((&self_term, self_sign))
        } else {
            None
        }
    }

    pub fn to_literal(self) -> Option<Literal> {
        if self.is_true_value() {
            Some(Literal::true_value())
        } else if self.is_false_value() {
            Some(Literal::false_value())
        } else if self.is_single_literal() {
            Some(self.into_single_literal())
        } else {
            None
        }
    }

    pub fn to_bool(&self) -> Option<bool> {
        if self.is_true_value() {
            Some(true)
        } else if self.is_false_value() {
            Some(false)
        } else {
            None
        }
    }

    /// Returns Some((term, positive)) if this CNF can be converted into a single signed term.
    /// Returns None otherwise.
    /// A boolean literal "foo" or "not foo" can be converted to (foo, true) or (foo, false).
    pub fn as_signed_term(&self) -> Option<(&Term, bool)> {
        if !self.is_single_literal() {
            return None;
        }
        let literal = &self.0[0][0];
        if literal.is_signed_term() {
            Some((&literal.left, literal.positive))
        } else {
            None
        }
    }

    /// Convert an if-then-else structure among literals into CNF.
    pub fn literal_if(condition: Literal, consequence: Literal, alternative: Literal) -> Self {
        Cnf::new(vec![
            vec![condition.negate(), consequence],
            vec![condition, alternative],
        ])
    }

    /// Convert an if a { b } else { c } structure among CNF formulas into CNF.
    pub fn cnf_if(a: Literal, b: Cnf, c: Cnf) -> Self {
        let not_a_lit = Cnf::from_literal(a.negate());
        let a_lit = Cnf::from_literal(a);
        let not_a_imp_c = a_lit.or(c);
        let a_imp_b = not_a_lit.or(b);
        a_imp_b.and(not_a_imp_c)
    }

    /// Parse a CNF formula from a string.
    /// The string should be in the format "clause1 and clause2 and ..."
    /// where each clause is "literal1 or literal2 or ...".
    pub fn parse(s: &str) -> Self {
        let clauses: Vec<Vec<Literal>> = s
            .split(" and ")
            .map(|clause_str| {
                clause_str
                    .split(" or ")
                    .map(|lit_str| Literal::parse(lit_str))
                    .collect()
            })
            .collect();
        Cnf::new(clauses)
    }
}

impl fmt::Display for Cnf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_true_value() {
            write!(f, "true")
        } else if self.is_false_value() {
            write!(f, "false")
        } else {
            let clause_strings: Vec<String> = self
                .0
                .iter()
                .map(|clause| {
                    clause
                        .iter()
                        .map(|lit| lit.to_string())
                        .collect::<Vec<_>>()
                        .join(" or ")
                })
                .collect();
            write!(f, "{}", clause_strings.join(" and "))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cnf_negate() {
        let cnf = Cnf::parse("x0 or x1 and x2 or x3");

        let negated = cnf.negate();

        let expected = Cnf::parse(
            "\
        not x0 or not x2 and \
        not x0 or not x3 and \
        not x1 or not x2 and \
        not x1 or not x3",
        );

        assert_eq!(negated, expected);
    }

    #[test]
    fn test_as_signed_term() {
        // Positive boolean literal
        let cnf = Cnf::parse("x0");
        let (term, positive) = cnf.as_signed_term().unwrap();
        assert_eq!(term, &Term::parse("x0"));
        assert_eq!(positive, true);

        // Negative boolean literal
        let cnf = Cnf::parse("not x0");
        let (term, positive) = cnf.as_signed_term().unwrap();
        assert_eq!(term, &Term::parse("x0"));
        assert_eq!(positive, false);

        // Equality - should return None
        let cnf = Cnf::parse("x0 = x1");
        assert_eq!(cnf.as_signed_term(), None);

        // Multiple clauses - should return None
        let cnf = Cnf::parse("x0 and x1");
        assert_eq!(cnf.as_signed_term(), None);

        // Disjunction - should return None
        let cnf = Cnf::parse("x0 or x1");
        assert_eq!(cnf.as_signed_term(), None);
    }
}
