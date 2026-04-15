use crate::kernel::atom::AtomId;
use crate::kernel::literal::Literal;
use crate::kernel::term::Term;

type ClauseLiterals = Vec<Vec<Literal>>;

fn clauses_true() -> ClauseLiterals {
    vec![]
}

fn clauses_false() -> ClauseLiterals {
    vec![vec![]]
}

fn clauses_from_literal(literal: Literal) -> ClauseLiterals {
    if literal.is_true_value() {
        clauses_true()
    } else if literal.is_false_value() {
        clauses_false()
    } else {
        vec![vec![literal]]
    }
}

fn literal_if_clauses(
    condition: Literal,
    consequence: Literal,
    alternative: Literal,
) -> ClauseLiterals {
    vec![
        vec![condition.negate(), consequence],
        vec![condition, alternative],
    ]
}

// An ExtendedTerm is like a term in the sense that a comparison between two of them can be
// converted into a raw set of literal clauses.
// They can be Boolean or have non-Boolean types.
#[derive(Clone, Debug)]
pub enum ExtendedTerm {
    Term(Term),

    // (condition, then branch, else branch)
    If(Literal, Term, Term),

    // Lambda(args, body) represents the value f such that f(args) = body.
    // The Term in the tuple is the type of the argument.
    Lambda(Vec<(AtomId, Term)>, Term),
}

impl std::fmt::Display for ExtendedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtendedTerm::Term(term) => write!(f, "{}", term),
            ExtendedTerm::If(condition, then_branch, else_branch) => {
                write!(
                    f,
                    "if {} then {} else {}",
                    condition, then_branch, else_branch
                )
            }
            ExtendedTerm::Lambda(args, body) => {
                write!(f, "function(")?;
                for (i, (arg_id, _)) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "x{}", arg_id,)?;
                }
                write!(f, ") {{ {} }}", body)
            }
        }
    }
}

impl ExtendedTerm {
    /// Convert an `ExtendedTerm::Term` into a plain `Term`.
    pub fn to_term(self) -> Result<Term, String> {
        match self {
            ExtendedTerm::Term(t) => Ok(t),
            other => Err(format!("expected plain term but got {}", other)),
        }
    }

    /// Apply arguments to an ExtendedTerm, similar to Term::apply.
    pub fn apply(&self, args: &[Term]) -> ExtendedTerm {
        match self {
            ExtendedTerm::Term(term) => ExtendedTerm::Term(term.apply(args)),
            ExtendedTerm::If(cond, then_term, else_term) => {
                let new_then = then_term.apply(args);
                let new_else = else_term.apply(args);
                ExtendedTerm::If(cond.clone(), new_then, new_else)
            }
            ExtendedTerm::Lambda(lambda_args, body) => {
                if args.len() < lambda_args.len() {
                    // Partial application - substitute some args and return a new lambda
                    let (applied_args, remaining_args) = lambda_args.split_at(args.len());
                    let var_ids: Vec<_> = applied_args.iter().map(|(var_id, _)| *var_id).collect();
                    let terms: Vec<_> = args.iter().collect();
                    let new_body = body.replace_variables(&var_ids, &terms);
                    ExtendedTerm::Lambda(remaining_args.to_vec(), new_body)
                } else if args.len() == lambda_args.len() {
                    // Exact application - substitute the arguments into the body
                    let var_ids: Vec<_> = lambda_args.iter().map(|(var_id, _)| *var_id).collect();
                    let terms: Vec<_> = args.iter().collect();
                    let result = body.replace_variables(&var_ids, &terms);
                    ExtendedTerm::Term(result)
                } else {
                    // Over-application - apply lambda args first, then apply the rest
                    let (lambda_args_slice, rest_args) = args.split_at(lambda_args.len());
                    let var_ids: Vec<_> = lambda_args.iter().map(|(var_id, _)| *var_id).collect();
                    let terms: Vec<_> = lambda_args_slice.iter().collect();
                    let result = body.replace_variables(&var_ids, &terms);
                    let applied = result.apply(rest_args);
                    ExtendedTerm::Term(applied)
                }
            }
        }
    }

    /// Convert an equality comparison between this ExtendedTerm and a Term into raw clause
    /// literals.
    fn eq_term_to_clause_set(self, term: Term, negate: bool) -> Result<ClauseLiterals, String> {
        match self {
            ExtendedTerm::Term(left) => {
                let literal = Literal::new(!negate, left, term);
                Ok(clauses_from_literal(literal))
            }
            ExtendedTerm::If(cond, then_t, else_t) => {
                let then_lit = Literal::new(!negate, then_t, term.clone());
                let else_lit = Literal::new(!negate, else_t, term);
                Ok(literal_if_clauses(cond, then_lit, else_lit))
            }
            ExtendedTerm::Lambda(_, t) => Err(format!(
                "comparison to {} should have been normalized upstream",
                t
            )),
        }
    }

    /// Convert an equality comparison between two ExtendedTerms into raw clause literals.
    pub fn eq_to_clause_set(
        self,
        other: ExtendedTerm,
        negate: bool,
    ) -> Result<ClauseLiterals, String> {
        match (self, other) {
            (left, ExtendedTerm::Term(right)) => left.eq_term_to_clause_set(right, negate),
            (ExtendedTerm::Term(left), right) => right.eq_term_to_clause_set(left, negate),
            (left, right) => Err(format!(
                "cannot normalize comparison: {} {} {}",
                left,
                if negate { "!=" } else { "=" },
                right
            )),
        }
    }
}
