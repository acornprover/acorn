use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::term_normalization::{normalize_clause_subterms, normalize_term};
use crate::kernel::variable_map::VariableMap;

/// A certificate claim line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Claim {
    /// The generic clause we are specializing.
    clause: Clause,

    /// Variable substitutions used for this claim.
    var_map: VariableMap,
}

impl Claim {
    /// Build a certificate claim pair in its canonical certificate form.
    ///
    /// The stored `clause` is the normalized generic theorem/pattern clause, and each mapped
    /// term in the `var_map` is term-normalized.
    ///
    /// Unlike full clause normalization, this keeps all existing local-variable slots fixed in
    /// place so `(clause, var_map)` round-trips remain stable for certificates.
    pub fn new(mut clause: Clause, mut var_map: VariableMap) -> Result<Claim, String> {
        clause = clause.normalized_preserving_locals();
        var_map.apply_to_all(normalize_term);

        let claim = Claim { clause, var_map };
        claim.validate_var_map_scope()?;
        Ok(claim)
    }

    fn validate_var_map_scope(&self) -> Result<(), String> {
        let generic_len = self.clause.get_local_context().len();
        for (var_id, term) in self.var_map.iter() {
            if var_id >= generic_len {
                return Err(format!(
                    "claim var map binds out-of-scope variable x{}",
                    var_id
                ));
            }
            if let Some(max_var) = term.max_variable() {
                if max_var as usize >= generic_len {
                    return Err(format!(
                        "claim var map term references out-of-scope variable x{}",
                        max_var
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn clause(&self) -> &Clause {
        &self.clause
    }

    pub fn var_map(&self) -> &VariableMap {
        &self.var_map
    }

    pub fn normalized_generic_clause(&self) -> Clause {
        self.clause.normalized()
    }

    /// Apply the claim's substitutions without normalizing the resulting clause.
    ///
    /// This is for certificate/display reconstruction paths that need to preserve the
    /// immediate substitution shape. Semantic checking should use
    /// `normalized_specialized_clause()` instead.
    pub fn specialized_clause_for_display(
        &self,
        kernel_context: &KernelContext,
    ) -> Result<Clause, String> {
        self.validate_var_map_scope()?;
        Ok(self.var_map.specialize_clause(&self.clause, kernel_context))
    }

    pub fn normalized_specialized_clause(
        &self,
        kernel_context: &KernelContext,
    ) -> Result<Clause, String> {
        Ok(
            normalize_clause_subterms(&self.specialized_clause_for_display(kernel_context)?)
                .normalized(),
        )
    }
}

/// A single kernel-level step in certificate generation/checking.
///
/// Parsing and generation both use this representation. Each step corresponds to one
/// line of certificate code.
#[derive(Clone, PartialEq, Eq)]
pub enum CertificateStep {
    /// A claim statement with a generic clause plus specialization map.
    Claim(Claim),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;

    #[test]
    fn test_claim_new_preserves_local_slots_and_normalizes_var_map_terms() {
        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::eq(
                Term::bool_type(),
                Term::new_variable(1),
                Term::new_variable(1),
            ))],
            &LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]),
        );

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::not(Term::not(Term::new_false())));
        var_map.set(1, Term::new_true());

        let claim = Claim::new(clause, var_map).expect("claim should normalize");

        assert_eq!(claim.clause.get_local_context().len(), 2);
        assert_eq!(claim.var_map.get_mapping(0), Some(&Term::new_false()));
        assert_eq!(claim.var_map.get_mapping(1), Some(&Term::new_true()));
    }

    #[test]
    fn test_claim_specialization_keeps_display_shape_but_normalizes_checker_shape() {
        use crate::kernel::atom::Atom;

        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constant("c0", "Bool");

        let claim = Claim::new(kernel_context.parse_clause("x0(c0)", &["Bool -> Bool"]), {
            let mut var_map = VariableMap::new();
            var_map.set(
                0,
                Term::lambda(
                    Term::bool_type(),
                    Term::not(Term::not(Term::atom(Atom::BoundVariable(0)))),
                ),
            );
            var_map
        })
        .expect("claim should normalize");

        let display_clause = claim
            .specialized_clause_for_display(&kernel_context)
            .expect("display specialization should succeed");
        let normalized_clause = claim
            .normalized_specialized_clause(&kernel_context)
            .expect("normalized specialization should succeed");
        let expected_display_clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(
                Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0)))
                    .apply(&[kernel_context.parse_term("c0")]),
            )],
            &LocalContext::empty(),
        );
        let expected_normalized_clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(kernel_context.parse_term("c0"))],
            &LocalContext::empty(),
        );

        assert_ne!(display_clause, normalized_clause);
        assert_eq!(display_clause, expected_display_clause);
        assert_eq!(normalized_clause, expected_normalized_clause);
    }
}
