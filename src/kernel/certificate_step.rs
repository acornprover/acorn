use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::AcornValue;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::term_normalization::{normalize_clause_subterms, normalize_term};
use crate::kernel::variable_map::{apply_to_term, VariableMap};

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
    /// term in the `var_map` is term-normalized and rewritten to the clause's normalized
    /// variable numbering.
    pub fn new(clause: Clause, mut var_map: VariableMap) -> Result<Claim, String> {
        let trace =
            Clause::normalize_with_trace(clause.literals.clone(), clause.get_local_context());
        var_map.apply_to_all(normalize_term);
        let renumber_map = VariableMap::from_var_ids(&trace.var_ids);
        let mut normalized_var_map = VariableMap::new();
        for (new_id, old_id) in trace.var_ids.iter().enumerate() {
            let Some(term) = var_map.get_mapping(*old_id) else {
                continue;
            };
            normalized_var_map.set(
                new_id as AtomId,
                apply_to_term(term.as_ref(), &renumber_map),
            );
        }

        let claim = Claim {
            clause: trace.clause,
            var_map: normalized_var_map,
        };
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
        self.clause.clone()
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

    #[cfg(any(test, feature = "validate"))]
    pub fn validate_normalized_shape(&self, kernel_context: &KernelContext) -> Result<(), String> {
        let _ = kernel_context;
        if self.clause != self.clause.normalized_preserving_locals() {
            return Err(format!(
                "claim generic clause is not normalized-preserving-locals: {}",
                self.clause
            ));
        }

        for (var_id, term) in self.var_map.iter() {
            let normalized = normalize_term(term);
            if *term != normalized {
                return Err(format!(
                    "claim var_map term x{} is not normalized: {} -> {}",
                    var_id, term, normalized
                ));
            }
        }

        let specialized = self.normalized_specialized_clause(kernel_context)?;
        if specialized != specialized.normalized() {
            return Err(format!(
                "claim specialized clause is not normalized: {}",
                specialized
            ));
        }
        Ok(())
    }

    #[cfg(feature = "validate")]
    pub fn validate_roundtrip_shape(&self, kernel_context: &KernelContext) -> Result<(), String> {
        self.validate_normalized_shape(kernel_context)?;
        kernel_context.validate_clause_roundtrip(&self.clause)?;
        let specialized = self.normalized_specialized_clause(kernel_context)?;
        kernel_context.validate_clause_roundtrip(&specialized)?;
        Ok(())
    }
}

/// A `let ... satisfy` declaration step in a certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatisfyStep {
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub arguments: Vec<(String, AcornType)>,
    pub return_name: Option<String>,
    pub return_type: AcornType,
    pub condition: AcornValue,
    /// The implicit `exists` / `forall ... exists` claim justified by this line.
    pub justification: Claim,
    /// The exact instantiated proposition made available after naming the witness.
    pub specialized_clause: Option<Clause>,
    /// The clauses made available after naming the witness.
    pub witness_clauses: Vec<Clause>,
}

impl SatisfyStep {
    /// Distinguish function witnesses from plain value witnesses.
    pub fn is_function(&self) -> bool {
        self.return_name.is_some()
    }
}

/// A single kernel-level step in certificate generation/checking.
///
/// Parsing and generation both use this representation. Each step corresponds to one
/// line of certificate code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateStep {
    /// A claim statement with a generic clause plus specialization map.
    Claim(Claim),

    /// A witness declaration that introduces a named synthetic value/function.
    Satisfy(SatisfyStep),
}

impl CertificateStep {
    #[cfg(any(test, feature = "validate"))]
    pub fn validate_normalized_shape(&self, kernel_context: &KernelContext) -> Result<(), String> {
        match self {
            CertificateStep::Claim(claim) => claim.validate_normalized_shape(kernel_context),
            CertificateStep::Satisfy(step) => {
                step.justification
                    .validate_normalized_shape(kernel_context)?;
                if let Some(clause) = &step.specialized_clause {
                    if *clause != clause.normalized() {
                        return Err(format!("specialized clause is not normalized: {}", clause));
                    }
                }
                for clause in &step.witness_clauses {
                    if *clause != clause.normalized() {
                        return Err(format!("witness clause is not normalized: {}", clause));
                    }
                }
                Ok(())
            }
        }
    }

    #[cfg(feature = "validate")]
    pub fn validate_roundtrip_shape(&self, kernel_context: &KernelContext) -> Result<(), String> {
        match self {
            CertificateStep::Claim(claim) => claim.validate_roundtrip_shape(kernel_context),
            CertificateStep::Satisfy(step) => {
                step.justification
                    .validate_roundtrip_shape(kernel_context)?;
                if let Some(clause) = &step.specialized_clause {
                    kernel_context.validate_clause_roundtrip(clause)?;
                }
                for clause in &step.witness_clauses {
                    kernel_context.validate_clause_roundtrip(clause)?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;

    #[test]
    fn test_claim_new_normalizes_var_map_terms() {
        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::eq(
                Term::bool_type(),
                Term::new_variable(0),
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
    fn test_claim_new_renumbers_var_map_to_match_normalized_clause() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constant("g0", "(Bool, Bool) -> Bool");
        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(
                kernel_context
                    .parse_term("g0")
                    .apply(&[Term::new_variable(1), Term::new_variable(0)]),
            )],
            &LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]),
        );
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::new_false());
        var_map.set(1, Term::new_true());

        let claim = Claim::new(clause, var_map).expect("claim should normalize");

        let expected = kernel_context.parse_clause("g0(x0, x1)", &["Bool", "Bool"]);

        assert_eq!(claim.normalized_generic_clause(), expected);
        assert_eq!(claim.var_map.get_mapping(0), Some(&Term::new_true()));
        assert_eq!(claim.var_map.get_mapping(1), Some(&Term::new_false()));
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
