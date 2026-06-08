use std::collections::{HashMap, HashSet};

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::{AcornValue, ConstantInstance};
use crate::elaborator::names::ConstantName;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::elaborator::to_term::build_type_var_map;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::{normalize_clause_subterms, normalize_term};
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::module::ModuleId;

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
        let input_context = clause.get_local_context().clone();
        let pinned_type_params = input_context
            .get_var_types()
            .iter()
            .take_while(|var_type| {
                var_type
                    .as_ref()
                    .is_some_and(|term| term.as_ref().is_type_param_kind())
            })
            .count();
        let trace = Clause::normalize_with_trace_pinned(
            clause.literals.clone(),
            clause.get_local_context(),
            pinned_type_params,
        );
        var_map.apply_to_all(normalize_term);

        let mut var_ids = trace.var_ids.clone();
        let mut renumbered_terms = HashMap::new();
        for (old_id, term) in var_map.iter() {
            let mut term = term.clone();
            term.normalize_var_ids_with_context(&mut var_ids, &input_context);
            renumbered_terms.insert(old_id as AtomId, term);
        }

        let mut normalized_var_map = VariableMap::new();
        for (new_id, old_id) in var_ids.iter().enumerate() {
            let Some(term) = renumbered_terms.get(old_id) else {
                continue;
            };
            normalized_var_map.set(new_id as AtomId, term.clone());
        }

        let mut normalized_clause = trace.clause;
        normalized_clause.context = input_context.remap(&var_ids);
        let claim = Claim {
            clause: normalized_clause,
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

    fn specialized_replacement_context(&self) -> LocalContext {
        let input_context = self.clause.get_local_context();
        let mut output_context = self.var_map.build_output_context(input_context);
        for i in 0..input_context.len() {
            if self.var_map.get_mapping(i as AtomId).is_none() {
                if let Some(var_type) = input_context.get_var_type(i) {
                    output_context.set_type(i, var_type.clone());
                }
            }
        }
        output_context
    }

    fn term_has_expected_type(
        term: &Term,
        actual_type: &Term,
        expected_type: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        if let Some(required_tc) = expected_type.as_ref().as_typeclass() {
            return actual_type.as_ref().is_type0()
                || kernel_context.type_store.type_term_is_instance_of(
                    term.as_ref(),
                    local_context,
                    required_tc,
                );
        }
        if expected_type.as_ref().is_type0() && actual_type.as_ref().is_type_param_kind() {
            return true;
        }
        actual_type == expected_type
    }

    fn validate_var_map_types(&self, kernel_context: &KernelContext) -> Result<(), String> {
        let input_context = self.clause.get_local_context();
        let replacement_context = self.specialized_replacement_context();
        for (var_id, term) in self.var_map.iter() {
            let Some(expected_type) = input_context.get_var_type(var_id) else {
                return Err(format!(
                    "claim specialization binds variable x{} with no declared type",
                    var_id
                ));
            };
            let expected_type =
                normalize_term(&apply_to_term(expected_type.as_ref(), &self.var_map));
            let actual_type = normalize_term(
                &term
                    .checked_type_with_context(&replacement_context, kernel_context)
                    .map_err(|err| {
                        format!(
                            "claim specialization x{} is not well-typed: {}",
                            var_id, err
                        )
                    })?,
            );
            if !Self::term_has_expected_type(
                term,
                &actual_type,
                &expected_type,
                &replacement_context,
                kernel_context,
            ) {
                return Err(format!(
                    "claim specialization x{} has type {}, but expected {}",
                    var_id, actual_type, expected_type
                ));
            }
        }
        Ok(())
    }

    fn validate_clause_well_typed(
        label: &str,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Result<(), String> {
        let local_context = clause.get_local_context();
        if !local_context.validate_variable_ordering() {
            return Err(format!("{} has badly ordered variable types", label));
        }
        for (var_id, var_type) in local_context.get_var_types().iter().enumerate() {
            let Some(var_type) = var_type else {
                continue;
            };
            let var_type_kind = var_type
                .checked_type_with_context(local_context, kernel_context)
                .map_err(|err| {
                    format!(
                        "{} variable x{} has ill-typed type {}: {}",
                        label, var_id, var_type, err
                    )
                })?;
            if !var_type_kind.as_ref().is_type_param_kind() {
                return Err(format!(
                    "{} variable x{} has non-type type annotation {} with type {}",
                    label, var_id, var_type, var_type_kind
                ));
            }
        }
        for literal in &clause.literals {
            let left_type = normalize_term(
                &literal
                    .left
                    .checked_type_with_context(local_context, kernel_context)
                    .map_err(|err| {
                        format!(
                            "{} has ill-typed left side {}: {}",
                            label, literal.left, err
                        )
                    })?,
            );
            let right_type = normalize_term(
                &literal
                    .right
                    .checked_type_with_context(local_context, kernel_context)
                    .map_err(|err| {
                        format!(
                            "{} has ill-typed right side {}: {}",
                            label, literal.right, err
                        )
                    })?,
            );
            if left_type != right_type {
                return Err(format!(
                    "{} literal type mismatch: {} has type {}, but {} has type {}",
                    label, literal.left, left_type, literal.right, right_type
                ));
            }
        }
        Ok(())
    }

    pub fn validate_checker_payload(&self, kernel_context: &KernelContext) -> Result<(), String> {
        self.validate_var_map_scope()?;
        Self::validate_clause_well_typed("claim generic clause", &self.clause, kernel_context)?;
        self.validate_var_map_types(kernel_context)?;
        let specialized = self.normalized_specialized_clause(kernel_context)?;
        Self::validate_clause_well_typed("claim specialized clause", &specialized, kernel_context)?;
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
        Ok(self
            .var_map
            .specialize_clause(&self.clause, kernel_context)
            .compacted_var_ids_preserving_literal_shape())
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

    fn type_var_map_for_params(
        kernel_context: &mut KernelContext,
        type_params: &[TypeParam],
    ) -> Option<HashMap<String, (AtomId, Term)>> {
        if type_params.is_empty() {
            None
        } else {
            Some(build_type_var_map(kernel_context, type_params))
        }
    }

    fn local_certificate_proposition(value: &AcornValue, type_params: &[TypeParam]) -> Proposition {
        Proposition::new(
            value.clone(),
            type_params.to_vec(),
            Source::anonymous(ModuleId::default(), Default::default(), 1),
        )
    }

    fn claim_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Claim, String> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        let clause = kernel_context.lower_clause(value, NewConstantType::Local, type_var_map)?;
        Claim::new(clause, VariableMap::new())
    }

    fn exact_witness_clauses_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Vec<Clause>, String> {
        let proposition = Self::local_certificate_proposition(value, type_params);
        Ok(kernel_context
            .lower_proposition_to_clauses(&proposition)?
            .into_iter()
            .map(|clause| clause.normalized())
            .collect())
    }

    fn maybe_specialized_clause_for_proposition(
        kernel_context: &mut KernelContext,
        value: &AcornValue,
        type_params: &[TypeParam],
    ) -> Result<Option<Clause>, String> {
        let type_var_map = Self::type_var_map_for_params(kernel_context, type_params);
        let term =
            kernel_context.lower_term(value, NewConstantType::Local, type_var_map.as_ref())?;
        let term = normalize_term(&term);
        let inline_literal_body =
            match kernel_context.term_to_inline_literal_body(&term, type_var_map) {
                Ok(term) => term,
                Err(_) => return Ok(None),
            };
        Ok(Some(
            Clause::from_literals_unnormalized(
                vec![Literal::positive(inline_literal_body)],
                &LocalContext::empty(),
            )
            .normalized(),
        ))
    }

    fn constant_matches_name(constant: &ConstantInstance, name: &str) -> bool {
        matches!(&constant.name, ConstantName::Unqualified(_, local_name) if local_name == name)
    }

    fn variable_witness_general_condition(&self) -> AcornValue {
        let condition = self.condition.clone().insert_stack(0, 1);
        condition.replace_constants(0, &|constant| {
            if Self::constant_matches_name(constant, &self.name) {
                Some(AcornValue::Variable(0, self.return_type.clone()))
            } else {
                None
            }
        })
    }

    fn function_witness_constant_name(
        &self,
        kernel_context: &KernelContext,
    ) -> Result<ConstantName, String> {
        kernel_context
            .symbol_table
            .find_scoped_unqualified_name(&self.name)
            .ok_or_else(|| format!("witness constant '{}' is not registered", self.name))
    }

    fn general_claim_value(&self) -> AcornValue {
        if self.is_function() {
            let arg_types = self
                .arguments
                .iter()
                .map(|(_, arg_type)| arg_type.clone())
                .collect();
            AcornValue::ForAll(
                arg_types,
                Box::new(AcornValue::Exists(
                    vec![self.return_type.clone()],
                    Box::new(self.condition.clone()),
                )),
            )
        } else {
            AcornValue::Exists(
                vec![self.return_type.clone()],
                Box::new(self.variable_witness_general_condition()),
            )
        }
    }

    fn specialized_claim_value(
        &self,
        kernel_context: &KernelContext,
    ) -> Result<AcornValue, String> {
        if !self.is_function() {
            return Ok(self.condition.clone());
        }

        let arg_types: Vec<AcornType> = self
            .arguments
            .iter()
            .map(|(_, arg_type)| arg_type.clone())
            .collect();
        let function_type = AcornType::functional(arg_types.clone(), self.return_type.clone());
        let function_constant = AcornValue::constant(
            self.function_witness_constant_name(kernel_context)?,
            vec![],
            function_type.clone(),
            function_type,
            self.type_params
                .iter()
                .map(|param| param.name.clone())
                .collect(),
            vec![],
        );
        let function_term = AcornValue::apply(
            function_constant,
            arg_types
                .iter()
                .enumerate()
                .map(|(i, arg_type)| AcornValue::Variable(i as AtomId, arg_type.clone()))
                .collect(),
        );
        let num_args = arg_types.len() as AtomId;
        let specialized_condition =
            self.condition
                .clone()
                .bind_values(num_args, num_args, &[function_term]);
        Ok(AcornValue::ForAll(
            arg_types,
            Box::new(specialized_condition),
        ))
    }

    fn same_clause_set(left: &[Clause], right: &[Clause]) -> bool {
        let left: HashSet<_> = left.iter().collect();
        let right: HashSet<_> = right.iter().collect();
        left == right
    }

    /// Recompute the clauses that this witness declaration is allowed to introduce.
    ///
    /// `SatisfyStep` stores display-oriented clauses produced by parsing or certificate
    /// generation. The checker validates them against the declaration payload before trusting
    /// them as proof facts.
    pub fn validate_checker_payload(
        &self,
        kernel_context: &mut KernelContext,
    ) -> Result<(), String> {
        let expected_justification = Self::claim_for_proposition(
            kernel_context,
            &self.general_claim_value(),
            &self.type_params,
        )?;
        if self.justification != expected_justification {
            return Err("witness justification does not match declaration".to_string());
        }

        let specialized_value = self.specialized_claim_value(kernel_context)?;
        let expected_specialized_clause = Self::maybe_specialized_clause_for_proposition(
            kernel_context,
            &specialized_value,
            &self.type_params,
        )?;
        if self.specialized_clause != expected_specialized_clause {
            return Err(format!(
                "witness specialized clause mismatch: expected {:?}, got {:?}",
                expected_specialized_clause, self.specialized_clause
            ));
        }

        let mut expected_witness_clauses = Self::exact_witness_clauses_for_proposition(
            kernel_context,
            &specialized_value,
            &self.type_params,
        )?;
        if !self.is_function() {
            expected_witness_clauses
                .retain(|clause| expected_specialized_clause.as_ref() != Some(clause));
        }
        if !Self::same_clause_set(&self.witness_clauses, &expected_witness_clauses) {
            return Err(format!(
                "witness clauses mismatch: expected {:?}, got {:?}",
                expected_witness_clauses, self.witness_clauses
            ));
        }

        Ok(())
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
    fn test_claim_new_preserves_type_local_used_only_in_var_map_term() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_typeclass("FiniteGroup");
        kernel_context.parse_polymorphic_constant("g0", "T: Type", "Bool -> Bool");
        kernel_context.parse_polymorphic_constant("g1", "T: Type", "T -> Bool");

        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(kernel_context.parse_term("g1(x0, x2)"))],
            &LocalContext::from_types(vec![
                Term::type_sort(),
                kernel_context.parse_type("FiniteGroup"),
                Term::new_variable(0),
            ]),
        );
        let mut var_map = VariableMap::new();
        var_map.set(0, Term::bool_type());
        var_map.set(2, kernel_context.parse_term("g0(x1, false)"));

        let claim = Claim::new(clause, var_map).expect("claim should normalize");

        assert_eq!(
            claim.clause.get_local_context().get_var_type(1),
            Some(&kernel_context.parse_type("FiniteGroup"))
        );
        assert_eq!(
            claim.var_map.get_mapping(2),
            Some(&kernel_context.parse_term("g0(x1, false)"))
        );
        claim
            .validate_normalized_shape(&kernel_context)
            .expect("claim should have normalized shape");
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
