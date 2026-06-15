use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::kernel::atom::AtomId;
use crate::kernel::clause::{BooleanReductionKind, Clause, NormalizedClauseTrace};
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_clause_subterms;
use crate::kernel::{EqualityGraph, StepId};

/// A compact primitive rule name for structured certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StructuredRule {
    Known,
    EqGraph,
    EqRes,
    EqFact,
    Inject,
    Ext,
    FalseLit,
    IteSimpLeft,
    IteSimpRight,
    IteLeftThen,
    IteLeftElse,
    IteRightThen,
    IteRightElse,
    FunNeqToExists,
    SignedNot,
    BoolEqToEq,
    PosForallOpen,
    PosExistsWitness,
    PosExistsOpen,
    NegForallExists,
    NegExistsOpen,
    PosAndLeft,
    PosAndRight,
    NegAnd,
    PosOr,
    NegOrLeft,
    NegOrRight,
    BoolEqLeftNotRight,
    BoolEqNotLeftRight,
    BoolNeqNotLeftNotRight,
    BoolNeqLeftRight,
}

impl StructuredRule {
    pub fn as_str(self) -> &'static str {
        match self {
            StructuredRule::Known => "known",
            StructuredRule::EqGraph => "eqgraph",
            StructuredRule::EqRes => "eq_res",
            StructuredRule::EqFact => "eq_fact",
            StructuredRule::Inject => "inject",
            StructuredRule::Ext => "ext",
            StructuredRule::FalseLit => "false_lit",
            StructuredRule::IteSimpLeft => "ite_simp_left",
            StructuredRule::IteSimpRight => "ite_simp_right",
            StructuredRule::IteLeftThen => "ite_left_then",
            StructuredRule::IteLeftElse => "ite_left_else",
            StructuredRule::IteRightThen => "ite_right_then",
            StructuredRule::IteRightElse => "ite_right_else",
            StructuredRule::FunNeqToExists => "fun_neq_to_exists",
            StructuredRule::SignedNot => "signed_not",
            StructuredRule::BoolEqToEq => "bool_eq_to_eq",
            StructuredRule::PosForallOpen => "pos_forall_open",
            StructuredRule::PosExistsWitness => "pos_exists_witness",
            StructuredRule::PosExistsOpen => "pos_exists_open",
            StructuredRule::NegForallExists => "neg_forall_exists",
            StructuredRule::NegExistsOpen => "neg_exists_open",
            StructuredRule::PosAndLeft => "pos_and_left",
            StructuredRule::PosAndRight => "pos_and_right",
            StructuredRule::NegAnd => "neg_and",
            StructuredRule::PosOr => "pos_or",
            StructuredRule::NegOrLeft => "neg_or_left",
            StructuredRule::NegOrRight => "neg_or_right",
            StructuredRule::BoolEqLeftNotRight => "bool_eq_left_not_right",
            StructuredRule::BoolEqNotLeftRight => "bool_eq_not_left_right",
            StructuredRule::BoolNeqNotLeftNotRight => "bool_neq_not_left_not_right",
            StructuredRule::BoolNeqLeftRight => "bool_neq_left_right",
        }
    }

    pub fn from_boolean_reduction_kind(kind: BooleanReductionKind) -> Self {
        match kind {
            BooleanReductionKind::FalseLiteralElimination => StructuredRule::FalseLit,
            BooleanReductionKind::IteSimplifyLeft => StructuredRule::IteSimpLeft,
            BooleanReductionKind::IteSimplifyRight => StructuredRule::IteSimpRight,
            BooleanReductionKind::IteSplitLeftThenBranch => StructuredRule::IteLeftThen,
            BooleanReductionKind::IteSplitLeftElseBranch => StructuredRule::IteLeftElse,
            BooleanReductionKind::IteSplitRightThenBranch => StructuredRule::IteRightThen,
            BooleanReductionKind::IteSplitRightElseBranch => StructuredRule::IteRightElse,
            BooleanReductionKind::FunctionInequalityToExists => StructuredRule::FunNeqToExists,
            BooleanReductionKind::SignedNot => StructuredRule::SignedNot,
            BooleanReductionKind::BooleanEqToEquality => StructuredRule::BoolEqToEq,
            BooleanReductionKind::PositiveForallOpen => StructuredRule::PosForallOpen,
            BooleanReductionKind::PositiveExistsObviousWitness => StructuredRule::PosExistsWitness,
            BooleanReductionKind::PositiveExistsOpen => StructuredRule::PosExistsOpen,
            BooleanReductionKind::NegatedForallToExists => StructuredRule::NegForallExists,
            BooleanReductionKind::NegatedExistsOpen => StructuredRule::NegExistsOpen,
            BooleanReductionKind::PositiveAndLeft => StructuredRule::PosAndLeft,
            BooleanReductionKind::PositiveAndRight => StructuredRule::PosAndRight,
            BooleanReductionKind::NegativeAnd => StructuredRule::NegAnd,
            BooleanReductionKind::PositiveOr => StructuredRule::PosOr,
            BooleanReductionKind::NegativeOrLeft => StructuredRule::NegOrLeft,
            BooleanReductionKind::NegativeOrRight => StructuredRule::NegOrRight,
            BooleanReductionKind::BooleanEqualityLeftOrNotRight => {
                StructuredRule::BoolEqLeftNotRight
            }
            BooleanReductionKind::BooleanEqualityNotLeftOrRight => {
                StructuredRule::BoolEqNotLeftRight
            }
            BooleanReductionKind::BooleanInequalityNotLeftOrNotRight => {
                StructuredRule::BoolNeqNotLeftNotRight
            }
            BooleanReductionKind::BooleanInequalityLeftOrRight => StructuredRule::BoolNeqLeftRight,
        }
    }

    fn boolean_reduction_kind(self) -> Option<BooleanReductionKind> {
        Some(match self {
            StructuredRule::FalseLit => BooleanReductionKind::FalseLiteralElimination,
            StructuredRule::IteSimpLeft => BooleanReductionKind::IteSimplifyLeft,
            StructuredRule::IteSimpRight => BooleanReductionKind::IteSimplifyRight,
            StructuredRule::IteLeftThen => BooleanReductionKind::IteSplitLeftThenBranch,
            StructuredRule::IteLeftElse => BooleanReductionKind::IteSplitLeftElseBranch,
            StructuredRule::IteRightThen => BooleanReductionKind::IteSplitRightThenBranch,
            StructuredRule::IteRightElse => BooleanReductionKind::IteSplitRightElseBranch,
            StructuredRule::FunNeqToExists => BooleanReductionKind::FunctionInequalityToExists,
            StructuredRule::SignedNot => BooleanReductionKind::SignedNot,
            StructuredRule::BoolEqToEq => BooleanReductionKind::BooleanEqToEquality,
            StructuredRule::PosForallOpen => BooleanReductionKind::PositiveForallOpen,
            StructuredRule::PosExistsWitness => BooleanReductionKind::PositiveExistsObviousWitness,
            StructuredRule::PosExistsOpen => BooleanReductionKind::PositiveExistsOpen,
            StructuredRule::NegForallExists => BooleanReductionKind::NegatedForallToExists,
            StructuredRule::NegExistsOpen => BooleanReductionKind::NegatedExistsOpen,
            StructuredRule::PosAndLeft => BooleanReductionKind::PositiveAndLeft,
            StructuredRule::PosAndRight => BooleanReductionKind::PositiveAndRight,
            StructuredRule::NegAnd => BooleanReductionKind::NegativeAnd,
            StructuredRule::PosOr => BooleanReductionKind::PositiveOr,
            StructuredRule::NegOrLeft => BooleanReductionKind::NegativeOrLeft,
            StructuredRule::NegOrRight => BooleanReductionKind::NegativeOrRight,
            StructuredRule::BoolEqLeftNotRight => {
                BooleanReductionKind::BooleanEqualityLeftOrNotRight
            }
            StructuredRule::BoolEqNotLeftRight => {
                BooleanReductionKind::BooleanEqualityNotLeftOrRight
            }
            StructuredRule::BoolNeqNotLeftNotRight => {
                BooleanReductionKind::BooleanInequalityNotLeftOrNotRight
            }
            StructuredRule::BoolNeqLeftRight => BooleanReductionKind::BooleanInequalityLeftOrRight,
            StructuredRule::Known
            | StructuredRule::EqGraph
            | StructuredRule::EqRes
            | StructuredRule::EqFact
            | StructuredRule::Inject
            | StructuredRule::Ext => return None,
        })
    }
}

impl fmt::Display for StructuredRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl FromStr for StructuredRule {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "known" => Ok(StructuredRule::Known),
            "eqgraph" => Ok(StructuredRule::EqGraph),
            "eq_res" => Ok(StructuredRule::EqRes),
            "eq_fact" => Ok(StructuredRule::EqFact),
            "inject" => Ok(StructuredRule::Inject),
            "ext" => Ok(StructuredRule::Ext),
            "false_lit" => Ok(StructuredRule::FalseLit),
            "ite_simp_left" => Ok(StructuredRule::IteSimpLeft),
            "ite_simp_right" => Ok(StructuredRule::IteSimpRight),
            "ite_left_then" => Ok(StructuredRule::IteLeftThen),
            "ite_left_else" => Ok(StructuredRule::IteLeftElse),
            "ite_right_then" => Ok(StructuredRule::IteRightThen),
            "ite_right_else" => Ok(StructuredRule::IteRightElse),
            "fun_neq_to_exists" => Ok(StructuredRule::FunNeqToExists),
            "signed_not" => Ok(StructuredRule::SignedNot),
            "bool_eq_to_eq" => Ok(StructuredRule::BoolEqToEq),
            "pos_forall_open" => Ok(StructuredRule::PosForallOpen),
            "pos_exists_witness" => Ok(StructuredRule::PosExistsWitness),
            "pos_exists_open" => Ok(StructuredRule::PosExistsOpen),
            "neg_forall_exists" => Ok(StructuredRule::NegForallExists),
            "neg_exists_open" => Ok(StructuredRule::NegExistsOpen),
            "pos_and_left" => Ok(StructuredRule::PosAndLeft),
            "pos_and_right" => Ok(StructuredRule::PosAndRight),
            "neg_and" => Ok(StructuredRule::NegAnd),
            "pos_or" => Ok(StructuredRule::PosOr),
            "neg_or_left" => Ok(StructuredRule::NegOrLeft),
            "neg_or_right" => Ok(StructuredRule::NegOrRight),
            "bool_eq_left_not_right" => Ok(StructuredRule::BoolEqLeftNotRight),
            "bool_eq_not_left_right" => Ok(StructuredRule::BoolEqNotLeftRight),
            "bool_neq_not_left_not_right" => Ok(StructuredRule::BoolNeqNotLeftNotRight),
            "bool_neq_left_right" => Ok(StructuredRule::BoolNeqLeftRight),
            _ => Err(format!("unknown structured certificate rule `{s}`")),
        }
    }
}

impl Serialize for StructuredRule {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for StructuredRule {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        StructuredRule::from_str(&s).map_err(serde::de::Error::custom)
    }
}

/// A kernel-level structured certificate step.
///
/// The eventual JSON adapter should parse optional source strings into `expected` clauses before
/// passing steps to this checker. Keeping source parsing out of the kernel avoids mixing binding
/// lookup and proof validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredProofStep {
    pub rule: StructuredRule,
    pub premises: Vec<usize>,
    pub expected: Option<Clause>,
}

impl StructuredProofStep {
    pub fn new(rule: StructuredRule, premises: Vec<usize>) -> Self {
        Self {
            rule,
            premises,
            expected: None,
        }
    }

    pub fn with_expected(rule: StructuredRule, premises: Vec<usize>, expected: Clause) -> Self {
        Self {
            rule,
            premises,
            expected: Some(expected),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredCheckError {
    message: String,
}

impl StructuredCheckError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for StructuredCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for StructuredCheckError {}

/// A local-step validator for structured certificates.
///
/// This checker does not close clauses under boolean reduction. It validates the named rule for
/// each step against the explicitly referenced premises.
#[derive(Debug, Clone, Default)]
pub struct StructuredChecker {
    known_clauses: HashSet<Clause>,
    clauses: Vec<Clause>,
    proven_inhabited: HashSet<(Term, LocalContext)>,
}

impl StructuredChecker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_known_clause(&mut self, clause: &Clause, kernel_context: &KernelContext) {
        let clause = Self::normalize_input_clause(clause);
        self.mark_inhabited_from_clause(&clause, kernel_context);
        self.known_clauses.insert(clause);
    }

    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    pub fn get_clause(&self, id: usize) -> Option<&Clause> {
        self.clauses.get(id)
    }

    pub fn check_steps(
        &mut self,
        steps: &[StructuredProofStep],
        kernel_context: &KernelContext,
    ) -> Result<(), StructuredCheckError> {
        for step in steps {
            self.check_step(step, kernel_context)?;
        }
        Ok(())
    }

    pub fn check_step(
        &mut self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<usize, StructuredCheckError> {
        let clause = self.derive_step_clause(step, kernel_context)?;
        self.mark_inhabited_from_clause(&clause, kernel_context);
        let id = self.clauses.len();
        self.clauses.push(clause);
        Ok(id)
    }

    fn normalize_input_clause(clause: &Clause) -> Clause {
        normalize_clause_subterms(clause).normalized()
    }

    fn derive_step_clause(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if step.rule == StructuredRule::Known {
            return self.derive_known(step);
        }
        if step.rule == StructuredRule::EqGraph {
            return self.derive_eqgraph(step, kernel_context);
        }

        let candidates = self.derive_candidate_clauses(step, kernel_context)?;
        self.select_candidate(step, candidates)
    }

    fn derive_known(&self, step: &StructuredProofStep) -> Result<Clause, StructuredCheckError> {
        if !step.premises.is_empty() {
            return Err(StructuredCheckError::new(format!(
                "rule {} expects no premises, got {}",
                step.rule,
                step.premises.len()
            )));
        }
        let Some(expected) = &step.expected else {
            return Err(StructuredCheckError::new(
                "known step requires an expected clause",
            ));
        };
        let expected = Self::normalize_input_clause(expected);
        if self.known_clauses.contains(&expected) {
            Ok(expected)
        } else {
            Err(StructuredCheckError::new(format!(
                "known step is not available: {}",
                expected
            )))
        }
    }

    fn derive_eqgraph(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if step.premises.is_empty() {
            return Err(StructuredCheckError::new("eqgraph requires premises"));
        }

        let mut graph = EqualityGraph::new();
        for (i, premise_id) in step.premises.iter().copied().enumerate() {
            let premise = self.premise_clause(premise_id)?;
            graph.insert_clause(premise, StepId(i), kernel_context);
        }

        if let Some(expected) = &step.expected {
            let expected = Self::normalize_input_clause(expected);
            if expected.is_impossible() {
                if graph.has_contradiction() {
                    return Ok(expected);
                }
            } else if graph.check_clause(&expected, kernel_context) {
                return Ok(expected);
            }
            return Err(StructuredCheckError::new(format!(
                "eqgraph did not prove expected clause {}",
                expected
            )));
        }

        if graph.has_contradiction() {
            Ok(Clause::impossible())
        } else {
            Err(StructuredCheckError::new(
                "eqgraph step without an expected clause requires a local contradiction",
            ))
        }
    }

    fn derive_candidate_clauses(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Vec<Clause>, StructuredCheckError> {
        let premise = self.only_premise(step)?;
        let mut candidates = Vec::new();

        if let Some(kind) = step.rule.boolean_reduction_kind() {
            for (candidate_kind, trace) in
                premise.find_boolean_reduction_kinds_with_options(kernel_context, true)
            {
                if candidate_kind == kind {
                    if let Some(clause) = self.normalize_trace(&trace, kernel_context) {
                        candidates.push(clause);
                    }
                }
            }
            return Ok(candidates);
        }

        match step.rule {
            StructuredRule::EqRes => {
                for (literals, context, _) in
                    inference::find_equality_resolutions(premise, kernel_context)
                {
                    let trace = Clause::normalize_with_trace(literals, &context);
                    if let Some(clause) = self.normalize_trace(&trace, kernel_context) {
                        if !clause.is_tautology() {
                            candidates.push(clause);
                        }
                    }
                }
            }
            StructuredRule::EqFact => {
                for (literals, context, _) in
                    inference::find_equality_factorings(premise, kernel_context)
                {
                    let trace = Clause::normalize_with_trace(literals, &context);
                    if let Some(clause) = self.normalize_trace(&trace, kernel_context) {
                        if !clause.is_tautology() {
                            candidates.push(clause);
                        }
                    }
                }
            }
            StructuredRule::Inject => {
                for literals in premise.find_injectivities() {
                    let trace = Clause::normalize_with_trace(literals, premise.get_local_context());
                    if let Some(clause) = self.normalize_trace(&trace, kernel_context) {
                        if !clause.is_tautology() {
                            candidates.push(clause);
                        }
                    }
                }
            }
            StructuredRule::Ext => {
                if let Some(literals) = premise.find_extensionality(kernel_context) {
                    candidates.push(Clause::new(literals, premise.get_local_context()));
                }
            }
            StructuredRule::Known | StructuredRule::EqGraph => unreachable!(),
            _ => {
                return Err(StructuredCheckError::new(format!(
                    "rule {} is not implemented by the structured checker",
                    step.rule
                )));
            }
        }

        Ok(candidates)
    }

    fn select_candidate(
        &self,
        step: &StructuredProofStep,
        candidates: Vec<Clause>,
    ) -> Result<Clause, StructuredCheckError> {
        let mut candidates: Vec<Clause> = candidates
            .into_iter()
            .map(|clause| Self::normalize_input_clause(&clause))
            .collect();
        candidates.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
        candidates.dedup();

        if let Some(expected) = &step.expected {
            let expected = Self::normalize_input_clause(expected);
            if candidates.iter().any(|candidate| candidate == &expected) {
                return Ok(expected);
            }
            return Err(StructuredCheckError::new(format!(
                "rule {} from {:?} did not produce expected clause {}; produced {} candidate(s)",
                step.rule,
                step.premises,
                expected,
                candidates.len()
            )));
        }

        match candidates.len() {
            0 => Err(StructuredCheckError::new(format!(
                "rule {} from {:?} produced no candidates",
                step.rule, step.premises
            ))),
            1 => Ok(candidates.into_iter().next().unwrap()),
            n => Err(StructuredCheckError::new(format!(
                "rule {} from {:?} is ambiguous without an expected clause: {} candidates",
                step.rule, step.premises, n
            ))),
        }
    }

    fn only_premise(&self, step: &StructuredProofStep) -> Result<&Clause, StructuredCheckError> {
        if step.premises.len() != 1 {
            return Err(StructuredCheckError::new(format!(
                "rule {} expects exactly one premise, got {}",
                step.rule,
                step.premises.len()
            )));
        }
        self.premise_clause(step.premises[0])
    }

    fn premise_clause(&self, id: usize) -> Result<&Clause, StructuredCheckError> {
        self.clauses.get(id).ok_or_else(|| {
            StructuredCheckError::new(format!(
                "structured certificate references missing step {}",
                id
            ))
        })
    }

    fn inhabited_type_key(var_type: &Term, context: &LocalContext) -> (Term, LocalContext) {
        let mut normalized_type = var_type.clone();
        let mut var_ids = Vec::new();
        normalized_type.normalize_var_ids_with_context(&mut var_ids, context);
        (normalized_type, context.remap(&var_ids))
    }

    fn inhabited_type_from_clause(
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<(Term, LocalContext)> {
        let reduction = clause.positive_exists_reduction(kernel_context)?;
        Some(Self::inhabited_type_key(
            &reduction.binder_type,
            clause.get_local_context(),
        ))
    }

    fn mark_inhabited_from_clause(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        let Some(key) = Self::inhabited_type_from_clause(clause, kernel_context) else {
            return false;
        };
        self.proven_inhabited.insert(key)
    }

    fn eliminated_vars_inhabited(
        &self,
        trace: &NormalizedClauseTrace,
        kernel_context: &KernelContext,
    ) -> bool {
        for var_id in 0..trace.pre_norm_context.len() {
            let var_id_atom = var_id as AtomId;
            if trace.var_ids.contains(&var_id_atom) {
                continue;
            }
            let Some(var_type) = trace.pre_norm_context.get_var_type(var_id) else {
                continue;
            };
            let proven_inhabited = self
                .proven_inhabited
                .contains(&Self::inhabited_type_key(var_type, &trace.pre_norm_context));
            if !proven_inhabited
                && !kernel_context.provably_inhabited_without_local_elements(
                    var_type,
                    Some(&trace.pre_norm_context),
                )
            {
                return false;
            }
        }
        true
    }

    fn normalize_trace(
        &self,
        trace: &NormalizedClauseTrace,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        if !self.eliminated_vars_inhabited(trace, kernel_context) {
            return None;
        }

        let subterm_normalized = normalize_clause_subterms(&trace.clause);
        let subterm_context = subterm_normalized.get_local_context().clone();
        let first = Clause::normalize_with_trace(subterm_normalized.literals, &subterm_context);
        if !self.eliminated_vars_inhabited(&first, kernel_context) {
            return None;
        }
        let first_context = first.clause.get_local_context().clone();
        let second = Clause::normalize_with_trace(first.clause.literals, &first_context);
        if !self.eliminated_vars_inhabited(&second, kernel_context) {
            return None;
        }
        Some(second.clause)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::literal::Literal;

    fn bool_context() -> KernelContext {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1", "c2", "c3"], "Bool");
        context
    }

    fn positive_and_clause(context: &KernelContext) -> Clause {
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");
        Clause::new(
            vec![Literal::positive(Term::and(c0, c1))],
            &LocalContext::empty(),
        )
    }

    #[test]
    fn structured_rule_names_roundtrip() {
        let rules = [
            StructuredRule::Known,
            StructuredRule::EqGraph,
            StructuredRule::EqRes,
            StructuredRule::EqFact,
            StructuredRule::Inject,
            StructuredRule::Ext,
            StructuredRule::FalseLit,
            StructuredRule::IteSimpLeft,
            StructuredRule::IteSimpRight,
            StructuredRule::IteLeftThen,
            StructuredRule::IteLeftElse,
            StructuredRule::IteRightThen,
            StructuredRule::IteRightElse,
            StructuredRule::FunNeqToExists,
            StructuredRule::SignedNot,
            StructuredRule::BoolEqToEq,
            StructuredRule::PosForallOpen,
            StructuredRule::PosExistsWitness,
            StructuredRule::PosExistsOpen,
            StructuredRule::NegForallExists,
            StructuredRule::NegExistsOpen,
            StructuredRule::PosAndLeft,
            StructuredRule::PosAndRight,
            StructuredRule::NegAnd,
            StructuredRule::PosOr,
            StructuredRule::NegOrLeft,
            StructuredRule::NegOrRight,
            StructuredRule::BoolEqLeftNotRight,
            StructuredRule::BoolEqNotLeftRight,
            StructuredRule::BoolNeqNotLeftNotRight,
            StructuredRule::BoolNeqLeftRight,
        ];

        for rule in rules {
            assert_eq!(StructuredRule::from_str(rule.as_str()).unwrap(), rule);
            let serialized = serde_json::to_string(&rule).unwrap();
            let deserialized: StructuredRule = serde_json::from_str(&serialized).unwrap();
            assert_eq!(deserialized, rule);
        }
        assert_eq!(StructuredRule::NegOrLeft.as_str(), "neg_or_left");
        assert_eq!(StructuredRule::BoolEqToEq.as_str(), "bool_eq_to_eq");
    }

    #[test]
    fn structured_checker_validates_named_boolean_reduction() {
        let context = bool_context();
        let known = positive_and_clause(&context);
        let expected_left = context.parse_clause("c0", &[]);
        let expected_right = context.parse_clause("c1", &[]);

        let mut checker = StructuredChecker::new();
        checker.add_known_clause(&known, &context);
        checker
            .check_step(
                &StructuredProofStep::with_expected(StructuredRule::Known, vec![], known),
                &context,
            )
            .unwrap();
        checker
            .check_step(
                &StructuredProofStep::with_expected(
                    StructuredRule::PosAndLeft,
                    vec![0],
                    expected_left,
                ),
                &context,
            )
            .unwrap();
        let right_id = checker
            .check_step(
                &StructuredProofStep::new(StructuredRule::PosAndRight, vec![0]),
                &context,
            )
            .unwrap();

        assert_eq!(
            checker.get_clause(right_id).unwrap(),
            &StructuredChecker::normalize_input_clause(&expected_right)
        );
    }

    #[test]
    fn structured_checker_rejects_wrong_expected_clause() {
        let context = bool_context();
        let known = positive_and_clause(&context);
        let wrong = context.parse_clause("c1", &[]);

        let mut checker = StructuredChecker::new();
        checker.add_known_clause(&known, &context);
        checker
            .check_step(
                &StructuredProofStep::with_expected(StructuredRule::Known, vec![], known),
                &context,
            )
            .unwrap();

        let err = checker
            .check_step(
                &StructuredProofStep::with_expected(StructuredRule::PosAndLeft, vec![0], wrong),
                &context,
            )
            .unwrap_err();
        assert!(
            err.to_string().contains("did not produce expected clause"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn structured_checker_validates_local_eqgraph_contradiction() {
        let context = bool_context();
        let pos = context.parse_clause("c0", &[]);
        let neg = context.parse_clause("not c0", &[]);

        let mut checker = StructuredChecker::new();
        checker.add_known_clause(&pos, &context);
        checker.add_known_clause(&neg, &context);
        checker
            .check_step(
                &StructuredProofStep::with_expected(StructuredRule::Known, vec![], pos),
                &context,
            )
            .unwrap();
        checker
            .check_step(
                &StructuredProofStep::with_expected(StructuredRule::Known, vec![], neg),
                &context,
            )
            .unwrap();
        let false_id = checker
            .check_step(
                &StructuredProofStep::new(StructuredRule::EqGraph, vec![0, 1]),
                &context,
            )
            .unwrap();

        assert!(checker.get_clause(false_id).unwrap().is_impossible());
    }
}
