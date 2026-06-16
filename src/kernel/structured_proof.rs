use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::{BooleanReductionKind, Clause, NormalizedClauseTrace};
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{PathStep, Term};
use crate::kernel::term_normalization::normalize_clause_subterms;
use crate::kernel::unifier::{Scope, Unifier};
use crate::kernel::variable_map::{apply_to_term, VariableMap};
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
    Resolve,
    Rewrite,
    Specialize,
    MultiRewrite,
    PassiveContra,
    Simplify,
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
            StructuredRule::Resolve => "resolve",
            StructuredRule::Rewrite => "rewrite",
            StructuredRule::Specialize => "specialize",
            StructuredRule::MultiRewrite => "multi_rewrite",
            StructuredRule::PassiveContra => "passive_contra",
            StructuredRule::Simplify => "simplify",
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
            | StructuredRule::Ext
            | StructuredRule::Resolve
            | StructuredRule::Rewrite
            | StructuredRule::Specialize
            | StructuredRule::MultiRewrite
            | StructuredRule::PassiveContra
            | StructuredRule::Simplify => return None,
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
            "resolve" => Ok(StructuredRule::Resolve),
            "rewrite" => Ok(StructuredRule::Rewrite),
            "specialize" => Ok(StructuredRule::Specialize),
            "multi_rewrite" => Ok(StructuredRule::MultiRewrite),
            "passive_contra" => Ok(StructuredRule::PassiveContra),
            "simplify" => Ok(StructuredRule::Simplify),
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
    pub premise_instantiations: Vec<Option<(VariableMap, LocalContext)>>,
    pub details: StructuredProofStepDetails,
}

impl StructuredProofStep {
    pub fn new(rule: StructuredRule, premises: Vec<usize>) -> Self {
        Self {
            rule,
            premises,
            expected: None,
            premise_instantiations: vec![],
            details: StructuredProofStepDetails::default(),
        }
    }

    pub fn with_expected(rule: StructuredRule, premises: Vec<usize>, expected: Clause) -> Self {
        Self {
            rule,
            premises,
            expected: Some(expected),
            premise_instantiations: vec![],
            details: StructuredProofStepDetails::default(),
        }
    }

    pub fn with_premise_instantiations(
        mut self,
        premise_instantiations: Vec<Option<(VariableMap, LocalContext)>>,
    ) -> Self {
        self.premise_instantiations = premise_instantiations;
        self
    }

    pub fn with_details(mut self, details: StructuredProofStepDetails) -> Self {
        self.details = details;
        self
    }
}

/// Explicit rule data needed to check a structured proof step without delegating to the legacy
/// certificate checker.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StructuredProofStepDetails {
    pub boolean: Option<StructuredBooleanHint>,
    pub rewrite: Option<StructuredRewriteHint>,
    pub simplification: Option<StructuredSimplificationHint>,
    pub resolution: Option<StructuredResolutionHint>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuredBooleanHint {
    pub literal_index: usize,
    pub candidate_index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredRewriteHint {
    pub forwards: bool,
    pub target_left: bool,
    pub path: Vec<PathStep>,
    pub use_instantiated_premises: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuredResolutionHint {
    pub left_literal: usize,
    pub right_literal: usize,
    pub flipped: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredSimplificationHint {
    pub removals: Vec<StructuredSimplificationRemoval>,
    pub resolution: Option<StructuredSimplificationResolution>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuredSimplificationRemoval {
    pub original_literal: usize,
    pub simplifier_premise: usize,
    pub simplifier_literal: usize,
    pub flipped: bool,
    pub use_instantiated_simplifier: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuredSimplificationResolution {
    pub original_literal: usize,
    pub simplifier_premise: usize,
    pub simplifier_literal: usize,
    pub flipped: bool,
    pub simplifier_first: bool,
    pub use_instantiated_simplifier: bool,
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

    pub fn complete_and_check_steps(
        &mut self,
        steps: &[StructuredProofStep],
        kernel_context: &KernelContext,
    ) -> Result<Vec<StructuredProofStep>, StructuredCheckError> {
        let mut completed_steps = Vec::with_capacity(steps.len());
        for step in steps {
            let completed = self.complete_step_details(step, kernel_context)?;
            self.check_step(&completed, kernel_context)?;
            completed_steps.push(completed);
        }
        Ok(completed_steps)
    }

    pub fn complete_step_details(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<StructuredProofStep, StructuredCheckError> {
        let mut completed = step.clone();
        self.validate_step_premise_instantiations(&completed, kernel_context)?;
        match completed.rule {
            StructuredRule::Resolve if completed.details.resolution.is_none() => {
                let expected = Self::required_expected_clause(&completed)?;
                completed.details.resolution =
                    Some(self.infer_resolution_hint(&completed, &expected, kernel_context)?);
            }
            StructuredRule::Rewrite if completed.details.rewrite.is_none() => {
                let expected = Self::required_expected_clause(&completed)?;
                completed.details.rewrite =
                    Some(self.infer_rewrite_hint(&completed, &expected, kernel_context)?);
            }
            StructuredRule::Simplify if completed.details.simplification.is_none() => {
                let expected = Self::required_expected_clause(&completed)?;
                completed.details.simplification =
                    Some(self.infer_simplification_hint(&completed, &expected, kernel_context)?);
            }
            rule if rule.boolean_reduction_kind().is_some()
                && rule != StructuredRule::PosExistsOpen
                && completed.details.boolean.is_none() =>
            {
                let expected = Self::required_expected_clause(&completed)?;
                match self.infer_boolean_hint(&completed, &expected, kernel_context) {
                    Ok(hint) => completed.details.boolean = Some(hint),
                    Err(_) if self.expected_matches_any_premise(&completed, &expected)? => {
                        completed.rule = StructuredRule::EqGraph;
                        completed.details = StructuredProofStepDetails::default();
                    }
                    Err(e) => return Err(e),
                }
            }
            _ => {}
        }
        Ok(completed)
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

    fn required_expected_clause(
        step: &StructuredProofStep,
    ) -> Result<Clause, StructuredCheckError> {
        step.expected
            .as_ref()
            .map(Self::normalize_input_clause)
            .ok_or_else(|| {
                StructuredCheckError::new(format!(
                    "rule {} from {:?} requires an expected clause to infer explicit details",
                    step.rule, step.premises
                ))
            })
    }

    fn validate_step_premise_instantiations(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<(), StructuredCheckError> {
        if step.premise_instantiations.is_empty() {
            return Ok(());
        }
        if step.premise_instantiations.len() != step.premises.len() {
            return Err(StructuredCheckError::new(format!(
                "rule {} has {} premises but {} premise instantiations",
                step.rule,
                step.premises.len(),
                step.premise_instantiations.len()
            )));
        }
        for premise_index in 0..step.premise_instantiations.len() {
            if step.premise_instantiations[premise_index].is_some() {
                self.instantiated_premise_clause(step, premise_index, kernel_context)?;
            }
        }
        Ok(())
    }

    fn expected_matches_any_premise(
        &self,
        step: &StructuredProofStep,
        expected: &Clause,
    ) -> Result<bool, StructuredCheckError> {
        for premise_id in step.premises.iter().copied() {
            if Self::normalize_input_clause(self.premise_clause(premise_id)?) == *expected {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn derive_step_clause(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        self.validate_step_premise_instantiations(step, kernel_context)?;
        if step.rule == StructuredRule::Known {
            return self.derive_known(step);
        }
        if step.rule == StructuredRule::EqGraph {
            return self.derive_eqgraph(step, kernel_context);
        }
        if step.rule == StructuredRule::Resolve {
            return self.derive_resolution(step, kernel_context);
        }
        if step.rule == StructuredRule::Rewrite {
            return self.derive_rewrite(step, kernel_context);
        }
        if step.rule == StructuredRule::PosExistsOpen {
            return self.derive_positive_exists_open(step, kernel_context);
        }
        if step.rule == StructuredRule::Specialize {
            return self.derive_specialization(step, kernel_context);
        }
        if step.rule == StructuredRule::PassiveContra {
            return self.derive_passive_contradiction(step, kernel_context);
        }
        if step.rule == StructuredRule::MultiRewrite {
            return self.derive_multi_rewrite(step, kernel_context);
        }
        if step.rule == StructuredRule::Simplify {
            return self.derive_simplification(step, kernel_context);
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

    fn derive_resolution(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if step.premises.len() != 2 {
            return Err(StructuredCheckError::new(format!(
                "resolve expects exactly two premises, got {}",
                step.premises.len()
            )));
        }
        let Some(expected) = &step.expected else {
            return Err(StructuredCheckError::new(
                "resolve requires an expected clause",
            ));
        };
        let expected = Self::normalize_input_clause(expected);
        let short = self.premise_clause(step.premises[0])?;
        let long = self.premise_clause(step.premises[1])?;
        let Some(hint) = step.details.resolution else {
            return Err(StructuredCheckError::new(format!(
                "resolve from {:?} requires explicit resolution details",
                step.premises
            )));
        };
        if hint.left_literal >= short.literals.len() || hint.right_literal >= long.literals.len() {
            return Err(StructuredCheckError::new(format!(
                "resolve details {:?} reference missing literal; short premise {}; long premise {}",
                hint, short, long
            )));
        }
        let Some(candidate) = Self::resolution_candidate(
            short,
            hint.left_literal,
            long,
            hint.right_literal,
            hint.flipped,
            kernel_context,
        ) else {
            return Err(StructuredCheckError::new(format!(
                "resolve details {:?} from {:?} are not unifiable; short premise {}; long premise {}",
                hint, step.premises, short, long
            )));
        };
        if candidate == expected {
            return Ok(expected);
        }

        Err(StructuredCheckError::new(format!(
            "resolve details {:?} from {:?} produced {}, expected {}; short premise {}; long premise {}",
            hint, step.premises, candidate, expected, short, long
        )))
    }

    fn resolution_candidate(
        short: &Clause,
        short_index: usize,
        long: &Clause,
        long_index: usize,
        flipped: bool,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, short.get_local_context());
        unifier.set_input_context(Scope::RIGHT, long.get_local_context());

        let short_literal = &short.literals[short_index];
        let long_literal = &long.literals[long_index];
        let (long_left, long_right) = if flipped {
            (&long_literal.right, &long_literal.left)
        } else {
            (&long_literal.left, &long_literal.right)
        };
        if !unifier.unify(Scope::LEFT, &short_literal.left, Scope::RIGHT, long_left) {
            return None;
        }
        if !unifier.unify(Scope::LEFT, &short_literal.right, Scope::RIGHT, long_right) {
            return None;
        }

        let mut long_remainder = Vec::new();
        for (i, literal) in long.literals.iter().enumerate() {
            if i == long_index {
                continue;
            }
            let (literal, _) = unifier.apply_to_literal(Scope::RIGHT, literal);
            long_remainder.push(literal);
        }

        let mut used_long_remainder = HashSet::new();
        for (i, literal) in short.literals.iter().enumerate() {
            if i == short_index {
                continue;
            }
            let (literal, _) = unifier.apply_to_literal(Scope::LEFT, literal);
            if let Some(match_index) =
                long_remainder
                    .iter()
                    .enumerate()
                    .position(|(j, candidate)| {
                        !used_long_remainder.contains(&j) && candidate == &literal
                    })
            {
                used_long_remainder.insert(match_index);
            } else {
                return None;
            }
        }

        let context = unifier.output_context().clone();
        let normalized = Clause::normalize_with_trace(long_remainder, &context);
        Some(Self::normalize_input_clause(&normalized.clause))
    }

    fn binary_resolution_candidate(
        left: &Clause,
        left_index: usize,
        right: &Clause,
        right_index: usize,
        flipped: bool,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let left_literal = &left.literals[left_index];
        let right_literal = &right.literals[right_index];
        if left_literal.positive == right_literal.positive {
            return None;
        }

        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, left.get_local_context());
        unifier.set_input_context(Scope::RIGHT, right.get_local_context());

        let (right_left, right_right) = if flipped {
            (&right_literal.right, &right_literal.left)
        } else {
            (&right_literal.left, &right_literal.right)
        };
        if !unifier.unify(Scope::LEFT, &left_literal.left, Scope::RIGHT, right_left) {
            return None;
        }
        if !unifier.unify(Scope::LEFT, &left_literal.right, Scope::RIGHT, right_right) {
            return None;
        }

        let mut literals = Vec::new();
        for (i, literal) in left.literals.iter().enumerate() {
            if i == left_index {
                continue;
            }
            let (literal, _) = unifier.apply_to_literal(Scope::LEFT, literal);
            literals.push(literal);
        }
        for (i, literal) in right.literals.iter().enumerate() {
            if i == right_index {
                continue;
            }
            let (literal, _) = unifier.apply_to_literal(Scope::RIGHT, literal);
            literals.push(literal);
        }

        let context = unifier.output_context().clone();
        let normalized = Clause::normalize_with_trace(literals, &context);
        Some(Self::normalize_input_clause(&normalized.clause))
    }

    fn infer_resolution_hint(
        &self,
        step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
    ) -> Result<StructuredResolutionHint, StructuredCheckError> {
        if step.premises.len() != 2 {
            return Err(StructuredCheckError::new(format!(
                "resolve expects exactly two premises, got {}",
                step.premises.len()
            )));
        }
        let short = self.premise_clause(step.premises[0])?;
        let long = self.premise_clause(step.premises[1])?;
        for (short_index, short_literal) in short.literals.iter().enumerate() {
            for (long_index, long_literal) in long.literals.iter().enumerate() {
                if short_literal.positive == long_literal.positive {
                    continue;
                }
                for flipped in [false, true] {
                    let Some(candidate) = Self::resolution_candidate(
                        short,
                        short_index,
                        long,
                        long_index,
                        flipped,
                        kernel_context,
                    ) else {
                        continue;
                    };
                    if &candidate == expected {
                        return Ok(StructuredResolutionHint {
                            left_literal: short_index,
                            right_literal: long_index,
                            flipped,
                        });
                    }
                }
            }
        }
        Err(StructuredCheckError::new(format!(
            "could not infer resolution details for {:?}; expected {}; short premise {}; long premise {}",
            step.premises, expected, short, long
        )))
    }

    fn infer_boolean_hint(
        &self,
        step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
    ) -> Result<StructuredBooleanHint, StructuredCheckError> {
        let Some(kind) = step.rule.boolean_reduction_kind() else {
            return Err(StructuredCheckError::new(format!(
                "rule {} is not a boolean reduction",
                step.rule
            )));
        };
        let premise = self.first_premise(step)?;
        let mut seen_for_literal = Vec::<(usize, usize)>::new();
        for (candidate_kind, literal_index, trace) in
            premise.find_boolean_reduction_kinds_with_locations_with_options(kernel_context, true)
        {
            if candidate_kind != kind {
                continue;
            }
            let candidate_index = match seen_for_literal
                .iter_mut()
                .find(|(seen_literal_index, _)| *seen_literal_index == literal_index)
            {
                Some((_, count)) => {
                    let current = *count;
                    *count += 1;
                    current
                }
                None => {
                    seen_for_literal.push((literal_index, 1));
                    0
                }
            };
            let Some(candidate) = self.normalize_trace(&trace, kernel_context) else {
                continue;
            };
            if &candidate == expected {
                return Ok(StructuredBooleanHint {
                    literal_index,
                    candidate_index,
                });
            }
        }
        Err(StructuredCheckError::new(format!(
            "could not infer boolean-reduction details for rule {} from {:?}; expected {}; premise {}",
            step.rule, step.premises, expected, premise
        )))
    }

    fn infer_rewrite_hint(
        &self,
        step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
    ) -> Result<StructuredRewriteHint, StructuredCheckError> {
        if step.premises.len() != 2 {
            return Err(StructuredCheckError::new(format!(
                "rewrite expects exactly two premises, got {}",
                step.premises.len()
            )));
        }
        let pattern = self.premise_clause(step.premises[0])?;
        let target = self.premise_clause(step.premises[1])?;
        let rewrite_seed = step
            .premise_instantiations
            .first()
            .and_then(|instantiation| instantiation.as_ref())
            .map(|(var_map, _)| var_map.clone());
        if let Some(hint) = Self::infer_rewrite_hint_with_clauses(
            step,
            expected,
            kernel_context,
            pattern,
            target,
            rewrite_seed.as_ref(),
            false,
        ) {
            return Ok(hint);
        }
        let instantiated_pattern = self.instantiated_premise_clause(step, 0, kernel_context)?;
        let instantiated_target = self.instantiated_premise_clause(step, 1, kernel_context)?;
        if let Some(hint) = Self::infer_rewrite_hint_with_clauses(
            step,
            expected,
            kernel_context,
            &instantiated_pattern,
            &instantiated_target,
            None,
            true,
        ) {
            return Ok(hint);
        }
        Err(StructuredCheckError::new(format!(
            "could not infer rewrite details for {:?}; expected {}; pattern {}; target {}; instantiated pattern {}; instantiated target {}",
            step.premises, expected, pattern, target, instantiated_pattern, instantiated_target
        )))
    }

    fn infer_rewrite_hint_with_clauses(
        _step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
        pattern: &Clause,
        target: &Clause,
        rewrite_seed: Option<&VariableMap>,
        use_instantiated_premises: bool,
    ) -> Option<StructuredRewriteHint> {
        if pattern.literals.len() != 1 || target.literals.len() != 1 {
            return None;
        }
        let pattern_literal = &pattern.literals[0];
        if !pattern_literal.positive {
            return None;
        }
        let target_literal = &target.literals[0];
        for (forwards, old_subterm, new_subterm) in [
            (true, &pattern_literal.left, &pattern_literal.right),
            (false, &pattern_literal.right, &pattern_literal.left),
        ] {
            for target_left in [true, false] {
                let target_term = if target_left {
                    &target_literal.left
                } else {
                    &target_literal.right
                };
                for (path, subterm) in Self::rewritable_subterms_with_paths(target_term) {
                    let mut candidate_maps = vec![VariableMap::new()];
                    if let Some(seed) = rewrite_seed {
                        if seed.len() > 0 {
                            candidate_maps.push(seed.clone());
                        }
                    }
                    for mut var_map in candidate_maps {
                        if !Self::match_rewrite_subterm(
                            old_subterm,
                            &subterm,
                            pattern.get_local_context(),
                            target.get_local_context(),
                            kernel_context,
                            &mut var_map,
                        ) {
                            continue;
                        }
                        if Self::rewrite_matches_expected_subterm(
                            old_subterm,
                            new_subterm,
                            &subterm,
                            target_literal,
                            expected,
                            target_left,
                            &path,
                            pattern.get_local_context(),
                            target.get_local_context(),
                            kernel_context,
                            var_map.clone(),
                        ) {
                            return Some(StructuredRewriteHint {
                                forwards,
                                target_left,
                                path,
                                use_instantiated_premises,
                            });
                        }
                        let replacement = apply_to_term(new_subterm.as_ref(), &var_map);
                        let (candidate_literal, _) =
                            target_literal.replace_at_path(target_left, &path, replacement);
                        let candidate_literal = Literal::new(
                            candidate_literal.positive,
                            kernel_context.canonicalize_instance_calls(&candidate_literal.left),
                            kernel_context.canonicalize_instance_calls(&candidate_literal.right),
                        );
                        let context = Self::rewrite_context(
                            target.get_local_context(),
                            pattern.get_local_context(),
                            &var_map,
                        );
                        if !Self::literal_context_is_complete(&candidate_literal, &context) {
                            continue;
                        }
                        let normalized =
                            Clause::normalize_with_trace(vec![candidate_literal], &context);
                        let candidate = Self::normalize_input_clause(&normalized.clause);
                        if &candidate == expected {
                            return Some(StructuredRewriteHint {
                                forwards,
                                target_left,
                                path,
                                use_instantiated_premises,
                            });
                        }
                    }
                }
            }
        }
        None
    }

    fn derive_rewrite(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if step.premises.len() != 2 {
            return Err(StructuredCheckError::new(format!(
                "rewrite expects exactly two premises, got {}",
                step.premises.len()
            )));
        }
        let Some(expected) = &step.expected else {
            return Err(StructuredCheckError::new(
                "rewrite requires an expected clause",
            ));
        };
        let expected = Self::normalize_input_clause(expected);

        self.derive_rewrite_direct(step, &expected, kernel_context)?;
        Ok(expected)
    }

    fn derive_rewrite_direct(
        &self,
        step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
    ) -> Result<(), StructuredCheckError> {
        let Some(hint) = step.details.rewrite.as_ref() else {
            return Err(StructuredCheckError::new(format!(
                "rewrite from {:?} requires explicit rewrite details",
                step.premises
            )));
        };
        let raw_pattern = self.premise_clause(step.premises[0])?;
        let raw_target = self.premise_clause(step.premises[1])?;
        let rewrite_seed = step
            .premise_instantiations
            .first()
            .and_then(|instantiation| instantiation.as_ref())
            .map(|(var_map, _)| var_map.clone());

        if hint.use_instantiated_premises {
            let instantiated_pattern = self.instantiated_premise_clause(step, 0, kernel_context)?;
            let instantiated_target = self.instantiated_premise_clause(step, 1, kernel_context)?;
            Self::derive_rewrite_direct_with_clauses(
                step,
                expected,
                kernel_context,
                &instantiated_pattern,
                &instantiated_target,
                None,
                hint,
            )
        } else {
            Self::derive_rewrite_direct_with_clauses(
                step,
                expected,
                kernel_context,
                raw_pattern,
                raw_target,
                rewrite_seed.as_ref(),
                hint,
            )
        }
    }

    fn derive_rewrite_direct_with_clauses(
        step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
        pattern: &Clause,
        target: &Clause,
        rewrite_seed: Option<&VariableMap>,
        hint: &StructuredRewriteHint,
    ) -> Result<(), StructuredCheckError> {
        if pattern.literals.len() != 1 || target.literals.len() != 1 {
            return Err(StructuredCheckError::new(format!(
                "rewrite expects single-literal premises, got pattern {} and target {}",
                pattern, target
            )));
        }

        let pattern_literal = &pattern.literals[0];
        if !pattern_literal.positive {
            return Err(StructuredCheckError::new(format!(
                "rewrite pattern is not an equality: {}",
                pattern
            )));
        }
        let target_literal = &target.literals[0];

        let (old_subterm, new_subterm) = if hint.forwards {
            (&pattern_literal.left, &pattern_literal.right)
        } else {
            (&pattern_literal.right, &pattern_literal.left)
        };
        let target_term = if hint.target_left {
            &target_literal.left
        } else {
            &target_literal.right
        };
        let Some(subterm) = target_term.get_term_at_path(&hint.path) else {
            return Err(StructuredCheckError::new(format!(
                "rewrite path {:?} is invalid for target {}",
                hint.path, target
            )));
        };
        let mut candidate_maps = vec![VariableMap::new()];
        if let Some(seed) = rewrite_seed {
            if seed.len() > 0 {
                candidate_maps.push(seed.clone());
            }
        }
        for mut var_map in candidate_maps {
            if !Self::match_rewrite_subterm(
                old_subterm,
                &subterm,
                pattern.get_local_context(),
                target.get_local_context(),
                kernel_context,
                &mut var_map,
            ) {
                continue;
            }
            if Self::rewrite_matches_expected_subterm(
                old_subterm,
                new_subterm,
                &subterm,
                target_literal,
                expected,
                hint.target_left,
                &hint.path,
                pattern.get_local_context(),
                target.get_local_context(),
                kernel_context,
                var_map.clone(),
            ) {
                return Ok(());
            }
            let replacement = apply_to_term(new_subterm.as_ref(), &var_map);
            let (candidate_literal, _) =
                target_literal.replace_at_path(hint.target_left, &hint.path, replacement);
            let candidate_literal = Literal::new(
                candidate_literal.positive,
                kernel_context.canonicalize_instance_calls(&candidate_literal.left),
                kernel_context.canonicalize_instance_calls(&candidate_literal.right),
            );
            let context = Self::rewrite_context(
                target.get_local_context(),
                pattern.get_local_context(),
                &var_map,
            );
            if !Self::literal_context_is_complete(&candidate_literal, &context) {
                continue;
            }
            let normalized = Clause::normalize_with_trace(vec![candidate_literal], &context);
            let candidate = Self::normalize_input_clause(&normalized.clause);
            if &candidate == expected {
                return Ok(());
            }
        }

        Err(StructuredCheckError::new(format!(
            "rewrite from {:?} with details {:?} did not reconstruct expected clause {}; pattern {}; target {}",
            step.premises, hint, expected, pattern, target
        )))
    }

    fn rewrite_matches_expected_subterm(
        old_subterm: &Term,
        new_subterm: &Term,
        target_subterm: &Term,
        target_literal: &Literal,
        expected: &Clause,
        target_left: bool,
        path: &[PathStep],
        pattern_context: &LocalContext,
        target_context: &LocalContext,
        kernel_context: &KernelContext,
        mut var_map: VariableMap,
    ) -> bool {
        if expected.literals.len() != 1 {
            return false;
        }
        let expected_literal = &expected.literals[0];
        let Some(expected_subterm) = expected_literal.get_term_at_path(target_left, path) else {
            return false;
        };
        let (rewritten_literal, _) =
            target_literal.replace_at_path(target_left, path, expected_subterm.clone());
        if rewritten_literal != *expected_literal {
            return false;
        }
        if !Self::match_rewrite_subterm(
            old_subterm,
            target_subterm,
            pattern_context,
            target_context,
            kernel_context,
            &mut var_map,
        ) {
            return false;
        }
        Self::match_rewrite_subterm(
            new_subterm,
            &expected_subterm,
            pattern_context,
            expected.get_local_context(),
            kernel_context,
            &mut var_map,
        )
    }

    fn match_rewrite_subterm(
        general: &Term,
        special: &Term,
        general_context: &LocalContext,
        special_context: &LocalContext,
        kernel_context: &KernelContext,
        var_map: &mut VariableMap,
    ) -> bool {
        let mut typed_map = var_map.clone();
        if typed_map.match_terms(
            general.as_ref(),
            special.as_ref(),
            general_context,
            special_context,
            kernel_context,
        ) {
            *var_map = typed_map;
        } else {
            let mut structural_map = var_map.clone();
            if !structural_map.match_terms_no_type_check(general.as_ref(), special.as_ref()) {
                return false;
            }
            *var_map = structural_map;
        }
        let _ = Self::infer_rewrite_type_bindings(
            var_map,
            general_context,
            special_context,
            kernel_context,
        );
        true
    }

    fn infer_rewrite_type_bindings(
        var_map: &mut VariableMap,
        general_context: &LocalContext,
        special_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        let mut inferred = var_map.clone();
        let bindings: Vec<(usize, Term)> = var_map
            .iter()
            .map(|(var_id, term)| (var_id, term.clone()))
            .collect();
        for (var_id, term) in bindings {
            let Some(var_type) = general_context.get_var_type(var_id) else {
                continue;
            };
            let Ok(special_type) = term.checked_type_with_context(special_context, kernel_context)
            else {
                // Some rewrite matches happen under binders or through type-level terms whose
                // replacement type is not independently checkable in the target context. The
                // structural match is still useful; skip only this inferred type binding.
                continue;
            };
            if !inferred.match_terms(
                var_type.as_ref(),
                special_type.as_ref(),
                general_context,
                special_context,
                kernel_context,
            ) {
                let mut structurally_inferred = inferred.clone();
                let general_literal = Literal::positive(var_type.clone());
                let special_literal = Literal::positive(special_type);
                if !structurally_inferred.match_literal(&general_literal, &special_literal, false) {
                    return true;
                }
                inferred = structurally_inferred;
            }
        }
        *var_map = inferred;
        true
    }

    fn rewrite_context(
        target_context: &LocalContext,
        pattern_context: &LocalContext,
        var_map: &VariableMap,
    ) -> LocalContext {
        let mut context = target_context.clone();
        for (i, var_type) in pattern_context.get_var_types().iter().enumerate() {
            if var_map.has_mapping(i as AtomId) {
                continue;
            }
            if let Some(var_type) = var_type {
                context.set_type(i, var_type.clone());
            }
        }
        context
    }

    fn rewritable_subterms_with_paths(term: &Term) -> Vec<(Vec<PathStep>, Term)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        Self::push_rewritable_subterms_with_paths(term, &mut prefix, &mut answer);
        answer
    }

    fn push_rewritable_subterms_with_paths(
        term: &Term,
        prefix: &mut Vec<PathStep>,
        answer: &mut Vec<(Vec<PathStep>, Term)>,
    ) {
        if term.is_true() {
            return;
        }
        if let Some((func, arg)) = term.as_ref().split_application() {
            prefix.push(PathStep::Function);
            Self::push_rewritable_subterms_with_paths(&func.to_owned(), prefix, answer);
            prefix.pop();

            prefix.push(PathStep::Argument);
            Self::push_rewritable_subterms_with_paths(&arg.to_owned(), prefix, answer);
            prefix.pop();
        }
        answer.push((prefix.clone(), term.clone()));
    }

    fn derive_positive_exists_open(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        let Some(expected) = &step.expected else {
            return Err(StructuredCheckError::new(
                "pos_exists_open requires an expected clause",
            ));
        };
        let expected = Self::normalize_input_clause(expected);
        let source = self.first_premise(step)?;
        for premise_id in step.premises.iter().copied().skip(1) {
            self.premise_clause(premise_id)?;
        }

        let Some(reduction) = source.positive_exists_reduction(kernel_context) else {
            return Err(StructuredCheckError::new(format!(
                "pos_exists_open premise is not an openable positive exists: {}",
                source
            )));
        };
        let mut context = source.get_local_context().clone();
        let witness_id = context.len() as AtomId;
        context.set_type(witness_id as usize, reduction.binder_type);
        let opened = reduction.body.open_bound(&Term::new_variable(witness_id));
        let generic =
            Self::normalize_input_clause(&Clause::new(vec![Literal::positive(opened)], &context));

        if Self::clause_is_instance(&generic, &expected, kernel_context) {
            Ok(expected)
        } else {
            Err(StructuredCheckError::new(format!(
                "pos_exists_open from {:?} did not prove expected clause {}; generic opened clause {}",
                step.premises, expected, generic
            )))
        }
    }

    fn derive_specialization(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if step.premises.len() != 1 {
            return Err(StructuredCheckError::new(format!(
                "specialize expects exactly one premise, got {}",
                step.premises.len()
            )));
        }
        let Some(expected) = &step.expected else {
            return Err(StructuredCheckError::new(
                "specialize requires an expected clause",
            ));
        };
        let expected = Self::normalize_input_clause(expected);
        let premise = self.premise_clause(step.premises[0])?;
        if Self::clause_is_instance(premise, &expected, kernel_context) {
            Ok(expected)
        } else {
            Err(StructuredCheckError::new(format!(
                "specialize from {:?} did not prove expected clause {}; premise {}",
                step.premises, expected, premise
            )))
        }
    }

    fn clause_is_instance(
        general: &Clause,
        special: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        if general.literals.len() != special.literals.len() {
            return false;
        }
        let mut var_map = VariableMap::new();
        for (general_lit, special_lit) in general.literals.iter().zip(&special.literals) {
            if general_lit.positive != special_lit.positive {
                return false;
            }
            let mut typed_unflipped_map = var_map.clone();
            if Self::match_literal_instance(
                &mut typed_unflipped_map,
                general_lit,
                special_lit,
                general.get_local_context(),
                special.get_local_context(),
                false,
                kernel_context,
            ) {
                var_map = typed_unflipped_map;
                continue;
            }
            let mut typed_flipped_map = var_map.clone();
            if Self::match_literal_instance(
                &mut typed_flipped_map,
                general_lit,
                special_lit,
                general.get_local_context(),
                special.get_local_context(),
                true,
                kernel_context,
            ) {
                var_map = typed_flipped_map;
                continue;
            }
            let mut unflipped_map = var_map.clone();
            if unflipped_map.match_literal(general_lit, special_lit, false) {
                var_map = unflipped_map;
                continue;
            }
            let mut flipped_map = var_map.clone();
            if flipped_map.match_literal(general_lit, special_lit, true) {
                var_map = flipped_map;
                continue;
            } else {
                return false;
            }
        }
        true
    }

    fn match_literal_instance(
        var_map: &mut VariableMap,
        general: &Literal,
        special: &Literal,
        general_context: &LocalContext,
        special_context: &LocalContext,
        flipped: bool,
        kernel_context: &KernelContext,
    ) -> bool {
        if general.is_signed_term() && special.is_signed_term() {
            return var_map.match_terms(
                general.left.as_ref(),
                special.left.as_ref(),
                general_context,
                special_context,
                kernel_context,
            );
        }
        if flipped {
            var_map.match_terms(
                general.left.as_ref(),
                special.right.as_ref(),
                general_context,
                special_context,
                kernel_context,
            ) && var_map.match_terms(
                general.right.as_ref(),
                special.left.as_ref(),
                general_context,
                special_context,
                kernel_context,
            )
        } else {
            var_map.match_terms(
                general.left.as_ref(),
                special.left.as_ref(),
                general_context,
                special_context,
                kernel_context,
            ) && var_map.match_terms(
                general.right.as_ref(),
                special.right.as_ref(),
                general_context,
                special_context,
                kernel_context,
            )
        }
    }

    fn infer_simplification_hint(
        &self,
        step: &StructuredProofStep,
        expected: &Clause,
        kernel_context: &KernelContext,
    ) -> Result<StructuredSimplificationHint, StructuredCheckError> {
        if step.premises.len() < 2 {
            return Err(StructuredCheckError::new(format!(
                "simplify expects an original premise and at least one simplifying premise, got {}",
                step.premises.len()
            )));
        }
        let original = self.premise_clause(step.premises[0])?;
        let mut removals = Vec::new();
        let mut removed = vec![false; original.literals.len()];

        for (original_index, original_literal) in original.literals.iter().enumerate() {
            let mut removal = None;
            'premises: for premise_index in 1..step.premises.len() {
                let raw_simplifier = Self::normalize_input_clause(
                    self.premise_clause(step.premises[premise_index])?,
                );
                for (use_instantiated_simplifier, simplifier) in [
                    (false, raw_simplifier.clone()),
                    (
                        true,
                        self.instantiated_premise_clause(step, premise_index, kernel_context)?,
                    ),
                ] {
                    if use_instantiated_simplifier && simplifier == raw_simplifier {
                        continue;
                    }
                    if simplifier.literals.len() != 1 {
                        continue;
                    }
                    for flipped in [false, true] {
                        if Self::literals_can_resolve_with_flipped(
                            &simplifier,
                            0,
                            original,
                            original_literal,
                            flipped,
                            kernel_context,
                        ) {
                            removal = Some(StructuredSimplificationRemoval {
                                original_literal: original_index,
                                simplifier_premise: premise_index,
                                simplifier_literal: 0,
                                flipped,
                                use_instantiated_simplifier,
                            });
                            break 'premises;
                        }
                    }
                }
            }
            if let Some(removal) = removal {
                removed[original_index] = true;
                removals.push(removal);
            }
        }

        let kept_literals: Vec<_> = original
            .literals
            .iter()
            .enumerate()
            .filter_map(|(i, literal)| (!removed[i]).then_some(literal.clone()))
            .collect();
        let normalized = Clause::normalize_with_trace(kept_literals, original.get_local_context());
        let candidate = Self::normalize_input_clause(&normalized.clause);
        if &candidate == expected {
            return Ok(StructuredSimplificationHint {
                removals,
                resolution: None,
            });
        }

        for premise_index in 1..step.premises.len() {
            let raw_simplifier =
                Self::normalize_input_clause(self.premise_clause(step.premises[premise_index])?);
            for (use_instantiated_simplifier, simplifier) in [
                (false, raw_simplifier.clone()),
                (
                    true,
                    self.instantiated_premise_clause(step, premise_index, kernel_context)?,
                ),
            ] {
                if use_instantiated_simplifier && simplifier == raw_simplifier {
                    continue;
                }
                if let Some(mut resolution) = Self::infer_simplification_resolution(
                    original,
                    &simplifier,
                    expected,
                    kernel_context,
                ) {
                    resolution.simplifier_premise = premise_index;
                    resolution.use_instantiated_simplifier = use_instantiated_simplifier;
                    return Ok(StructuredSimplificationHint {
                        removals: vec![],
                        resolution: Some(resolution),
                    });
                }
            }
        }

        Err(StructuredCheckError::new(format!(
            "could not infer simplification details for {:?}; expected {}; original {}; direct removal candidate {}",
            step.premises, expected, original, candidate
        )))
    }

    fn derive_simplification(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        let Some(expected) = &step.expected else {
            return Err(StructuredCheckError::new(
                "simplify requires an expected clause",
            ));
        };
        let expected = Self::normalize_input_clause(expected);
        if step.premises.len() < 2 {
            return Err(StructuredCheckError::new(format!(
                "simplify expects an original premise and at least one simplifying premise, got {}",
                step.premises.len()
            )));
        }
        let Some(hint) = step.details.simplification.as_ref() else {
            return Err(StructuredCheckError::new(format!(
                "simplify from {:?} requires explicit simplification details",
                step.premises
            )));
        };

        let original = self.premise_clause(step.premises[0])?;
        if let Some(resolution) = hint.resolution {
            let simplifier = self.simplification_hint_clause(
                step,
                resolution.simplifier_premise,
                resolution.use_instantiated_simplifier,
                kernel_context,
            )?;
            let candidate = if resolution.simplifier_first {
                Self::binary_resolution_candidate(
                    &simplifier,
                    resolution.simplifier_literal,
                    original,
                    resolution.original_literal,
                    resolution.flipped,
                    kernel_context,
                )
            } else {
                Self::binary_resolution_candidate(
                    original,
                    resolution.original_literal,
                    &simplifier,
                    resolution.simplifier_literal,
                    resolution.flipped,
                    kernel_context,
                )
            };
            if candidate.as_ref() == Some(&expected) {
                return Ok(expected);
            }
            return Err(StructuredCheckError::new(format!(
                "simplify resolution details {:?} from {:?} did not produce expected clause {}",
                resolution, step.premises, expected
            )));
        }

        let mut removed = vec![false; original.literals.len()];
        for removal in &hint.removals {
            if removal.original_literal >= original.literals.len() {
                return Err(StructuredCheckError::new(format!(
                    "simplify removal references missing original literal {} in {}",
                    removal.original_literal, original
                )));
            }
            if removed[removal.original_literal] {
                return Err(StructuredCheckError::new(format!(
                    "simplify removes original literal {} more than once",
                    removal.original_literal
                )));
            }
            let simplifier = self.simplification_hint_clause(
                step,
                removal.simplifier_premise,
                removal.use_instantiated_simplifier,
                kernel_context,
            )?;
            if removal.simplifier_literal >= simplifier.literals.len() {
                return Err(StructuredCheckError::new(format!(
                    "simplify removal references missing simplifier literal {} in {}",
                    removal.simplifier_literal, simplifier
                )));
            }
            if !Self::literals_can_resolve_with_flipped(
                &simplifier,
                removal.simplifier_literal,
                original,
                &original.literals[removal.original_literal],
                removal.flipped,
                kernel_context,
            ) {
                return Err(StructuredCheckError::new(format!(
                    "simplify removal {:?} does not resolve original literal {} against simplifier {}",
                    removal, original.literals[removal.original_literal], simplifier
                )));
            }
            removed[removal.original_literal] = true;
        }

        let kept_literals: Vec<_> = original
            .literals
            .iter()
            .enumerate()
            .filter_map(|(i, literal)| (!removed[i]).then_some(literal.clone()))
            .collect();
        let normalized = Clause::normalize_with_trace(kept_literals, original.get_local_context());
        let candidate = Self::normalize_input_clause(&normalized.clause);
        if candidate == expected {
            return Ok(expected);
        }
        Err(StructuredCheckError::new(format!(
            "simplify removals {:?} from {:?} produced {}, expected {}",
            hint.removals, step.premises, candidate, expected
        )))
    }

    fn simplification_hint_clause(
        &self,
        step: &StructuredProofStep,
        premise_index: usize,
        use_instantiated: bool,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if premise_index == 0 || premise_index >= step.premises.len() {
            return Err(StructuredCheckError::new(format!(
                "simplify detail references invalid simplifier premise index {}",
                premise_index
            )));
        }
        if use_instantiated {
            self.instantiated_premise_clause(step, premise_index, kernel_context)
        } else {
            Ok(Self::normalize_input_clause(
                self.premise_clause(step.premises[premise_index])?,
            ))
        }
    }

    fn infer_simplification_resolution(
        original: &Clause,
        simplifier: &Clause,
        expected: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StructuredSimplificationResolution> {
        for original_index in 0..original.literals.len() {
            for simplifier_index in 0..simplifier.literals.len() {
                for flipped in [false, true] {
                    if let Some(candidate) = Self::binary_resolution_candidate(
                        original,
                        original_index,
                        simplifier,
                        simplifier_index,
                        flipped,
                        kernel_context,
                    ) {
                        if &candidate == expected {
                            return Some(StructuredSimplificationResolution {
                                original_literal: original_index,
                                simplifier_premise: 0,
                                simplifier_literal: simplifier_index,
                                flipped,
                                simplifier_first: false,
                                use_instantiated_simplifier: false,
                            });
                        }
                    }
                    if let Some(candidate) = Self::binary_resolution_candidate(
                        simplifier,
                        simplifier_index,
                        original,
                        original_index,
                        flipped,
                        kernel_context,
                    ) {
                        if &candidate == expected {
                            return Some(StructuredSimplificationResolution {
                                original_literal: original_index,
                                simplifier_premise: 0,
                                simplifier_literal: simplifier_index,
                                flipped,
                                simplifier_first: true,
                                use_instantiated_simplifier: false,
                            });
                        }
                    }
                }
            }
        }
        None
    }

    fn derive_passive_contradiction(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        let expected = step
            .expected
            .as_ref()
            .map(Self::normalize_input_clause)
            .unwrap_or_else(Clause::impossible);
        if !expected.is_impossible() {
            return Err(StructuredCheckError::new(format!(
                "passive_contra requires an impossible expected clause, got {}",
                expected
            )));
        }
        if step.premises.len() < 2 {
            return Err(StructuredCheckError::new(format!(
                "passive_contra expects at least two premises, got {}",
                step.premises.len()
            )));
        }

        let mut premises = Vec::new();
        for premise_id in step.premises.iter().copied() {
            let premise = self.premise_clause(premise_id)?;
            if premise.is_impossible() {
                return Ok(expected);
            }
            premises.push(premise);
        }

        for i in 0..premises.len() {
            for j in (i + 1)..premises.len() {
                if Self::clauses_are_passive_contradiction(premises[i], premises[j], kernel_context)
                {
                    return Ok(expected);
                }
            }
        }

        Err(StructuredCheckError::new(format!(
            "passive_contra from {:?} did not find an explicit contradiction",
            step.premises
        )))
    }

    fn derive_multi_rewrite(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        let expected = step
            .expected
            .as_ref()
            .map(Self::normalize_input_clause)
            .unwrap_or_else(Clause::impossible);
        if !expected.is_impossible() {
            return Err(StructuredCheckError::new(format!(
                "multi_rewrite requires an impossible expected clause, got {}",
                expected
            )));
        }
        if step.premises.is_empty() {
            return Err(StructuredCheckError::new("multi_rewrite requires premises"));
        }
        let mut graph = EqualityGraph::new();
        for (i, premise_id) in step.premises.iter().copied().enumerate() {
            let premise = self.premise_clause(premise_id)?;
            graph.insert_clause(premise, StepId(i), kernel_context);
        }
        if graph.has_contradiction() {
            Ok(expected)
        } else {
            Err(StructuredCheckError::new(format!(
                "multi_rewrite from {:?} did not produce an equality-graph contradiction",
                step.premises
            )))
        }
    }

    fn clauses_are_passive_contradiction(
        left: &Clause,
        right: &Clause,
        kernel_context: &KernelContext,
    ) -> bool {
        if left.literals.len() != 1 || right.literals.len() != 1 {
            return false;
        }
        if !Self::clause_context_provably_inhabited(left, kernel_context)
            || !Self::clause_context_provably_inhabited(right, kernel_context)
        {
            return false;
        }
        let left_lit = &left.literals[0];
        let right_lit = &right.literals[0];
        if left_lit.positive == right_lit.positive {
            return false;
        }
        (left_lit.left == right_lit.left && left_lit.right == right_lit.right)
            || (left_lit.left == right_lit.right && left_lit.right == right_lit.left)
    }

    fn clause_context_provably_inhabited(clause: &Clause, kernel_context: &KernelContext) -> bool {
        let context = clause.get_local_context();
        (0..context.len()).all(|i| {
            context
                .get_var_type(i)
                .is_none_or(|var_type| kernel_context.provably_inhabited(var_type, Some(context)))
        })
    }

    fn literals_can_resolve_with_flipped(
        short: &Clause,
        short_index: usize,
        long: &Clause,
        long_literal: &Literal,
        flipped: bool,
        kernel_context: &KernelContext,
    ) -> bool {
        if short.literals[short_index].positive == long_literal.positive {
            return false;
        }
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, short.get_local_context());
        unifier.set_input_context(Scope::RIGHT, long.get_local_context());
        let short_literal = &short.literals[short_index];
        let (long_left, long_right) = if flipped {
            (&long_literal.right, &long_literal.left)
        } else {
            (&long_literal.left, &long_literal.right)
        };
        if unifier.unify(Scope::LEFT, &short_literal.left, Scope::RIGHT, long_left)
            && unifier.unify(Scope::LEFT, &short_literal.right, Scope::RIGHT, long_right)
        {
            return true;
        }
        false
    }

    fn instantiated_premise_clause(
        &self,
        step: &StructuredProofStep,
        premise_index: usize,
        kernel_context: &KernelContext,
    ) -> Result<Clause, StructuredCheckError> {
        if !step.premise_instantiations.is_empty()
            && step.premise_instantiations.len() != step.premises.len()
        {
            return Err(StructuredCheckError::new(format!(
                "rule {} has {} premises but {} premise instantiations",
                step.rule,
                step.premises.len(),
                step.premise_instantiations.len()
            )));
        }
        let premise = self.premise_clause(step.premises[premise_index])?;
        let Some(Some((var_map, replacement_context))) =
            step.premise_instantiations.get(premise_index)
        else {
            return Ok(Self::normalize_input_clause(premise));
        };
        let specialized = var_map.specialize_clause_with_replacement_context_and_compact_vars(
            premise,
            replacement_context,
            kernel_context,
        );
        let specialized = specialized.normalized_preserving_locals();
        if !Self::local_context_is_complete(specialized.get_local_context()) {
            return Err(StructuredCheckError::new(format!(
                "rule {} produced an incomplete specialized premise context after compaction: {}",
                step.rule, specialized
            )));
        }
        Ok(specialized)
    }

    fn local_context_is_complete(context: &LocalContext) -> bool {
        for maybe_var_type in context.get_var_types() {
            let Some(var_type) = maybe_var_type else {
                return false;
            };
            for atom in var_type.iter_atoms() {
                if let Atom::FreeVariable(var_id) = atom {
                    if context.get_var_type(*var_id as usize).is_none() {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn literal_context_is_complete(literal: &Literal, context: &LocalContext) -> bool {
        for atom in literal.left.iter_atoms().chain(literal.right.iter_atoms()) {
            if let Atom::FreeVariable(var_id) = atom {
                if context.get_var_type(*var_id as usize).is_none() {
                    return false;
                }
            }
        }
        Self::local_context_is_complete(context)
    }

    fn derive_candidate_clauses(
        &self,
        step: &StructuredProofStep,
        kernel_context: &KernelContext,
    ) -> Result<Vec<Clause>, StructuredCheckError> {
        let mut candidates = Vec::new();

        if let Some(kind) = step.rule.boolean_reduction_kind() {
            let premise = self.first_premise(step)?;
            for premise_id in step.premises.iter().copied().skip(1) {
                self.premise_clause(premise_id)?;
            }
            let Some(hint) = step.details.boolean else {
                return Err(StructuredCheckError::new(format!(
                    "rule {} from {:?} requires explicit boolean-reduction details",
                    step.rule, step.premises
                )));
            };
            let mut candidate_index = 0;
            for (candidate_kind, literal_index, trace) in premise
                .find_boolean_reduction_kinds_with_locations_with_options(kernel_context, true)
            {
                if candidate_kind == kind && literal_index == hint.literal_index {
                    if candidate_index == hint.candidate_index {
                        if let Some(clause) = self.normalize_trace(&trace, kernel_context) {
                            candidates.push(clause);
                        }
                        break;
                    }
                    candidate_index += 1;
                }
            }
            if candidates.is_empty() {
                return Err(StructuredCheckError::new(format!(
                    "rule {} from {:?} did not find boolean candidate {:?}",
                    step.rule, step.premises, hint
                )));
            }
            return Ok(candidates);
        }

        let premise = self.only_premise(step)?;
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
            StructuredRule::Resolve
            | StructuredRule::Rewrite
            | StructuredRule::Specialize
            | StructuredRule::MultiRewrite
            | StructuredRule::PassiveContra
            | StructuredRule::Simplify => unreachable!(),
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

    fn first_premise(&self, step: &StructuredProofStep) -> Result<&Clause, StructuredCheckError> {
        let Some(id) = step.premises.first().copied() else {
            return Err(StructuredCheckError::new(format!(
                "rule {} expects at least one premise",
                step.rule
            )));
        };
        self.premise_clause(id)
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
        let reduction = clause.positive_exists_witness_reduction(kernel_context)?;
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
            StructuredRule::Resolve,
            StructuredRule::Rewrite,
            StructuredRule::Specialize,
            StructuredRule::MultiRewrite,
            StructuredRule::PassiveContra,
            StructuredRule::Simplify,
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
                )
                .with_details(StructuredProofStepDetails {
                    boolean: Some(StructuredBooleanHint {
                        literal_index: 0,
                        candidate_index: 0,
                    }),
                    ..Default::default()
                }),
                &context,
            )
            .unwrap();
        let right_id = checker
            .check_step(
                &StructuredProofStep::new(StructuredRule::PosAndRight, vec![0]).with_details(
                    StructuredProofStepDetails {
                        boolean: Some(StructuredBooleanHint {
                            literal_index: 0,
                            candidate_index: 0,
                        }),
                        ..Default::default()
                    },
                ),
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
                &StructuredProofStep::with_expected(StructuredRule::PosAndLeft, vec![0], wrong)
                    .with_details(StructuredProofStepDetails {
                        boolean: Some(StructuredBooleanHint {
                            literal_index: 0,
                            candidate_index: 0,
                        }),
                        ..Default::default()
                    }),
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
