use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::certificate::{Certificate, CertificateLine, CheckedCertificate};
use crate::code_generator::Error as CodeGenError;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::atom::Atom;
use crate::kernel::certificate_step::CertificateStep;
use crate::kernel::checker::{BooleanReductionWitness, Checker, StepReason};
use crate::kernel::clause::{BooleanReductionKind, Clause};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Decomposition;
use crate::project::ProjectLookup;

/// Standard certificate proof payload.
///
/// The certificate trace is intentionally rule-oriented: each step says which checker procedure
/// accepts it and which earlier steps are its premises.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(transparent)]
pub struct ProofTrace {
    pub steps: Vec<TraceStep>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TraceStep {
    #[serde(rename = "r", default, skip_serializing_if = "TraceRule::is_claim")]
    pub rule: TraceRule,

    #[serde(rename = "c")]
    pub claim: String,

    #[serde(rename = "f", default, skip_serializing_if = "Vec::is_empty")]
    pub premises: Vec<usize>,

    #[serde(rename = "g", default, skip_serializing_if = "is_false")]
    pub generic: bool,

    #[serde(rename = "k", skip_serializing_if = "Option::is_none")]
    pub br_kind: Option<BooleanReductionKind>,

    #[serde(rename = "i", skip_serializing_if = "Option::is_none")]
    pub br_literal_index: Option<usize>,
}

fn is_false(value: &bool) -> bool {
    !*value
}

fn is_serialized_generic_artifact(code: &str) -> bool {
    code.starts_with("(forall(") || code.starts_with("forall(")
}

fn is_synthetic_generic_wrapper(code: &str) -> bool {
    let trimmed = code.trim_start();
    trimmed.starts_with("function[") && trimmed.ends_with(']')
}

#[derive(Clone)]
pub(crate) struct CertificateTraceInput {
    pub step: CertificateStep,
    pub code: String,
    pub boolean_reduction_source: Option<Clause>,
}

#[derive(Clone)]
struct StepClauses {
    primary: Clause,
    aliases: Vec<Clause>,
}

impl StepClauses {
    fn new(primary: Clause, aliases: Vec<Clause>) -> Self {
        let mut deduped = vec![];
        for alias in aliases {
            if alias != primary && !deduped.contains(&alias) {
                deduped.push(alias);
            }
        }
        Self {
            primary,
            aliases: deduped,
        }
    }

    fn all(&self) -> impl Iterator<Item = &Clause> {
        std::iter::once(&self.primary).chain(self.aliases.iter())
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TraceRule {
    /// A source/environment fact accepted by direct checker lookup.
    Fact,

    /// A proof claim accepted by direct exact/egraph lookup.
    Claim,

    /// One explicit boolean reduction from a previous step.
    Br,

    /// Prove this clause because one of its boolean-reduction sets is already known.
    BrIntro,

    /// A local equality-graph check using the listed premises.
    Eq,

    /// One explicit equality-resolution step from a previous step.
    Er,

    /// One explicit equality-factoring step from a previous step.
    Ef,

    /// One explicit extensionality step from a previous step.
    Ext,

    /// One explicit injectivity step from a previous step.
    Inj,

    /// Instantiate a generic claim from a previous step.
    Inst,

    /// A certificate-local witness declaration.
    Wit,

    /// A final contradiction after earlier steps have been inserted.
    Contra,
}

impl Default for TraceRule {
    fn default() -> Self {
        Self::Claim
    }
}

impl TraceRule {
    fn is_claim(rule: &Self) -> bool {
        matches!(rule, Self::Claim)
    }
}

impl TraceStep {
    pub fn claim(claim: String) -> Self {
        Self {
            rule: TraceRule::Claim,
            claim,
            premises: vec![],
            generic: false,
            br_kind: None,
            br_literal_index: None,
        }
    }

    fn with_rule(rule: TraceRule, claim: String, premises: Vec<usize>, generic: bool) -> Self {
        Self {
            rule,
            claim,
            premises,
            generic,
            br_kind: None,
            br_literal_index: None,
        }
    }

    fn with_br_detail(
        rule: TraceRule,
        claim: String,
        premises: Vec<usize>,
        generic: bool,
        detail: Option<(BooleanReductionKind, usize)>,
    ) -> Self {
        let mut step = Self::with_rule(rule, claim, premises, generic);
        if let Some((kind, literal_index)) = detail {
            step.br_kind = Some(kind);
            step.br_literal_index = Some(literal_index);
        }
        step
    }
}

impl ProofTrace {
    pub(crate) fn from_certificate_steps_checked(
        inputs: &[CertificateTraceInput],
        checker: Checker,
        project: &dyn ProjectLookup,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<Self, CodeGenError> {
        TraceWriter::new(checker.clone(), checker, project, bindings, kernel_context).write(inputs)
    }

    pub fn without_unreferenced_auxiliary_steps(&self) -> Self {
        let mut referenced = vec![false; self.steps.len()];
        for step in &self.steps {
            for &premise in &step.premises {
                if let Some(slot) = referenced.get_mut(premise) {
                    *slot = true;
                }
            }
        }

        let mut remap = vec![None; self.steps.len()];
        let mut steps = vec![];
        for (old_index, step) in self.steps.iter().enumerate() {
            let serialized_generic_artifact = matches!(step.rule, TraceRule::Claim)
                && step.premises.is_empty()
                && step.generic
                && is_serialized_generic_artifact(&step.claim);
            let auxiliary = step.generic || serialized_generic_artifact;
            if auxiliary && !referenced[old_index] {
                continue;
            }
            remap[old_index] = Some(steps.len());
            steps.push(step.clone());
        }
        for step in &mut steps {
            for premise in &mut step.premises {
                *premise = remap
                    .get(*premise)
                    .and_then(|mapped| *mapped)
                    .expect("referenced certificate trace premise should be retained");
            }
        }
        Self { steps }
    }

    pub fn check_with_usage(
        &self,
        checker: Checker,
        project: &dyn ProjectLookup,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<CheckedCertificate, CodeGenError> {
        TraceChecker::new(checker, project, bindings, kernel_context, true).check(self)
    }

    pub fn check_usage_only(
        &self,
        checker: Checker,
        project: &dyn ProjectLookup,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<CheckedCertificate, CodeGenError> {
        TraceChecker::new(checker, project, bindings, kernel_context, false).check(self)
    }
}

/// The parsed forms of a claim being emitted as trace steps.
struct ClaimEmission {
    code: String,
    clause: Clause,
    generic: Clause,
}

/// The strategies for justifying a certificate claim, in attempt order.
///
/// Each strategy pairs a judgment with its serialization; strategies whose
/// serialization is speculative run inside a checkpoint through their helpers, so
/// a failed attempt leaves no steps behind and the next strategy is tried. The
/// reduction-witness strategies also back `emit_clause`, so boolean-reduction
/// sources and dependency clauses flow through the same engine as claims: the
/// writer never accepts a clause it cannot serialize.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClaimStrategy {
    /// The clause (or its generic form) is already carried by an emitted step.
    Available,
    /// Directly known to the replay-visible state: a plain Claim step.
    DirectFact,
    /// A boolean-reduction witness tree over the shadow state.
    ReductionWitness,
    /// A conjunction fact in the base state reduces to the claim.
    BaseConjunction,
    /// An eagerly derived chain from the saturated base closure, gated on a
    /// replay check.
    GatedEagerChain,
    /// The same chain search without the gate.
    EagerChain,
    /// A recently inserted derivation clause boolean-reduces to the claim.
    DerivedSourceBr,
    /// The claim itself is an inserted derivation clause; emit its own chain.
    DerivedSourceExact,
    /// An emitted step boolean-reduces to the claim.
    StepSourceBr,
    /// An emitted step justifies the claim through the equality graph.
    StepSourceEq,
    /// An inserted derivation clause justifies the claim through the equality graph.
    DerivedSourceEq,
    /// As above, with relaxed matching over recent insertions only.
    DerivedSourceEqRelaxed,
    /// All emitted steps jointly justify the claim through the equality graph.
    MultiPremiseEq,
    /// A boolean-reduction witness tree over the eagerly saturated shadow state.
    EagerReductionWitness,
}

const CLAIM_STRATEGIES: &[ClaimStrategy] = &[
    ClaimStrategy::Available,
    ClaimStrategy::DirectFact,
    ClaimStrategy::ReductionWitness,
    ClaimStrategy::BaseConjunction,
    ClaimStrategy::GatedEagerChain,
    ClaimStrategy::EagerChain,
    ClaimStrategy::DerivedSourceBr,
    ClaimStrategy::DerivedSourceExact,
    ClaimStrategy::StepSourceBr,
    ClaimStrategy::StepSourceEq,
    ClaimStrategy::DerivedSourceEq,
    ClaimStrategy::DerivedSourceEqRelaxed,
    ClaimStrategy::MultiPremiseEq,
    ClaimStrategy::EagerReductionWitness,
];

struct TraceWriter<'a> {
    base_checker: Checker,
    derivation_checker: Checker,
    shadow_checker: Checker,
    project: &'a dyn ProjectLookup,
    bindings: Cow<'a, BindingMap>,
    kernel_context: Cow<'a, KernelContext>,
    steps: Vec<TraceStep>,
    step_clauses: Vec<StepClauses>,
    available: HashMap<Clause, usize>,
    inserted_to_trace: HashMap<usize, usize>,
    emitting_inserted_ids: HashSet<usize>,
    /// Leaves currently being grounded via extra-literal refutation, to stop cycles.
    grounding_leaves_in_flight: HashSet<Clause>,
    emitting_local_inserted_ids: HashSet<usize>,
    deferred_claims: Vec<DeferredClaim>,
    variable_support_depth: usize,
    /// When positive, `emit_clause` restricts itself to cheap strategies. This is
    /// incremented around dependency and witness-member emission, so speculative
    /// scans never trigger nested global searches.
    cheap_emission_depth: usize,
}

struct DeferredClaim {
    line_index: usize,
    code: String,
    emit_error: String,
    checker_error: String,
}

struct TraceWriterCheckpoint {
    steps: Vec<TraceStep>,
    step_clauses: Vec<StepClauses>,
    available: HashMap<Clause, usize>,
    inserted_to_trace: HashMap<usize, usize>,
    emitting_local_inserted_ids: HashSet<usize>,
    shadow_checker: Checker,
    variable_support_depth: usize,
}

impl<'a> TraceWriter<'a> {
    fn new(
        checker: Checker,
        derivation_checker: Checker,
        project: &'a dyn ProjectLookup,
        bindings: Cow<'a, BindingMap>,
        kernel_context: Cow<'a, KernelContext>,
    ) -> Self {
        let mut derivation_checker = derivation_checker;
        derivation_checker.enable_eager_boolean_reductions(&kernel_context);
        Self {
            base_checker: checker.clone(),
            derivation_checker,
            shadow_checker: checker,
            project,
            bindings,
            kernel_context,
            steps: vec![],
            step_clauses: vec![],
            available: HashMap::new(),
            inserted_to_trace: HashMap::new(),
            emitting_inserted_ids: HashSet::new(),
            grounding_leaves_in_flight: HashSet::new(),
            emitting_local_inserted_ids: HashSet::new(),
            deferred_claims: vec![],
            variable_support_depth: 0,
            cheap_emission_depth: 0,
        }
    }

    fn checkpoint(&self) -> TraceWriterCheckpoint {
        TraceWriterCheckpoint {
            steps: self.steps.clone(),
            step_clauses: self.step_clauses.clone(),
            available: self.available.clone(),
            inserted_to_trace: self.inserted_to_trace.clone(),
            emitting_local_inserted_ids: self.emitting_local_inserted_ids.clone(),
            shadow_checker: self.shadow_checker.clone(),
            variable_support_depth: self.variable_support_depth,
        }
    }

    fn restore(&mut self, checkpoint: TraceWriterCheckpoint) {
        self.steps = checkpoint.steps;
        self.step_clauses = checkpoint.step_clauses;
        self.available = checkpoint.available;
        self.inserted_to_trace = checkpoint.inserted_to_trace;
        self.emitting_local_inserted_ids = checkpoint.emitting_local_inserted_ids;
        self.shadow_checker = checkpoint.shadow_checker;
        self.variable_support_depth = checkpoint.variable_support_depth;
    }

    fn write(mut self, inputs: &[CertificateTraceInput]) -> Result<ProofTrace, CodeGenError> {
        for (line_index, input) in inputs.iter().enumerate() {
            if self.derivation_checker.has_contradiction()
                || self.shadow_checker.has_contradiction()
            {
                break;
            }
            self.write_step(line_index, input)?;
        }
        if !self.derivation_checker.has_contradiction() && !self.shadow_checker.has_contradiction()
        {
            self.derivation_checker
                .enable_eager_boolean_reductions(&self.kernel_context);
        }
        if !self.derivation_checker.has_contradiction() && !self.shadow_checker.has_contradiction()
        {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "generated proof steps did not close while writing certificate trace{}",
                self.deferred_claim_context()
            )));
        }
        if !self.shadow_checker.has_contradiction() {
            self.emit_boolean_reduction_contradiction()?;
        }
        Ok(ProofTrace { steps: self.steps })
    }

    fn write_step(
        &mut self,
        line_index: usize,
        input: &CertificateTraceInput,
    ) -> Result<(), CodeGenError> {
        let parsed = match &input.step {
            CertificateStep::Satisfy(_) => Certificate::parse_code_line(
                &input.code,
                self.project,
                &mut self.bindings,
                &mut self.kernel_context,
            )?,
            CertificateStep::Claim(_) => input.step.clone(),
        };
        let code = input.code.as_str();

        let mut deferred_claim_error = None;
        let claim_index = match &parsed {
            CertificateStep::Claim(claim) => {
                if let Some(source) = &input.boolean_reduction_source {
                    Some(self.emit_boolean_reduction_claim_step(
                        code.to_string(),
                        source.clone(),
                        claim,
                    )?)
                } else {
                    match self.emit_claim_step(code.to_string(), claim) {
                        Ok(index) => Some(index),
                        Err(err) => {
                            deferred_claim_error = Some(err);
                            None
                        }
                    }
                }
            }
            CertificateStep::Satisfy(satisfy) => {
                let justification = satisfy
                    .justification
                    .normalized_specialized_clause(&self.kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;
                self.emit_clause(justification, StepReason::PreviousClaim)?;
                self.emit_witness_step(code.to_string(), satisfy)?;
                None
            }
        };

        if self.shadow_checker.has_contradiction() {
            return Ok(());
        }
        let before = self.derivation_checker.inserted_len();
        let mut checked_steps = Vec::new();
        let mut reprocess_derivation = false;
        match self.apply_step_to_derivation_checker(
            &parsed,
            code,
            input.boolean_reduction_source.as_ref(),
        ) {
            Ok(checked) => {
                checked_steps = checked;
            }
            Err(err)
                if claim_index.is_some() && err.to_string().contains("is not obviously true") =>
            {
                if let CertificateStep::Claim(claim) = &parsed {
                    let generic = claim.normalized_generic_clause();
                    let clause = claim
                        .normalized_specialized_clause(&self.kernel_context)
                        .map_err(CodeGenError::GeneratedBadCode)?;
                    self.derivation_checker.insert_clause_for_trace(
                        &generic,
                        StepReason::PreviousClaim,
                        &self.kernel_context,
                    );
                    self.derivation_checker.insert_clause_for_trace(
                        &clause,
                        StepReason::PreviousClaim,
                        &self.kernel_context,
                    );
                    reprocess_derivation = true;
                } else {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "proof step {} failed while writing certificate trace: {} ({})",
                        line_index + 1,
                        code,
                        err
                    )));
                }
            }
            Err(err) if deferred_claim_error.is_some() => {
                self.deferred_claims.push(DeferredClaim {
                    line_index,
                    code: code.to_string(),
                    emit_error: deferred_claim_error.unwrap().to_string(),
                    checker_error: err.to_string(),
                });
                return Ok(());
            }
            Err(err)
                if matches!(parsed, CertificateStep::Satisfy(_))
                    && err.to_string().contains("Witness declaration") =>
            {
                if let CertificateStep::Satisfy(satisfy) = &parsed {
                    let generic = satisfy.justification.normalized_generic_clause();
                    let clause = satisfy
                        .justification
                        .normalized_specialized_clause(&self.kernel_context)
                        .map_err(CodeGenError::GeneratedBadCode)?;
                    self.derivation_checker.insert_clause_for_trace(
                        &generic,
                        StepReason::WitnessDeclaration,
                        &self.kernel_context,
                    );
                    self.derivation_checker.insert_clause_for_trace(
                        &clause,
                        StepReason::WitnessDeclaration,
                        &self.kernel_context,
                    );
                    if let Some(specialized_clause) = &satisfy.specialized_clause {
                        self.derivation_checker.insert_clause_for_trace(
                            specialized_clause,
                            StepReason::WitnessDeclaration,
                            &self.kernel_context,
                        );
                    }
                    for witness_clause in &satisfy.witness_clauses {
                        self.derivation_checker.insert_clause_for_trace(
                            witness_clause,
                            StepReason::WitnessDeclaration,
                            &self.kernel_context,
                        );
                    }
                    reprocess_derivation = true;
                }
            }
            Err(err) => {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "proof step {} failed while writing certificate trace: {} ({})",
                    line_index + 1,
                    code,
                    err
                )));
            }
        }
        for (clause, reason) in checked_steps {
            if self.available.contains_key(&clause) {
                continue;
            }
            if let Err(err) = self.emit_clause(clause.clone(), reason.clone()) {
                if deferred_claim_error.is_some() {
                    self.deferred_claims.push(DeferredClaim {
                        line_index,
                        code: code.to_string(),
                        emit_error: deferred_claim_error
                            .as_ref()
                            .expect("checked above")
                            .to_string(),
                        checker_error: err.to_string(),
                    });
                    continue;
                }
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "failed to emit checked proof step {} while writing certificate trace: {} ({})",
                    line_index + 1,
                    code,
                    err
                )));
            }
        }
        for inserted_id in before..self.derivation_checker.inserted_len() {
            let inserted = self
                .derivation_checker
                .inserted_clause(inserted_id)
                .ok_or_else(|| {
                    CodeGenError::GeneratedBadCode(format!(
                        "missing inserted clause {} while writing certificate trace",
                        inserted_id
                    ))
                })?;
            let certificate_trace_index = match self.emit_inserted_clause(inserted_id) {
                Ok(index) => index,
                Err(_)
                    if matches!(inserted.reason, StepReason::PreviousClaim)
                        && claim_index.is_some() =>
                {
                    claim_index.expect("claim_index checked above")
                }
                Err(_) => continue,
            };
            self.inserted_to_trace
                .insert(inserted_id, certificate_trace_index);
        }
        if reprocess_derivation {
            self.derivation_checker
                .enable_eager_boolean_reductions(&self.kernel_context);
        }
        Ok(())
    }

    fn apply_step_to_derivation_checker(
        &mut self,
        step: &CertificateStep,
        code: &str,
        boolean_reduction_source: Option<&Clause>,
    ) -> Result<Vec<(Clause, StepReason)>, CodeGenError> {
        let cert_line_context = format!("; certificate line: {:?}", code);

        #[cfg(feature = "validate")]
        step.validate_normalized_shape(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;

        match step {
            CertificateStep::Claim(claim) => {
                claim
                    .validate_checker_payload(&self.kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;

                let generic_clause = claim.normalized_generic_clause();
                let clause = claim
                    .normalized_specialized_clause(&self.kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;

                if let Some(source) = boolean_reduction_source {
                    let source_reason = self
                        .derivation_checker
                        .check_clause_direct_for_trace(source, &self.kernel_context);
                    if source_reason.is_none() {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "Boolean reduction has unknown source{} (source debug: {:?})",
                            cert_line_context, source,
                        )));
                    }
                    if self
                        .derivation_checker
                        .boolean_reduction_detail_for_trace(source, &clause, &self.kernel_context)
                        .is_none()
                    {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "Boolean reduction does not reduce source to result{} (source debug: {:?}; result debug: {:?})",
                            cert_line_context,
                            source,
                            clause,
                        )));
                    }
                    self.derivation_checker.insert_clause(
                        &clause,
                        StepReason::PreviousClaim,
                        &self.kernel_context,
                    );
                    return Ok(vec![(clause, source_reason.unwrap())]);
                }

                let reason = self
                    .derivation_checker
                    .check_clause(&generic_clause, &self.kernel_context)
                    .or_else(|| {
                        self.derivation_checker
                            .check_clause(&clause, &self.kernel_context)
                    });

                let Some(reason) = reason else {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "Claim is not obviously true{} (generic debug: {:?}; specialized debug: {:?})",
                        cert_line_context,
                        claim.clause(),
                        clause,
                    )));
                };

                self.derivation_checker.insert_clause(
                    &generic_clause,
                    StepReason::PreviousClaim,
                    &self.kernel_context,
                );
                self.derivation_checker.insert_clause(
                    &clause,
                    StepReason::PreviousClaim,
                    &self.kernel_context,
                );
                Ok(vec![(clause, reason)])
            }
            CertificateStep::Satisfy(step) => {
                let mut witness_validation_context = self.kernel_context.as_ref().clone();
                step.validate_checker_payload(&mut witness_validation_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;

                let generic_clause = step.justification.normalized_generic_clause();
                let justification_clause = step
                    .justification
                    .normalized_specialized_clause(&self.kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;
                let justification_ok = self
                    .derivation_checker
                    .check_clause(&generic_clause, &self.kernel_context)
                    .or_else(|| {
                        self.derivation_checker
                            .check_clause(&justification_clause, &self.kernel_context)
                    })
                    .is_some();
                if !justification_ok {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "Witness declaration is not obviously true{} (missing implicit existential {:?})",
                        cert_line_context,
                        justification_clause,
                    )));
                }

                self.derivation_checker.insert_clause(
                    &generic_clause,
                    StepReason::WitnessDeclaration,
                    &self.kernel_context,
                );
                self.derivation_checker.insert_clause(
                    &justification_clause,
                    StepReason::WitnessDeclaration,
                    &self.kernel_context,
                );
                if let Some(specialized_clause) = &step.specialized_clause {
                    self.derivation_checker.insert_clause(
                        specialized_clause,
                        StepReason::WitnessDeclaration,
                        &self.kernel_context,
                    );
                }
                for clause in &step.witness_clauses {
                    self.derivation_checker.insert_clause(
                        clause,
                        StepReason::WitnessDeclaration,
                        &self.kernel_context,
                    );
                }

                Ok(vec![(justification_clause, StepReason::WitnessDeclaration)])
            }
        }
    }

    fn deferred_claim_context(&self) -> String {
        if self.deferred_claims.is_empty() {
            return String::new();
        }
        let claims = self
            .deferred_claims
            .iter()
            .take(8)
            .map(|claim| {
                format!(
                    "step {} `{}` (emit: {}; checker: {})",
                    claim.line_index + 1,
                    claim.code,
                    claim.emit_error,
                    claim.checker_error
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        format!("; deferred unneeded claims: {}", claims)
    }

    /// Emits one certificate claim as trace steps by walking CLAIM_STRATEGIES in
    /// order. A claim that exhausts the table is reported to the caller, which
    /// defers it; the writer never accepts a claim it could not serialize.
    fn emit_claim_step(
        &mut self,
        code: String,
        claim: &crate::kernel::certificate_step::Claim,
    ) -> Result<usize, CodeGenError> {
        let generic = claim.normalized_generic_clause();
        let clause = claim
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let emission = ClaimEmission {
            code,
            clause,
            generic,
        };
        for &strategy in CLAIM_STRATEGIES {
            if let Some(index) = self.attempt_claim_strategy(strategy, &emission)? {
                return Ok(index);
            }
        }
        Err(CodeGenError::GeneratedBadCode(format!(
            "could not emit claim to certificate trace: {}",
            emission.code
        )))
    }

    /// Tries a single justification strategy for a claim. Returns the trace step
    /// index carrying the claim when the strategy both judges the claim justified
    /// and serializes that judgment.
    fn attempt_claim_strategy(
        &mut self,
        strategy: ClaimStrategy,
        emission: &ClaimEmission,
    ) -> Result<Option<usize>, CodeGenError> {
        let ClaimEmission {
            code,
            clause,
            generic,
        } = emission;
        match strategy {
            ClaimStrategy::Available => {
                if let Some(&index) = self.available.get(clause) {
                    return Ok(Some(index));
                }
                if let Some(&index) = self.available.get(generic) {
                    if generic != clause {
                        return self
                            .push_step(
                                TraceRule::Inst,
                                code.clone(),
                                vec![index],
                                clause.clone(),
                                false,
                                vec![],
                            )
                            .map(Some);
                    }
                    return Ok(Some(index));
                }
                Ok(None)
            }
            ClaimStrategy::DirectFact => {
                let reason = self
                    .shadow_checker
                    .check_clause_direct_for_trace(clause, &self.kernel_context)
                    .or_else(|| {
                        self.shadow_checker
                            .check_clause_direct_for_trace(generic, &self.kernel_context)
                    });
                if reason.is_none() {
                    return Ok(None);
                }
                self.push_step(
                    TraceRule::Claim,
                    code.clone(),
                    vec![],
                    clause.clone(),
                    false,
                    Self::claim_aliases_for_code(code, generic.clone(), clause),
                )
                .map(Some)
            }
            ClaimStrategy::ReductionWitness => {
                self.emit_claim_via_reduction_witness(clause, generic, code, false)
            }
            ClaimStrategy::EagerReductionWitness => {
                self.emit_claim_via_reduction_witness(clause, generic, code, true)
            }
            ClaimStrategy::BaseConjunction => {
                for (candidate, candidate_generic) in
                    [(clause.clone(), false), (generic.clone(), true)]
                {
                    if let Some(index) = self.emit_component_from_base_conjunction(
                        code.clone(),
                        candidate.clone(),
                        candidate_generic,
                    )? {
                        if candidate_generic && candidate != *clause {
                            return self
                                .push_step(
                                    TraceRule::Inst,
                                    code.clone(),
                                    vec![index],
                                    clause.clone(),
                                    false,
                                    vec![],
                                )
                                .map(Some);
                        }
                        return Ok(Some(index));
                    }
                }
                Ok(None)
            }
            ClaimStrategy::GatedEagerChain | ClaimStrategy::EagerChain => {
                let gated = strategy == ClaimStrategy::GatedEagerChain;
                let code_is_forall_claim = is_serialized_generic_artifact(code);
                let try_clause_eager =
                    !code_is_forall_claim && !Self::is_single_positive_forall_clause(clause);
                if try_clause_eager
                    && (!gated || self.eager_boolean_reduction_intro_replays(clause))
                {
                    if let Some(index) = self.emit_eager_boolean_reduction_path(
                        code.clone(),
                        clause.clone(),
                        false,
                        &[],
                    )? {
                        return Ok(Some(index));
                    }
                }
                let try_generic_eager =
                    is_serialized_generic_artifact(code) || is_synthetic_generic_wrapper(code);
                let try_generic_eager = try_generic_eager
                    && !code_is_forall_claim
                    && !Self::is_single_positive_forall_clause(generic);
                if try_generic_eager
                    && generic != clause
                    && (!gated || self.eager_boolean_reduction_intro_replays(generic))
                {
                    if let Some(generic_index) = self.emit_eager_boolean_reduction_path(
                        code.clone(),
                        generic.clone(),
                        true,
                        &[],
                    )? {
                        return self
                            .push_step(
                                TraceRule::Inst,
                                code.clone(),
                                vec![generic_index],
                                clause.clone(),
                                false,
                                vec![],
                            )
                            .map(Some);
                    }
                }
                Ok(None)
            }
            ClaimStrategy::DerivedSourceBr => {
                for (candidate, candidate_generic) in
                    [(clause.clone(), false), (generic.clone(), true)]
                {
                    for inserted_id in (0..self.derivation_checker.inserted_len()).rev().take(256) {
                        let Some(source_inserted) =
                            self.derivation_checker.inserted_clause(inserted_id)
                        else {
                            continue;
                        };
                        if source_inserted.clause == candidate {
                            continue;
                        }
                        if self
                            .shadow_checker
                            .boolean_reduction_detail_for_trace(
                                &source_inserted.clause,
                                &candidate,
                                &self.kernel_context,
                            )
                            .is_none()
                        {
                            continue;
                        }
                        let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                            continue;
                        };
                        return self
                            .push_candidate_step(
                                TraceRule::Br,
                                code.clone(),
                                vec![source_index],
                                candidate,
                                candidate_generic,
                                clause,
                            )
                            .map(Some);
                    }
                }
                Ok(None)
            }
            ClaimStrategy::DerivedSourceExact => {
                for (candidate, candidate_generic) in
                    [(clause.clone(), false), (generic.clone(), true)]
                {
                    let Some(inserted_id) = self.derivation_checker.exact_clause_id(&candidate)
                    else {
                        continue;
                    };
                    let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                        continue;
                    };
                    if candidate_generic && candidate != *clause {
                        return self
                            .push_step(
                                TraceRule::Inst,
                                code.clone(),
                                vec![source_index],
                                clause.clone(),
                                false,
                                vec![],
                            )
                            .map(Some);
                    }
                    return Ok(Some(source_index));
                }
                Ok(None)
            }
            ClaimStrategy::StepSourceBr => {
                for (candidate, candidate_generic) in
                    [(clause.clone(), false), (generic.clone(), true)]
                {
                    for source_index in (0..self.step_clauses.len()).rev() {
                        if self
                            .boolean_reduction_detail_for_step(source_index, &candidate)
                            .is_some()
                        {
                            return self
                                .push_candidate_step(
                                    TraceRule::Br,
                                    code.clone(),
                                    vec![source_index],
                                    candidate,
                                    candidate_generic,
                                    clause,
                                )
                                .map(Some);
                        }
                    }
                }
                Ok(None)
            }
            ClaimStrategy::StepSourceEq => {
                for (candidate, candidate_generic) in
                    [(clause.clone(), false), (generic.clone(), true)]
                {
                    for source_index in (0..self.step_clauses.len()).rev() {
                        let premises = vec![source_index];
                        if self.eq_step_replays(&premises, &candidate) {
                            return self
                                .push_candidate_step(
                                    TraceRule::Eq,
                                    code.clone(),
                                    premises,
                                    candidate,
                                    candidate_generic,
                                    clause,
                                )
                                .map(Some);
                        }
                    }
                }
                Ok(None)
            }
            ClaimStrategy::DerivedSourceEq | ClaimStrategy::DerivedSourceEqRelaxed => {
                let relaxed = strategy == ClaimStrategy::DerivedSourceEqRelaxed;
                let scan = if relaxed { 128 } else { usize::MAX };
                for (candidate, candidate_generic) in
                    [(clause.clone(), false), (generic.clone(), true)]
                {
                    for inserted_id in (0..self.derivation_checker.inserted_len()).rev().take(scan)
                    {
                        let Some(source_inserted) =
                            self.derivation_checker.inserted_clause(inserted_id)
                        else {
                            continue;
                        };
                        if source_inserted.clause == candidate {
                            continue;
                        }
                        if !self.source_clause_eq_replays(
                            &source_inserted.clause,
                            &candidate,
                            relaxed,
                        ) {
                            continue;
                        }
                        let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                            continue;
                        };
                        let premises = vec![source_index];
                        return self
                            .push_candidate_step(
                                TraceRule::Eq,
                                code.clone(),
                                premises,
                                candidate,
                                candidate_generic,
                                clause,
                            )
                            .map(Some);
                    }
                }
                Ok(None)
            }
            ClaimStrategy::MultiPremiseEq => {
                if let Some(index) =
                    self.emit_multi_premise_eq_step(code.clone(), clause.clone(), false)?
                {
                    return Ok(Some(index));
                }
                if generic != clause {
                    if let Some(generic_index) =
                        self.emit_multi_premise_eq_step(code.clone(), generic.clone(), true)?
                    {
                        return self
                            .push_step(
                                TraceRule::Inst,
                                code.clone(),
                                vec![generic_index],
                                clause.clone(),
                                false,
                                vec![],
                            )
                            .map(Some);
                    }
                }
                Ok(None)
            }
        }
    }

    /// Tries to emit a claim by constructing a boolean-reduction witness for it and
    /// serializing the witness tree into premise-bearing BrIntro steps.
    ///
    /// With `eager` false the witness is computed against the shadow checker as-is;
    /// with `eager` true, against an eagerly saturated clone, which covers claims
    /// whose justification runs through eagerly derived clauses. Either way the
    /// serialized steps carry their premises, so replay verifies each node locally.
    fn emit_claim_via_reduction_witness(
        &mut self,
        clause: &Clause,
        generic: &Clause,
        code: &str,
        eager: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        let mut local = self.shadow_checker.clone();
        if eager {
            local.enable_eager_boolean_reductions(&self.kernel_context);
        }

        for (target, target_is_generic) in [(clause, false), (generic, true)] {
            if target_is_generic && generic == clause {
                continue;
            }
            let Some(witness) = local.boolean_reduction_witness(target, &self.kernel_context)
            else {
                continue;
            };
            let BooleanReductionWitness::Reduced { members, .. } = witness else {
                // A directly-known clause is handled by the earlier claim paths.
                continue;
            };
            let Some(premises) = self.emit_witness_members(&local, &members)? else {
                continue;
            };
            if target_is_generic {
                let generic_index = self.push_step(
                    TraceRule::BrIntro,
                    code.to_string(),
                    premises,
                    generic.clone(),
                    true,
                    vec![],
                )?;
                return self
                    .push_step(
                        TraceRule::Inst,
                        code.to_string(),
                        vec![generic_index],
                        clause.clone(),
                        false,
                        vec![],
                    )
                    .map(Some);
            }
            let aliases = Self::claim_aliases_for_code(code, generic.clone(), clause);
            return self
                .push_step(
                    TraceRule::BrIntro,
                    code.to_string(),
                    premises,
                    clause.clone(),
                    false,
                    aliases,
                )
                .map(Some);
        }
        Ok(None)
    }

    /// Serializes every member of a witness node, returning their trace step
    /// indices. Member emission runs at raised cheap-emission depth so it never
    /// triggers nested global searches.
    fn emit_witness_members(
        &mut self,
        local: &Checker,
        members: &[BooleanReductionWitness],
    ) -> Result<Option<Vec<usize>>, CodeGenError> {
        self.cheap_emission_depth += 1;
        let debug = std::env::var("ACORN_DEBUG_CERT").is_ok();
        let result = (|| {
            let mut premises = Vec::new();
            for member in members {
                let outcome = self.emit_reduction_witness(local, member)?;
                if debug {
                    let (kind, clause, id) = match member {
                        BooleanReductionWitness::Direct {
                            clause,
                            inserted_id,
                        } => ("direct", clause, *inserted_id),
                        BooleanReductionWitness::Reduced { clause, .. } => {
                            ("reduced", clause, None)
                        }
                    };
                    eprintln!(
                        "WITNESS-MEMBER kind={} id={:?} emitted={} clause={}",
                        kind,
                        id,
                        outcome.is_some(),
                        clause
                    );
                }
                match outcome {
                    Some(index) => {
                        if !premises.contains(&index) {
                            premises.push(index);
                        }
                    }
                    None => return Ok(None),
                }
            }
            if premises.is_empty() {
                return Ok(None);
            }
            Ok(Some(premises))
        })();
        self.cheap_emission_depth -= 1;
        result
    }

    /// Tries to emit a bare clause via a boolean-reduction witness, first over the
    /// shadow state and then over an eagerly saturated clone. This is the same
    /// engine that backs claim emission, applied to boolean-reduction sources and
    /// dependency clauses so that everything the writer accepts has a serialization.
    fn emit_clause_via_reduction_witness(
        &mut self,
        clause: &Clause,
    ) -> Result<Option<usize>, CodeGenError> {
        let debug = std::env::var("ACORN_DEBUG_CERT").is_ok();
        if self.cheap_emission_depth > 0 {
            if debug {
                eprintln!(
                    "WITNESS: depth={} skipping for {}",
                    self.cheap_emission_depth, clause
                );
            }
            return Ok(None);
        }
        for eager in [false, true] {
            let mut local = self.shadow_checker.clone();
            if eager {
                local.enable_eager_boolean_reductions(&self.kernel_context);
            }
            let witness_opt = local.boolean_reduction_witness(clause, &self.kernel_context);
            if debug {
                eprintln!(
                    "WITNESS: eager={} clause={} witness={}",
                    eager,
                    clause,
                    match &witness_opt {
                        None => "none".to_string(),
                        Some(BooleanReductionWitness::Reduced { members, .. }) =>
                            format!("reduced({} members)", members.len()),
                        Some(_) => "other".to_string(),
                    }
                );
            }
            let Some(witness) = witness_opt else {
                continue;
            };
            let BooleanReductionWitness::Reduced { members, .. } = witness else {
                continue;
            };
            let Some(premises) = self.emit_witness_members(&local, &members)? else {
                continue;
            };
            let (code, generic) = self.serialize_clause_step(clause)?;
            return self
                .push_step(
                    TraceRule::BrIntro,
                    code,
                    premises,
                    clause.clone(),
                    generic,
                    vec![],
                )
                .map(Some);
        }
        Ok(None)
    }

    /// Serializes one node of a boolean-reduction witness tree, returning the trace
    /// step index carrying that node's clause. Direct leaves resolve through the
    /// checker the witness was computed against, so their own derivation chains
    /// (fact citations, eager reductions, simplifications) serialize too.
    /// The eager checker can know a leaf by normalizing a grounding clause whose
    /// extra literals are refuted by other eager derivations. Replay only sees
    /// emitted steps, so serialize those refutations too: emit a witness-backed
    /// claim for the negation of each extra literal, then re-ask the same direct
    /// judgment replay will use. Returns whether the leaf is now justified.
    fn refute_grounding_extras(
        &mut self,
        local: &Checker,
        leaf: &Clause,
        grounding: &Clause,
    ) -> Result<bool, CodeGenError> {
        let debug = std::env::var("ACORN_DEBUG_CERT").is_ok();
        if !self.grounding_leaves_in_flight.insert(leaf.clone()) {
            if debug {
                eprintln!("REFUTE: cycle on leaf {}", leaf);
            }
            return Ok(false);
        }
        if debug {
            eprintln!("REFUTE: leaf={} grounding={}", leaf, grounding);
        }
        let result = (|this: &mut Self| {
            for literal in &grounding.literals {
                if leaf.literals.contains(literal) {
                    continue;
                }
                let negated = Clause::new(vec![literal.negate()], grounding.get_local_context());
                if this
                    .shadow_checker
                    .check_clause_direct_for_trace(&negated, &this.kernel_context)
                    .is_some()
                {
                    continue;
                }
                // The negation may be directly known to the eager checker (for
                // example by and-elimination of an inserted conjunction); emit
                // its insertion chain. Otherwise fall back to a reduction tree.
                let mut prover = local.clone();
                let direct_id = prover
                    .check_clause_direct_for_trace(&negated, &this.kernel_context)
                    .and_then(|_| local.exact_clause_id(&negated));
                if debug {
                    eprintln!(
                        "REFUTE: extra literal {} direct_id={:?}",
                        literal, direct_id
                    );
                }
                if let Some(id) = direct_id {
                    if this
                        .emit_local_inserted_clause(local, id, &mut HashSet::new())
                        .is_ok()
                    {
                        continue;
                    }
                }
                let witness_opt = prover.boolean_reduction_witness(&negated, &this.kernel_context);
                if debug {
                    eprintln!(
                        "REFUTE: extra literal {} negated-witness={}",
                        literal,
                        witness_opt.is_some()
                    );
                }
                let Some(witness) = witness_opt else {
                    return Ok(false);
                };
                let emitted = this.emit_reduction_witness(local, &witness)?;
                if debug {
                    eprintln!("REFUTE: emitted={}", emitted.is_some());
                }
                if emitted.is_none() {
                    return Ok(false);
                }
            }
            Ok(this
                .shadow_checker
                .check_clause_direct_for_trace(leaf, &this.kernel_context)
                .is_some())
        })(self);
        self.grounding_leaves_in_flight.remove(leaf);
        result
    }

    fn emit_reduction_witness(
        &mut self,
        local: &Checker,
        witness: &BooleanReductionWitness,
    ) -> Result<Option<usize>, CodeGenError> {
        match witness {
            BooleanReductionWitness::Direct {
                clause,
                inserted_id,
            } => {
                if let Some(&index) = self.available.get(clause) {
                    return Ok(Some(index));
                }
                if let Some(id) = inserted_id {
                    return self
                        .emit_local_inserted_clause(local, *id, &mut HashSet::new())
                        .map(Some);
                }
                // Known through the term graph only. Serialize as a factless Eq step
                // when the replay-visible state can also justify it directly.
                if self
                    .shadow_checker
                    .check_clause_direct_for_trace(clause, &self.kernel_context)
                    .is_some()
                {
                    let (code, generic) = self.serialize_clause_step(clause)?;
                    return self
                        .push_step(TraceRule::Eq, code, vec![], clause.clone(), generic, vec![])
                        .map(Some);
                }
                // Otherwise the graph knows the leaf by normalizing some inserted
                // clause (for example, dropping literals that known facts refute).
                // Find a grounding clause, emit its own chain, and serialize the
                // leaf as an Eq step from it. The grounding may normalize to a
                // strictly stronger clause than the leaf, so after the cheap exact
                // check, candidates are tried transactionally: emit the chain, then
                // ask the same direct judgment replay will use, and roll back when
                // it declines. Recent insertions first: eager derivations land late.
                let grounding_debug = std::env::var("ACORN_DEBUG_CERT").is_ok();
                if grounding_debug {
                    eprintln!("GROUND: leaf={} local_len={}", clause, local.inserted_len());
                    let needle = format!("{}", clause.literals[0].left);
                    for id in 0..local.inserted_len() {
                        if let Some(ins) = local.inserted_clause(id) {
                            let s = format!("{}", ins.clause);
                            if s.contains(&needle) {
                                eprintln!("GROUND: contains-lhs id={} clause={}", id, s);
                            }
                        }
                    }
                }
                // Scanning is cheap; transactional emission attempts are not.
                // Scan every insertion (the eager closure can push the useful
                // groundings far from the tail) but bound the attempts.
                let mut attempts = 0;
                for local_id in (0..local.inserted_len()).rev() {
                    if attempts >= 32 {
                        break;
                    }
                    let Some(inserted) = local.inserted_clause(local_id) else {
                        continue;
                    };
                    if inserted.clause == *clause {
                        continue;
                    }
                    let shares_literal = inserted
                        .clause
                        .literals
                        .iter()
                        .any(|literal| clause.literals.contains(literal));
                    if !shares_literal {
                        continue;
                    }
                    attempts += 1;
                    if grounding_debug {
                        eprintln!(
                            "GROUND: candidate id={} clause={} reason={:?}",
                            local_id, inserted.clause, inserted.reason
                        );
                    }
                    let exact = self.source_clause_eq_replays(&inserted.clause, clause, false);
                    let checkpoint = self.checkpoint();
                    let emit_result =
                        self.emit_local_inserted_clause(local, local_id, &mut HashSet::new());
                    if grounding_debug {
                        eprintln!("GROUND: emit_local={:?}", emit_result.as_ref().map(|_| ()));
                    }
                    let Ok(source_index) = emit_result else {
                        self.restore(checkpoint);
                        continue;
                    };
                    if !exact
                        && self
                            .shadow_checker
                            .check_clause_direct_for_trace(clause, &self.kernel_context)
                            .is_none()
                        && !self.refute_grounding_extras(local, clause, &inserted.clause)?
                    {
                        self.restore(checkpoint);
                        continue;
                    }
                    let (code, generic) = self.serialize_clause_step(clause)?;
                    return self
                        .push_step(
                            TraceRule::Eq,
                            code,
                            vec![source_index],
                            clause.clone(),
                            generic,
                            vec![],
                        )
                        .map(Some);
                }
                Ok(None)
            }
            BooleanReductionWitness::Reduced { clause, members } => {
                if let Some(&index) = self.available.get(clause) {
                    return Ok(Some(index));
                }
                let Some(premises) = self.emit_witness_members(local, members)? else {
                    return Ok(None);
                };
                let (code, generic) = self.serialize_clause_step(clause)?;
                self.push_step(
                    TraceRule::BrIntro,
                    code,
                    premises,
                    clause.clone(),
                    generic,
                    vec![],
                )
                .map(Some)
            }
        }
    }

    fn eager_boolean_reduction_intro_replays(&self, clause: &Clause) -> bool {
        let mut local = self.shadow_checker.clone();
        local.enable_eager_boolean_reductions(&self.kernel_context);
        local.boolean_reduction_proves_for_trace(clause, &self.kernel_context)
            || local.check_clause(clause, &self.kernel_context).is_some()
    }

    fn is_single_positive_forall_clause(clause: &Clause) -> bool {
        let [literal] = clause.literals.as_slice() else {
            return false;
        };
        literal.positive
            && ((literal.right.is_true() && literal.left.as_ref().is_forall())
                || (literal.left.is_true() && literal.right.as_ref().is_forall()))
    }

    fn emit_boolean_reduction_claim_step(
        &mut self,
        code: String,
        source: Clause,
        result: &crate::kernel::certificate_step::Claim,
    ) -> Result<usize, CodeGenError> {
        let result = result
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let source_index = match self.emit_clause(source.clone(), StepReason::PreviousClaim) {
            Ok(index) => index,
            Err(source_err) => {
                let mut seen = HashSet::new();
                if let Some(index) =
                    self.emit_supporting_component_clause(result.clone(), &mut seen)?
                {
                    return Ok(index);
                }
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "failed to emit source while writing boolean-reduction step {}: {}",
                    code, source_err
                )));
            }
        };
        self.push_br_step(code, source_index, result, false, vec![])
    }

    fn insert_step_clauses(&mut self, index: usize, clauses: &StepClauses) {
        for clause in clauses.all() {
            self.shadow_checker.insert_clause_for_trace(
                clause,
                StepReason::PreviousClaim,
                &self.kernel_context,
            );
            self.available.entry(clause.clone()).or_insert(index);
        }
    }

    fn claim_aliases(generic: Clause, specialized: &Clause) -> Vec<Clause> {
        if generic == *specialized {
            vec![]
        } else {
            vec![generic]
        }
    }

    fn claim_aliases_for_code(code: &str, generic: Clause, specialized: &Clause) -> Vec<Clause> {
        if is_synthetic_generic_wrapper(code) {
            vec![]
        } else {
            Self::claim_aliases(generic, specialized)
        }
    }

    fn emit_witness_step(
        &mut self,
        code: String,
        satisfy: &crate::kernel::certificate_step::SatisfyStep,
    ) -> Result<usize, CodeGenError> {
        let clause = satisfy
            .justification
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        if self
            .shadow_checker
            .check_clause_direct_for_trace(&clause, &self.kernel_context)
            .is_none()
        {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "certificate trace witness declaration is missing justification: {}",
                code
            )));
        }
        self.shadow_checker.insert_clause_for_trace(
            &satisfy.justification.normalized_generic_clause(),
            StepReason::WitnessDeclaration,
            &self.kernel_context,
        );
        self.shadow_checker.insert_clause_for_trace(
            &clause,
            StepReason::WitnessDeclaration,
            &self.kernel_context,
        );
        if let Some(specialized_clause) = &satisfy.specialized_clause {
            self.shadow_checker.insert_clause_for_trace(
                specialized_clause,
                StepReason::WitnessDeclaration,
                &self.kernel_context,
            );
        }
        for witness_clause in &satisfy.witness_clauses {
            self.shadow_checker.insert_clause_for_trace(
                witness_clause,
                StepReason::WitnessDeclaration,
                &self.kernel_context,
            );
        }
        let mut aliases = vec![satisfy.justification.normalized_generic_clause()];
        if let Some(specialized_clause) = &satisfy.specialized_clause {
            aliases.push(specialized_clause.clone());
        }
        aliases.extend(satisfy.witness_clauses.iter().cloned());
        self.push_step(TraceRule::Wit, code, vec![], clause, false, aliases)
    }

    fn emit_inserted_clause(&mut self, inserted_id: usize) -> Result<usize, CodeGenError> {
        if let Some(&index) = self.inserted_to_trace.get(&inserted_id) {
            return Ok(index);
        }
        if !self.emitting_inserted_ids.insert(inserted_id) {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "cycle while emitting inserted clause {}",
                inserted_id
            )));
        }
        self.cheap_emission_depth += 1;
        let result = match self.derivation_checker.inserted_clause(inserted_id) {
            Some(inserted) => self.emit_clause(inserted.clause, inserted.reason),
            None => Err(CodeGenError::GeneratedBadCode(format!(
                "missing inserted clause {}",
                inserted_id
            ))),
        };
        self.cheap_emission_depth -= 1;
        self.emitting_inserted_ids.remove(&inserted_id);
        if let Ok(index) = result {
            self.inserted_to_trace.insert(inserted_id, index);
        }
        result
    }

    fn emit_clause(&mut self, clause: Clause, reason: StepReason) -> Result<usize, CodeGenError> {
        if let Some(index) = self.available.get(&clause) {
            return Ok(*index);
        }
        let (code, generic) = self.serialize_clause_step(&clause)?;

        if self
            .shadow_checker
            .check_clause_direct_for_trace(&clause, &self.kernel_context)
            .is_some()
        {
            return self.push_step(TraceRule::Claim, code, vec![], clause, generic, vec![]);
        }

        if matches!(reason, StepReason::EqualityGraph) {
            if let Some(index) =
                self.emit_unit_resolution_support(code.clone(), clause.clone(), generic)?
            {
                return Ok(index);
            }
            if let Some(index) =
                self.emit_positive_and_intro_support(code.clone(), clause.clone(), generic)?
            {
                return Ok(index);
            }
        }

        if let StepReason::VariableSimplification(dependencies) = &reason {
            if let Some(index) = self.emit_variable_simplification_support_from_dependencies(
                code.clone(),
                clause.clone(),
                generic,
                dependencies,
            )? {
                return Ok(index);
            }

            let mut premises = vec![];
            let mut missing_dependencies = vec![];
            for &dependency in dependencies {
                let source_index = if let Some(&source_index) =
                    self.inserted_to_trace.get(&dependency)
                {
                    source_index
                } else if self
                    .derivation_checker
                    .inserted_clause(dependency)
                    .is_some()
                {
                    let source_index = self.emit_inserted_clause(dependency).map_err(|err| {
                        CodeGenError::GeneratedBadCode(format!(
                            "failed to emit dependency {} while writing inserted clause {}: {}",
                            dependency, clause, err
                        ))
                    })?;
                    self.inserted_to_trace.insert(dependency, source_index);
                    source_index
                } else {
                    missing_dependencies.push(dependency);
                    continue;
                };
                if !premises.contains(&source_index) {
                    premises.push(source_index);
                }
            }
            if !missing_dependencies.is_empty() {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "variable simplification for {} references missing dependencies {:?}",
                    clause, missing_dependencies
                )));
            }
            if premises.is_empty() {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "variable simplification for {} had no emitted premises from dependencies {:?}",
                    clause, dependencies
                )));
            }
            if self.eq_step_replays(&premises, &clause) {
                self.sort_eq_premises_for_replay(&mut premises);
                return self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![]);
            }
            let premise_debug = premises
                .iter()
                .map(|premise| format!("{}: {}", premise, self.step_clauses[*premise].primary))
                .collect::<Vec<_>>()
                .join("; ");
            return Err(CodeGenError::GeneratedBadCode(format!(
                "variable simplification for {} did not replay from dependencies {:?}; premises: {}",
                clause, dependencies, premise_debug
            )));
        }

        if let Some(source_id) = reason.dependency() {
            let source_index = if let Some(&source_index) = self.inserted_to_trace.get(&source_id) {
                Some(source_index)
            } else if self.derivation_checker.inserted_clause(source_id).is_some() {
                let source_index = self.emit_inserted_clause(source_id).map_err(|err| {
                    CodeGenError::GeneratedBadCode(format!(
                        "failed to emit dependency {} while writing inserted clause {}: {}",
                        source_id, clause, err
                    ))
                })?;
                self.inserted_to_trace.insert(source_id, source_index);
                Some(source_index)
            } else {
                None
            };

            if let Some(source_index) = source_index {
                let source_candidates: Vec<Clause> =
                    self.step_clauses[source_index].all().cloned().collect();
                let rule = source_candidates.iter().find_map(|source| match reason {
                    StepReason::EqualityResolution(_)
                        if self.shadow_checker.equality_resolution_derives_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        ) =>
                    {
                        Some(TraceRule::Er)
                    }
                    StepReason::EqualityFactoring(_)
                        if self.shadow_checker.equality_factoring_derives_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        ) =>
                    {
                        Some(TraceRule::Ef)
                    }
                    StepReason::Extensionality(_)
                        if self.shadow_checker.extensionality_derives_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        ) =>
                    {
                        Some(TraceRule::Ext)
                    }
                    StepReason::Injectivity(_)
                        if self.shadow_checker.injectivity_derives_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        ) =>
                    {
                        Some(TraceRule::Inj)
                    }
                    StepReason::VariableSimplification(_)
                        if self.shadow_checker.equality_graph_derives_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        ) =>
                    {
                        Some(TraceRule::Eq)
                    }
                    StepReason::BooleanReduction(_)
                        if self
                            .shadow_checker
                            .boolean_reduction_detail_for_trace(
                                source,
                                &clause,
                                &self.kernel_context,
                            )
                            .is_some() =>
                    {
                        Some(TraceRule::Br)
                    }
                    _ => None,
                });
                if let Some(rule) = rule {
                    if matches!(rule, TraceRule::Br) {
                        return self.push_br_step(code, source_index, clause, generic, vec![]);
                    }
                    return self.push_step(rule, code, vec![source_index], clause, generic, vec![]);
                }
            }
        }

        if matches!(reason, StepReason::BooleanReduction(_)) {
            for source_index in (0..self.step_clauses.len()).rev() {
                if self
                    .boolean_reduction_detail_for_step(source_index, &clause)
                    .is_some()
                {
                    return self.push_br_step(code, source_index, clause, generic, vec![]);
                }
            }
        }

        if !matches!(reason, StepReason::BooleanReduction(_)) {
            for source_index in (0..self.step_clauses.len()).rev() {
                if self
                    .boolean_reduction_detail_for_step(source_index, &clause)
                    .is_some()
                {
                    return self.push_br_step(code, source_index, clause, generic, vec![]);
                }
            }
        }

        for inserted_id in (0..self.derivation_checker.inserted_len()).rev() {
            let Some(source_inserted) = self.derivation_checker.inserted_clause(inserted_id) else {
                continue;
            };
            if source_inserted.clause == clause {
                continue;
            }
            if self
                .shadow_checker
                .boolean_reduction_detail_for_trace(
                    &source_inserted.clause,
                    &clause,
                    &self.kernel_context,
                )
                .is_none()
            {
                continue;
            }
            let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                continue;
            };
            return self.push_br_step(code, source_index, clause, generic, vec![]);
        }

        if matches!(reason, StepReason::EqualityGraph) {
            for source_index in (0..self.step_clauses.len()).rev() {
                let premises = vec![source_index];
                if self.eq_step_replays(&premises, &clause) {
                    return self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![]);
                }
            }
        }

        if !matches!(reason, StepReason::EqualityGraph) {
            for source_index in (0..self.step_clauses.len()).rev() {
                let premises = vec![source_index];
                if self.eq_step_replays(&premises, &clause) {
                    return self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![]);
                }
            }
        }

        if matches!(reason, StepReason::EqualityGraph) {
            for inserted_id in (0..self.base_checker.inserted_len()).rev() {
                let Some(source_inserted) = self.base_checker.inserted_clause(inserted_id) else {
                    continue;
                };
                if source_inserted.clause == clause {
                    continue;
                }
                if !self.source_clause_eq_replays(&source_inserted.clause, &clause, false) {
                    continue;
                }
                let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                    continue;
                };
                return self.push_step(
                    TraceRule::Eq,
                    code,
                    vec![source_index],
                    clause,
                    generic,
                    vec![],
                );
            }

            for inserted_id in (0..self.base_checker.inserted_len()).rev().take(256) {
                let Some(source_inserted) = self.base_checker.inserted_clause(inserted_id) else {
                    continue;
                };
                if source_inserted.clause == clause {
                    continue;
                }
                if !self.source_clause_eq_replays(&source_inserted.clause, &clause, true) {
                    continue;
                }
                let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                    continue;
                };
                return self.push_step(
                    TraceRule::Eq,
                    code,
                    vec![source_index],
                    clause,
                    generic,
                    vec![],
                );
            }

            for inserted_id in (0..self.derivation_checker.inserted_len()).rev() {
                let Some(source_inserted) = self.derivation_checker.inserted_clause(inserted_id)
                else {
                    continue;
                };
                if source_inserted.clause == clause {
                    continue;
                }
                if !self.source_clause_eq_replays(&source_inserted.clause, &clause, false) {
                    continue;
                }
                let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                    continue;
                };
                return self.push_step(
                    TraceRule::Eq,
                    code,
                    vec![source_index],
                    clause,
                    generic,
                    vec![],
                );
            }

            for inserted_id in (0..self.derivation_checker.inserted_len()).rev().take(256) {
                let Some(source_inserted) = self.derivation_checker.inserted_clause(inserted_id)
                else {
                    continue;
                };
                if source_inserted.clause == clause {
                    continue;
                }
                if !self.source_clause_eq_replays(&source_inserted.clause, &clause, true) {
                    continue;
                }
                let Ok(source_index) = self.emit_inserted_clause(inserted_id) else {
                    continue;
                };
                return self.push_step(
                    TraceRule::Eq,
                    code,
                    vec![source_index],
                    clause,
                    generic,
                    vec![],
                );
            }
        }

        if self
            .shadow_checker
            .boolean_reduction_proves_for_trace(&clause, &self.kernel_context)
        {
            return self.push_step(TraceRule::BrIntro, code, vec![], clause, generic, vec![]);
        }
        if self.eager_boolean_reduction_intro_replays(&clause) {
            if let Some(index) =
                self.emit_eager_boolean_reduction_path(code.clone(), clause.clone(), generic, &[])?
            {
                return Ok(index);
            }
        }
        if matches!(reason, StepReason::EqualityGraph) {
            if let Some(dependencies) = self
                .derivation_checker
                .equality_graph_dependencies_for_clause_for_trace(&clause, &self.kernel_context)
            {
                for dependency in dependencies {
                    let _ = self.emit_inserted_clause(dependency);
                }
                if let Some(index) =
                    self.emit_multi_premise_eq_step(code.clone(), clause.clone(), generic)?
                {
                    return Ok(index);
                }
            }
            let premises: Vec<usize> = (0..self.step_clauses.len()).collect();
            if let Some(index) = self.emit_eager_boolean_reduction_path(
                code.clone(),
                clause.clone(),
                generic,
                &premises,
            )? {
                return Ok(index);
            }
            for source_index in (0..self.step_clauses.len()).rev() {
                if self
                    .boolean_reduction_detail_for_step(source_index, &clause)
                    .is_some()
                {
                    return self.push_br_step(code, source_index, clause, generic, vec![]);
                }
            }
            if let Some(index) =
                self.emit_multi_premise_eq_step(code.clone(), clause.clone(), generic)?
            {
                return Ok(index);
            }
            if let Some(index) =
                self.emit_unit_resolution_support(code.clone(), clause.clone(), generic)?
            {
                return Ok(index);
            }
            if let Some(index) =
                self.emit_positive_and_intro_support(code.clone(), clause.clone(), generic)?
            {
                return Ok(index);
            }
            if let Some(index) =
                self.emit_variable_simplification_support(code.clone(), clause.clone(), generic)?
            {
                return Ok(index);
            }
        }
        if let Some(index) =
            self.emit_multi_premise_eq_step(code.clone(), clause.clone(), generic)?
        {
            return Ok(index);
        }
        if let Some(index) =
            self.emit_variable_simplification_support(code.clone(), clause.clone(), generic)?
        {
            return Ok(index);
        }
        // Last resort: the same reduction-witness engine that backs claim emission.
        // Boolean-reduction sources and dependency clauses can need it for the same
        // reason claims do: the clause is justified by reduction reasoning without
        // being an exact member of anything emitted yet.
        if let Some(index) = self.emit_clause_via_reduction_witness(&clause)? {
            return Ok(index);
        }

        let dependency_context = reason
            .dependency()
            .map(|source_id| {
                if let Some(source_index) = self.inserted_to_trace.get(&source_id) {
                    format!(
                        "; dependency {} mapped to certificate trace step {}: {}",
                        source_id, source_index, self.step_clauses[*source_index].primary
                    )
                } else if let Some(source_inserted) =
                    self.derivation_checker.inserted_clause(source_id)
                {
                    format!(
                        "; dependency {} is unmapped inserted clause: {} ({:?})",
                        source_id, source_inserted.clause, source_inserted.reason
                    )
                } else {
                    format!("; dependency {} is not available", source_id)
                }
            })
            .unwrap_or_default();
        let equality_graph_context = if matches!(reason, StepReason::EqualityGraph) {
            let mut checker = self.derivation_checker.clone();
            let direct = checker
                .check_clause_direct_for_trace(&clause, &self.kernel_context)
                .is_some();
            let dependencies = self
                .derivation_checker
                .equality_graph_dependencies_for_clause_for_trace(&clause, &self.kernel_context)
                .map(|deps| format!("{:?}", deps))
                .unwrap_or_else(|| "none".to_string());
            let base_dependencies = self
                .base_checker
                .equality_graph_dependencies_for_clause_for_trace(&clause, &self.kernel_context)
                .map(|deps| format!("{:?}", deps))
                .unwrap_or_else(|| "none".to_string());
            let emitted = self
                .step_clauses
                .iter()
                .map(|clauses| clauses.primary.to_string())
                .collect::<Vec<_>>()
                .join(" | ");
            format!(
                "; equality graph direct: {}; literals: {}; deps: {}; base deps: {}; emitted steps: {}; emitted clauses: {}",
                direct,
                clause.len(),
                dependencies,
                base_dependencies,
                self.steps.len(),
                emitted
            )
        } else {
            String::new()
        };
        if std::env::var("ACORN_DEBUG_CERT").is_ok() {
            eprintln!("EMIT-FAIL clause={} reason={:?}", clause, reason);
            for (i, clauses) in self.step_clauses.iter().enumerate() {
                eprintln!("  trace step {}: {}", i, clauses.primary);
            }
            for (avail, idx) in self.available.iter() {
                eprintln!("  available[{}]: {}", idx, avail);
            }
        }
        Err(CodeGenError::GeneratedBadCode(format!(
            "could not emit inserted clause to certificate trace: {} ({:?}){}{}",
            clause, reason, dependency_context, equality_graph_context
        )))
    }

    fn emit_multi_premise_eq_step(
        &mut self,
        code: String,
        clause: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        if self.step_clauses.is_empty() {
            return Ok(None);
        }
        let premises: Vec<usize> = (0..self.step_clauses.len()).collect();
        if !self.eq_step_replays(&premises, &clause) {
            return Ok(None);
        }
        self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![])
            .map(Some)
    }

    fn split_positive_and_clause(clause: &Clause) -> Option<(Clause, Clause)> {
        let [literal] = clause.literals.as_slice() else {
            return None;
        };
        if !literal.positive || !literal.right.is_true() {
            return None;
        }
        let (head, args) = literal.left.as_ref().split_application_multi()?;
        if args.len() != 2 {
            return None;
        }
        match head.as_ref().decompose() {
            Decomposition::Atom(Atom::Symbol(Symbol::And)) => Some((
                Clause::new(
                    vec![Literal::positive(args[0].clone())],
                    clause.get_local_context(),
                ),
                Clause::new(
                    vec![Literal::positive(args[1].clone())],
                    clause.get_local_context(),
                ),
            )),
            _ => None,
        }
    }

    fn emit_positive_and_intro_support(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        let mut seen = HashSet::new();
        self.emit_positive_and_intro_support_inner(code, target, generic, &mut seen)
    }

    fn emit_positive_and_intro_support_inner(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
        seen: &mut HashSet<Clause>,
    ) -> Result<Option<usize>, CodeGenError> {
        if !seen.insert(target.clone()) {
            return Ok(None);
        }
        let Some((left, right)) = Self::split_positive_and_clause(&target) else {
            return Ok(None);
        };

        let before_steps = self.steps.len();
        let before_step_clauses = self.step_clauses.len();
        let before_available = self.available.clone();
        let before_inserted_to_trace = self.inserted_to_trace.clone();
        let before_shadow = self.shadow_checker.clone();

        let mut premises = vec![];
        let mut ok = true;
        for component in [left, right] {
            match self.emit_supporting_component_clause(component, seen)? {
                Some(index) => {
                    if !premises.contains(&index) {
                        premises.push(index);
                    }
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }

        if ok && self.eq_step_replays(&premises, &target) {
            self.sort_eq_premises_for_replay(&mut premises);
            return self
                .push_step(TraceRule::Eq, code, premises, target, generic, vec![])
                .map(Some);
        }

        self.steps.truncate(before_steps);
        self.step_clauses.truncate(before_step_clauses);
        self.available = before_available;
        self.inserted_to_trace = before_inserted_to_trace;
        self.shadow_checker = before_shadow;
        Ok(None)
    }

    fn emit_supporting_component_clause(
        &mut self,
        component: Clause,
        seen: &mut HashSet<Clause>,
    ) -> Result<Option<usize>, CodeGenError> {
        if let Some(index) = self.available.get(&component) {
            return Ok(Some(*index));
        }

        let (code, generic) = self.serialize_clause_step(&component)?;

        if self
            .shadow_checker
            .check_clause_direct_for_trace(&component, &self.kernel_context)
            .is_some()
        {
            return self
                .push_step(TraceRule::Claim, code, vec![], component, generic, vec![])
                .map(Some);
        }

        if self
            .shadow_checker
            .boolean_reduction_proves_for_trace(&component, &self.kernel_context)
        {
            return self
                .push_step(TraceRule::BrIntro, code, vec![], component, generic, vec![])
                .map(Some);
        }

        for source_index in (0..self.step_clauses.len()).rev() {
            if self
                .boolean_reduction_detail_for_step(source_index, &component)
                .is_some()
            {
                return self
                    .push_br_step(
                        code.clone(),
                        source_index,
                        component.clone(),
                        generic,
                        vec![],
                    )
                    .map(Some);
            }
        }

        for source_index in (0..self.step_clauses.len()).rev() {
            let premises = vec![source_index];
            if self.eq_step_replays(&premises, &component) {
                return self
                    .push_step(
                        TraceRule::Eq,
                        code.clone(),
                        premises,
                        component.clone(),
                        generic,
                        vec![],
                    )
                    .map(Some);
            }
        }

        if let Some(index) =
            self.emit_multi_premise_eq_step(code.clone(), component.clone(), generic)?
        {
            return Ok(Some(index));
        }

        if let Some(index) =
            self.emit_component_from_base_equality(code.clone(), component.clone(), generic)?
        {
            return Ok(Some(index));
        }

        if let Some(index) =
            self.emit_component_from_base_conjunction(code.clone(), component.clone(), generic)?
        {
            return Ok(Some(index));
        }

        if let Some(inserted_id) = self.derivation_checker.exact_clause_id(&component) {
            let checkpoint = self.checkpoint();
            match self.emit_inserted_clause(inserted_id) {
                Ok(index) => {
                    return Ok(Some(index));
                }
                Err(_) => self.restore(checkpoint),
            }
        }

        if let Some(inserted_id) = self.base_checker.exact_clause_id(&component) {
            if let Some(inserted) = self.base_checker.inserted_clause(inserted_id) {
                let checkpoint = self.checkpoint();
                match self.emit_clause(inserted.clause, inserted.reason) {
                    Ok(index) => {
                        return Ok(Some(index));
                    }
                    Err(_) => self.restore(checkpoint),
                }
            }
        }

        let premises: Vec<usize> = (0..self.step_clauses.len()).collect();
        let checkpoint = self.checkpoint();
        match self.emit_eager_boolean_reduction_path(
            code.clone(),
            component.clone(),
            generic,
            &premises,
        ) {
            Ok(Some(index)) => {
                return Ok(Some(index));
            }
            Ok(None) => {}
            Err(_) => {}
        }
        self.restore(checkpoint);

        if let Some(index) = self.emit_positive_and_intro_support_inner(
            code.clone(),
            component.clone(),
            generic,
            seen,
        )? {
            return Ok(Some(index));
        }

        Ok(None)
    }

    fn emit_component_from_base_conjunction(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        let base_clauses = (0..self.base_checker.inserted_len())
            .filter_map(|inserted_id| self.base_checker.inserted_clause(inserted_id))
            .collect::<Vec<_>>();

        for inserted in base_clauses.into_iter().rev() {
            let source = inserted.clause;
            if source == target || Self::split_positive_and_clause(&source).is_none() {
                continue;
            }
            let Some(path) = self.find_boolean_reduction_path(&source, &target, 6) else {
                continue;
            };

            let checkpoint = self.checkpoint();
            let Some(mut source_index) = self.emit_base_fact_clause(source)? else {
                self.restore(checkpoint);
                continue;
            };

            let mut ok = true;
            for (step_clause, br_detail) in path {
                let (step_code, step_generic) = self.serialize_clause_step(&step_clause)?;
                match self.push_step_with_br_detail(
                    TraceRule::Br,
                    step_code,
                    vec![source_index],
                    step_clause.clone(),
                    step_generic,
                    vec![],
                    Some(br_detail),
                ) {
                    Ok(index) => source_index = index,
                    Err(_) => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                self.restore(checkpoint);
                continue;
            }

            if self.step_clauses[source_index].primary == target {
                return Ok(Some(source_index));
            }
            if self.eq_step_replays(&[source_index], &target) {
                return self
                    .push_step(
                        TraceRule::Eq,
                        code,
                        vec![source_index],
                        target,
                        generic,
                        vec![],
                    )
                    .map(Some);
            }
            self.restore(checkpoint);
        }

        Ok(None)
    }

    fn emit_component_from_base_equality(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        let base_clauses = (0..self.base_checker.inserted_len())
            .filter_map(|inserted_id| self.base_checker.inserted_clause(inserted_id))
            .collect::<Vec<_>>();

        for inserted in base_clauses.into_iter().rev() {
            let equality_clause = inserted.clause;
            let [literal] = equality_clause.literals.as_slice() else {
                continue;
            };
            if !literal.positive || literal.right.is_true() {
                continue;
            }

            for (and_term, fact_term) in [
                (literal.left.clone(), literal.right.clone()),
                (literal.right.clone(), literal.left.clone()),
            ] {
                let and_clause = Clause::new(
                    vec![Literal::positive(and_term)],
                    equality_clause.get_local_context(),
                );
                if Self::split_positive_and_clause(&and_clause).is_none() {
                    continue;
                }
                let Some(path) = self.find_boolean_reduction_path(&and_clause, &target, 4) else {
                    continue;
                };
                let fact_clause = Clause::new(
                    vec![Literal::positive(fact_term)],
                    equality_clause.get_local_context(),
                );

                let checkpoint = self.checkpoint();
                let Some(equality_index) = self.emit_base_fact_clause(equality_clause.clone())?
                else {
                    self.restore(checkpoint);
                    continue;
                };
                let Some(fact_index) = self.emit_base_fact_clause(fact_clause)? else {
                    self.restore(checkpoint);
                    continue;
                };

                let mut premises = vec![equality_index, fact_index];
                if !self.eq_step_replays(&premises, &and_clause) {
                    self.restore(checkpoint);
                    continue;
                }
                self.sort_eq_premises_for_replay(&mut premises);
                let (and_code, and_generic) = self.serialize_clause_step(&and_clause)?;
                let mut source_index = self.push_step(
                    TraceRule::Eq,
                    and_code,
                    premises,
                    and_clause,
                    and_generic,
                    vec![],
                )?;

                let mut ok = true;
                for (step_clause, br_detail) in path {
                    let (step_code, step_generic) = self.serialize_clause_step(&step_clause)?;
                    match self.push_step_with_br_detail(
                        TraceRule::Br,
                        step_code,
                        vec![source_index],
                        step_clause.clone(),
                        step_generic,
                        vec![],
                        Some(br_detail),
                    ) {
                        Ok(index) => source_index = index,
                        Err(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    self.restore(checkpoint);
                    continue;
                }

                if self.step_clauses[source_index].primary == target {
                    return Ok(Some(source_index));
                }
                if self.eq_step_replays(&[source_index], &target) {
                    return self
                        .push_step(
                            TraceRule::Eq,
                            code,
                            vec![source_index],
                            target,
                            generic,
                            vec![],
                        )
                        .map(Some);
                }
                self.restore(checkpoint);
            }
        }

        Ok(None)
    }

    fn emit_base_fact_clause(&mut self, clause: Clause) -> Result<Option<usize>, CodeGenError> {
        if let Some(index) = self.available.get(&clause) {
            return Ok(Some(*index));
        }
        if self
            .shadow_checker
            .check_clause_direct_for_trace(&clause, &self.kernel_context)
            .is_none()
        {
            return Ok(None);
        }
        let (code, generic) = self.serialize_clause_step(&clause)?;
        self.push_step(TraceRule::Fact, code, vec![], clause, generic, vec![])
            .map(Some)
    }

    fn find_boolean_reduction_path(
        &self,
        source: &Clause,
        target: &Clause,
        max_depth: usize,
    ) -> Option<Vec<(Clause, (BooleanReductionKind, usize))>> {
        let mut seen = HashSet::new();
        self.find_boolean_reduction_path_inner(source, target, max_depth, &mut seen)
    }

    fn find_boolean_reduction_path_inner(
        &self,
        source: &Clause,
        target: &Clause,
        max_depth: usize,
        seen: &mut HashSet<Clause>,
    ) -> Option<Vec<(Clause, (BooleanReductionKind, usize))>> {
        if !seen.insert(source.clone()) {
            return None;
        }
        for (kind, literal_index, _trace) in source
            .find_boolean_reduction_kinds_with_locations_with_options(&self.kernel_context, true)
        {
            let Some(candidate) = self.shadow_checker.apply_boolean_reduction_for_trace(
                source,
                kind,
                literal_index,
                &self.kernel_context,
            ) else {
                continue;
            };
            let detail = (kind, literal_index);
            if candidate == *target {
                return Some(vec![(candidate, detail)]);
            }
            if max_depth > 0 {
                if let Some(mut path) =
                    self.find_boolean_reduction_path_inner(&candidate, target, max_depth - 1, seen)
                {
                    let mut answer = vec![(candidate, detail)];
                    answer.append(&mut path);
                    return Some(answer);
                }
            }
        }
        None
    }

    fn emit_unit_resolution_support(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        for source_index in (0..self.step_clauses.len()).rev() {
            let source_candidates: Vec<Clause> =
                self.step_clauses[source_index].all().cloned().collect();
            for source in source_candidates {
                if source.literals.len() != target.literals.len() + 1 {
                    continue;
                }
                let mut used_target = vec![false; target.literals.len()];
                let mut extras = vec![];
                for source_literal in &source.literals {
                    let mut matched = false;
                    for (target_index, target_literal) in target.literals.iter().enumerate() {
                        if !used_target[target_index] && source_literal == target_literal {
                            used_target[target_index] = true;
                            matched = true;
                            break;
                        }
                    }
                    if !matched {
                        extras.push(source_literal.clone());
                    }
                }
                if extras.len() != 1 || used_target.iter().any(|used| !used) {
                    continue;
                }
                let other_literal = extras.remove(0);
                let complement =
                    Clause::new(vec![other_literal.negate()], source.get_local_context());
                let complement_index = if let Some(index) = self.available.get(&complement) {
                    *index
                } else {
                    if self
                        .shadow_checker
                        .check_clause_direct_for_trace(&complement, &self.kernel_context)
                        .is_none()
                        && self
                            .derivation_checker
                            .exact_clause_id(&complement)
                            .is_none()
                        && self.base_checker.exact_clause_id(&complement).is_none()
                    {
                        continue;
                    }

                    let before_steps = self.steps.len();
                    let before_step_clauses = self.step_clauses.len();
                    let before_available = self.available.clone();
                    let before_inserted_to_trace = self.inserted_to_trace.clone();
                    let before_shadow = self.shadow_checker.clone();

                    match self.emit_literal_complement(&source, &other_literal) {
                        Ok(Some(index)) => {
                            let premises = vec![source_index, index];
                            if self.eq_step_replays(&premises, &target) {
                                return self
                                    .push_step(
                                        TraceRule::Eq,
                                        code,
                                        premises,
                                        target,
                                        generic,
                                        vec![],
                                    )
                                    .map(Some);
                            }
                            self.steps.truncate(before_steps);
                            self.step_clauses.truncate(before_step_clauses);
                            self.available = before_available;
                            self.inserted_to_trace = before_inserted_to_trace;
                            self.shadow_checker = before_shadow;
                            continue;
                        }
                        Ok(None) | Err(_) => {
                            self.steps.truncate(before_steps);
                            self.step_clauses.truncate(before_step_clauses);
                            self.available = before_available;
                            self.inserted_to_trace = before_inserted_to_trace;
                            self.shadow_checker = before_shadow;
                            continue;
                        }
                    }
                };
                let premises = vec![source_index, complement_index];
                if self.eq_step_replays(&premises, &target) {
                    return self
                        .push_step(TraceRule::Eq, code, premises, target, generic, vec![])
                        .map(Some);
                }
            }
        }
        Ok(None)
    }

    fn extra_source_literals(source: &Clause, target: &Clause) -> Option<Vec<Literal>> {
        if source.literals.len() <= target.literals.len() {
            return None;
        }

        let mut used_source = vec![false; source.literals.len()];
        for target_literal in &target.literals {
            let mut matched = false;
            for (source_index, source_literal) in source.literals.iter().enumerate() {
                if used_source[source_index] || source_literal != target_literal {
                    continue;
                }
                used_source[source_index] = true;
                matched = true;
                break;
            }
            if !matched {
                return None;
            }
        }

        let extras = source
            .literals
            .iter()
            .zip(used_source)
            .filter_map(|(literal, used)| (!used).then(|| literal.clone()))
            .collect::<Vec<_>>();
        (!extras.is_empty()).then_some(extras)
    }

    fn emit_literal_complement(
        &mut self,
        source: &Clause,
        literal: &Literal,
    ) -> Result<Option<usize>, CodeGenError> {
        let complement = Clause::new(vec![literal.negate()], source.get_local_context());
        if let Some(index) = self.available.get(&complement) {
            return Ok(Some(*index));
        }

        let (code, generic) = self.serialize_clause_step(&complement)?;
        if let Some(index) = self.emit_base_fact_clause(complement.clone())? {
            return Ok(Some(index));
        }

        if let Some(index) =
            self.emit_component_from_base_conjunction(code.clone(), complement.clone(), generic)?
        {
            return Ok(Some(index));
        }
        if let Some(index) =
            self.emit_component_from_base_equality(code.clone(), complement.clone(), generic)?
        {
            return Ok(Some(index));
        }
        if let Some(index) = self.emit_variable_simplification_support(code, complement, generic)? {
            return Ok(Some(index));
        }

        let complement = Clause::new(vec![literal.negate()], source.get_local_context());
        if let Some(inserted_id) = self.base_checker.exact_clause_id(&complement) {
            if let Some(inserted) = self.base_checker.inserted_clause(inserted_id) {
                return self.emit_clause(inserted.clause, inserted.reason).map(Some);
            }
        }

        if let Some(inserted_id) = self.derivation_checker.exact_clause_id(&complement) {
            return self.emit_inserted_clause(inserted_id).map(Some);
        }

        Ok(None)
    }

    fn emit_variable_simplification_support(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        if self.variable_support_depth > 0 {
            return Ok(None);
        }
        self.variable_support_depth += 1;
        let result = self.emit_variable_simplification_support_inner(code, target, generic);
        self.variable_support_depth -= 1;
        result
    }

    fn emit_variable_simplification_support_inner(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
    ) -> Result<Option<usize>, CodeGenError> {
        let mut candidates = Vec::new();
        for inserted_id in (0..self.derivation_checker.inserted_len()).rev().take(64) {
            if let Some(inserted) = self.derivation_checker.inserted_clause(inserted_id) {
                candidates.push(inserted);
            }
        }

        for inserted in candidates {
            let source = inserted.clause;
            if source == target {
                continue;
            }
            let Some(extras) = Self::extra_source_literals(&source, &target) else {
                continue;
            };
            if extras.len() > 8 {
                continue;
            }

            let before_steps = self.steps.len();
            let before_step_clauses = self.step_clauses.len();
            let before_available = self.available.clone();
            let before_inserted_to_trace = self.inserted_to_trace.clone();
            let before_shadow = self.shadow_checker.clone();

            let mut premises = Vec::with_capacity(extras.len() + 1);
            let mut ok = true;
            for extra in &extras {
                match self.emit_literal_complement(&source, extra)? {
                    Some(index) => premises.push(index),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                match self.emit_clause(source, inserted.reason) {
                    Ok(source_index) => {
                        premises.push(source_index);
                        if self.eq_step_replays(&premises, &target) {
                            return self
                                .push_step(TraceRule::Eq, code, premises, target, generic, vec![])
                                .map(Some);
                        }
                    }
                    Err(_) => ok = false,
                }
            }

            if !ok || !self.eq_step_replays(&premises, &target) {
                self.steps.truncate(before_steps);
                self.step_clauses.truncate(before_step_clauses);
                self.available = before_available;
                self.inserted_to_trace = before_inserted_to_trace;
                self.shadow_checker = before_shadow;
            }
        }

        Ok(None)
    }

    fn emit_variable_simplification_support_from_dependencies(
        &mut self,
        code: String,
        target: Clause,
        generic: bool,
        dependencies: &[usize],
    ) -> Result<Option<usize>, CodeGenError> {
        let mut candidates = Vec::new();
        for &dependency in dependencies {
            let Some(inserted) = self.derivation_checker.inserted_clause(dependency) else {
                continue;
            };
            candidates.push((dependency, inserted));
        }

        for (_dependency, inserted) in candidates {
            let source = inserted.clause;
            if source == target {
                continue;
            }
            let Some(extras) = Self::extra_source_literals(&source, &target) else {
                continue;
            };

            let before_steps = self.steps.len();
            let before_step_clauses = self.step_clauses.len();
            let before_available = self.available.clone();
            let before_inserted_to_trace = self.inserted_to_trace.clone();
            let before_shadow = self.shadow_checker.clone();

            let mut premises = Vec::with_capacity(extras.len() + 1);
            let mut ok = true;
            for extra in &extras {
                match self.emit_literal_complement(&source, extra)? {
                    Some(index) => premises.push(index),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                match self.emit_clause(source, inserted.reason) {
                    Ok(source_index) => {
                        premises.push(source_index);
                        if self.eq_step_replays(&premises, &target) {
                            self.sort_eq_premises_for_replay(&mut premises);
                            return self
                                .push_step(TraceRule::Eq, code, premises, target, generic, vec![])
                                .map(Some);
                        }
                    }
                    Err(_) => ok = false,
                }
            }

            if !ok || !self.eq_step_replays(&premises, &target) {
                self.steps.truncate(before_steps);
                self.step_clauses.truncate(before_step_clauses);
                self.available = before_available;
                self.inserted_to_trace = before_inserted_to_trace;
                self.shadow_checker = before_shadow;
            }
        }

        Ok(None)
    }

    fn emit_eager_boolean_reduction_path(
        &mut self,
        code: String,
        clause: Clause,
        generic: bool,
        premises: &[usize],
    ) -> Result<Option<usize>, CodeGenError> {
        if !self.emitting_local_inserted_ids.is_empty() {
            return Ok(None);
        }
        let mut local = self.base_checker.clone();
        local.set_eager_boolean_reductions(false);
        for &premise in premises {
            let Some(clauses) = self.step_clauses.get(premise) else {
                return Ok(None);
            };
            for clause in clauses.all() {
                local.insert_clause(clause, StepReason::PreviousClaim, &self.kernel_context);
            }
        }
        local.enable_eager_boolean_reductions(&self.kernel_context);
        if let Some(local_id) = local.exact_clause_id(&clause) {
            let index = self.emit_local_inserted_clause(&local, local_id, &mut HashSet::new())?;
            if self.step_clauses[index].primary == clause {
                return Ok(Some(index));
            }
            return self
                .push_step(TraceRule::Eq, code, vec![index], clause, generic, vec![])
                .map(Some);
        }
        if let Some(dependencies) =
            local.equality_graph_dependencies_for_clause_for_trace(&clause, &self.kernel_context)
        {
            let mut trace_premises = vec![];
            for dependency in dependencies {
                let Ok(index) =
                    self.emit_local_inserted_clause(&local, dependency, &mut HashSet::new())
                else {
                    continue;
                };
                if !trace_premises.contains(&index) {
                    trace_premises.push(index);
                }
            }
            if !trace_premises.is_empty() && self.eq_step_replays(&trace_premises, &clause) {
                self.sort_eq_premises_for_replay(&mut trace_premises);
                return self
                    .push_step(TraceRule::Eq, code, trace_premises, clause, generic, vec![])
                    .map(Some);
            }
        }
        Ok(None)
    }

    fn local_eager_cycle_error(local_id: usize) -> CodeGenError {
        CodeGenError::GeneratedBadCode(format!(
            "cycle while emitting local eager clause {}",
            local_id
        ))
    }

    fn emit_local_inserted_clause(
        &mut self,
        local: &Checker,
        local_id: usize,
        seen: &mut HashSet<usize>,
    ) -> Result<usize, CodeGenError> {
        let inserted = local.inserted_clause(local_id).ok_or_else(|| {
            CodeGenError::GeneratedBadCode(format!(
                "missing local eager inserted clause {}",
                local_id
            ))
        })?;
        if let Some(index) = self.available.get(&inserted.clause) {
            return Ok(*index);
        }
        if !seen.insert(local_id) {
            return Err(Self::local_eager_cycle_error(local_id));
        }
        if !self.emitting_local_inserted_ids.insert(local_id) {
            return Err(Self::local_eager_cycle_error(local_id));
        }

        self.cheap_emission_depth += 1;
        let result = (|| {
            if let Some(source_id) = inserted.reason.dependency() {
                let source_index = self.emit_local_inserted_clause(local, source_id, seen)?;
                let source_candidates: Vec<Clause> =
                    self.step_clauses[source_index].all().cloned().collect();
                let (code, generic) = self.serialize_clause_step(&inserted.clause)?;
                let rule = source_candidates
                    .iter()
                    .find_map(|source| match inserted.reason {
                        StepReason::EqualityResolution(_)
                            if self.shadow_checker.equality_resolution_derives_for_trace(
                                source,
                                &inserted.clause,
                                &self.kernel_context,
                            ) =>
                        {
                            Some(TraceRule::Er)
                        }
                        StepReason::EqualityFactoring(_)
                            if self.shadow_checker.equality_factoring_derives_for_trace(
                                source,
                                &inserted.clause,
                                &self.kernel_context,
                            ) =>
                        {
                            Some(TraceRule::Ef)
                        }
                        StepReason::Extensionality(_)
                            if self.shadow_checker.extensionality_derives_for_trace(
                                source,
                                &inserted.clause,
                                &self.kernel_context,
                            ) =>
                        {
                            Some(TraceRule::Ext)
                        }
                        StepReason::Injectivity(_)
                            if self.shadow_checker.injectivity_derives_for_trace(
                                source,
                                &inserted.clause,
                                &self.kernel_context,
                            ) =>
                        {
                            Some(TraceRule::Inj)
                        }
                        StepReason::BooleanReduction(_)
                            if self
                                .shadow_checker
                                .boolean_reduction_detail_for_trace(
                                    source,
                                    &inserted.clause,
                                    &self.kernel_context,
                                )
                                .is_some() =>
                        {
                            Some(TraceRule::Br)
                        }
                        _ => None,
                    });
                if let Some(rule) = rule {
                    if matches!(rule, TraceRule::Br) {
                        return self.push_br_step(
                            code,
                            source_index,
                            inserted.clause,
                            generic,
                            vec![],
                        );
                    }
                    return self.push_step(
                        rule,
                        code,
                        vec![source_index],
                        inserted.clause,
                        generic,
                        vec![],
                    );
                }
            }

            self.emit_clause(inserted.clause, StepReason::PreviousClaim)
        })();
        self.cheap_emission_depth -= 1;
        self.emitting_local_inserted_ids.remove(&local_id);
        result
    }

    fn eq_step_replays(&self, premises: &[usize], clause: &Clause) -> bool {
        if premises.len() == 1 {
            let source_index = premises[0];
            let Some(source) = self
                .step_clauses
                .get(source_index)
                .map(|clauses| &clauses.primary)
            else {
                return false;
            };
            let mut ambient = self.shadow_checker.clone();
            if ambient.equality_graph_derives_for_trace(source, clause, &self.kernel_context) {
                return true;
            }
        }

        let mut local = Checker::new();
        local.set_eager_boolean_reductions(false);
        let mut sources = vec![];
        let mut ordered_premises = premises.to_vec();
        self.sort_eq_premises_for_replay(&mut ordered_premises);
        for &premise in &ordered_premises {
            let Some(clauses) = self.step_clauses.get(premise) else {
                return false;
            };
            for clause in clauses.all() {
                sources.push(clause.clone());
                local.insert_clause_for_trace(
                    clause,
                    StepReason::PreviousClaim,
                    &self.kernel_context,
                );
            }
        }
        if local
            .check_clause_direct_for_trace(clause, &self.kernel_context)
            .is_some()
        {
            return true;
        }
        sources.iter().any(|source| {
            local.equality_graph_derives_for_trace(source, clause, &self.kernel_context)
        })
    }

    fn sort_eq_premises_for_replay(&self, premises: &mut [usize]) {
        premises.sort_by_key(|premise| {
            self.step_clauses
                .get(*premise)
                .map(|clauses| clauses.primary.has_any_variable())
                .unwrap_or(true)
        });
    }

    fn source_clause_eq_replays(
        &self,
        source: &Clause,
        clause: &Clause,
        _allow_eager: bool,
    ) -> bool {
        let mut ambient = self.shadow_checker.clone();
        if ambient.equality_graph_derives_for_trace(source, clause, &self.kernel_context) {
            return true;
        }

        let mut local = Checker::new();
        local.insert_clause_for_trace(source, StepReason::PreviousClaim, &self.kernel_context);
        local
            .check_clause_direct_for_trace(clause, &self.kernel_context)
            .is_some()
    }

    fn serialize_clause_step(&self, clause: &Clause) -> Result<(String, bool), CodeGenError> {
        let mut candidates = vec![Certificate::serialize_clause_for_trace(
            clause,
            &self.kernel_context,
            self.bindings.as_ref(),
        )?];
        if clause.get_local_context().is_empty() {
            if let Ok(code) = Certificate::serialize_closed_clause_for_trace(
                clause,
                &self.kernel_context,
                self.bindings.as_ref(),
            ) {
                candidates.push((code, false));
            }
        }

        let mut parsed_summaries = vec![];
        for (code, preferred_generic) in candidates {
            let mut attempted = vec![];
            for generic in [preferred_generic, !preferred_generic] {
                if attempted.contains(&generic) {
                    continue;
                }
                attempted.push(generic);
                match self.parse_serialized_clause(&code, generic) {
                    Ok(parsed) if parsed == *clause => {
                        return Ok((code, generic));
                    }
                    Ok(parsed) => {
                        parsed_summaries.push(format!("{} / g={}: {}", code, generic, parsed));
                    }
                    Err(err) => {
                        parsed_summaries.push(format!("{} / g={}: {}", code, generic, err));
                    }
                }
            }
        }

        Err(CodeGenError::GeneratedBadCode(format!(
            "certificate trace serializer did not roundtrip clause {} ({})",
            clause,
            parsed_summaries.join("; ")
        )))
    }

    fn parse_serialized_clause(&self, code: &str, generic: bool) -> Result<Clause, CodeGenError> {
        let mut bindings = Cow::Owned(self.bindings.as_ref().clone());
        let mut kernel_context = Cow::Owned(self.kernel_context.as_ref().clone());
        match Certificate::parse_code_line(code, self.project, &mut bindings, &mut kernel_context)?
        {
            CertificateStep::Claim(claim) => {
                if generic {
                    Ok(claim.normalized_generic_clause())
                } else {
                    claim
                        .normalized_specialized_clause(&kernel_context)
                        .map_err(CodeGenError::GeneratedBadCode)
                }
            }
            CertificateStep::Satisfy(satisfy) => satisfy
                .justification
                .normalized_specialized_clause(&kernel_context)
                .map_err(CodeGenError::GeneratedBadCode),
        }
    }

    fn find_boolean_reduction_contradiction_path(
        &self,
        source: &Clause,
        seen: &mut HashSet<Clause>,
    ) -> Option<Vec<(Clause, (BooleanReductionKind, usize))>> {
        if !seen.insert(source.clone()) {
            return None;
        }
        for (kind, literal_index, _trace) in source
            .find_boolean_reduction_kinds_with_locations_with_options(&self.kernel_context, true)
        {
            let Some(candidate) = self.shadow_checker.apply_boolean_reduction_for_trace(
                source,
                kind,
                literal_index,
                &self.kernel_context,
            ) else {
                continue;
            };
            let detail = (kind, literal_index);
            let mut checker = self.shadow_checker.clone();
            checker.insert_clause_for_trace(
                &candidate,
                StepReason::PreviousClaim,
                &self.kernel_context,
            );
            if checker.has_contradiction() {
                return Some(vec![(candidate, detail)]);
            }
            if candidate.is_impossible() {
                return Some(vec![(candidate, detail)]);
            }
            if let Some(mut path) = self.find_boolean_reduction_contradiction_path(&candidate, seen)
            {
                path.insert(0, (candidate, detail));
                return Some(path);
            }
        }
        None
    }

    fn emit_boolean_reduction_contradiction_from_step(
        &mut self,
        source_index: usize,
    ) -> Result<bool, CodeGenError> {
        let source_candidates: Vec<Clause> =
            self.step_clauses[source_index].all().cloned().collect();
        for source in source_candidates {
            let Some(path) =
                self.find_boolean_reduction_contradiction_path(&source, &mut HashSet::new())
            else {
                continue;
            };
            let mut premise_index = source_index;
            for (clause, br_detail) in path {
                if let Some(existing_index) = self.available.get(&clause) {
                    premise_index = *existing_index;
                    continue;
                }
                let (code, generic) = if clause.is_impossible() {
                    ("false".to_string(), false)
                } else {
                    self.serialize_clause_step(&clause)?
                };
                premise_index = self.push_step_with_br_detail(
                    TraceRule::Br,
                    code,
                    vec![premise_index],
                    clause,
                    generic,
                    vec![],
                    Some(br_detail),
                )?;
            }
            if self.shadow_checker.has_contradiction() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn emit_boolean_reduction_closure_contradiction_from_step(
        &mut self,
        source_index: usize,
    ) -> Result<bool, CodeGenError> {
        let source_candidates: Vec<Clause> =
            self.step_clauses[source_index].all().cloned().collect();
        if !source_candidates.iter().any(|source| {
            self.shadow_checker
                .boolean_reduction_closes_for_trace(source, &self.kernel_context)
        }) {
            return Ok(false);
        }
        self.push_step(
            TraceRule::Contra,
            "false".to_string(),
            vec![source_index],
            Clause::impossible(),
            false,
            vec![],
        )?;
        Ok(true)
    }

    fn find_contradicting_step(&self, clause: &Clause, exclude: Option<usize>) -> Option<usize> {
        for source_index in (0..self.step_clauses.len()).rev() {
            if exclude == Some(source_index) {
                continue;
            }
            let source_candidates: Vec<Clause> =
                self.step_clauses[source_index].all().cloned().collect();
            if source_candidates.iter().any(|source| {
                Checker::clauses_contradict_for_trace(source, clause, &self.kernel_context)
            }) {
                return Some(source_index);
            }
        }
        None
    }

    fn emit_contra_step(&mut self, left: usize, right: usize) -> Result<(), CodeGenError> {
        self.push_step(
            TraceRule::Contra,
            "false".to_string(),
            vec![left, right],
            Clause::impossible(),
            false,
            vec![],
        )?;
        Ok(())
    }

    fn emit_derivation_contradiction_trace(&mut self) -> Result<bool, CodeGenError> {
        let Some(dependencies) = self
            .derivation_checker
            .contradiction_dependencies_for_trace()
        else {
            return Ok(false);
        };
        let mut emitted = vec![];
        for inserted_id in dependencies {
            let Some(inserted) = self.derivation_checker.inserted_clause(inserted_id) else {
                continue;
            };
            let Ok(step_index) = self.emit_inserted_clause(inserted_id) else {
                return Ok(false);
            };
            emitted.push((step_index, inserted.clause));
            if self.shadow_checker.has_contradiction() {
                return Ok(true);
            }
            if self.emit_boolean_reduction_closure_contradiction_from_step(step_index)? {
                return Ok(true);
            }
        }
        for (step_index, clause) in emitted {
            if let Some(source_index) = self.find_contradicting_step(&clause, Some(step_index)) {
                self.emit_contra_step(source_index, step_index)?;
                return Ok(true);
            }
        }
        Ok(self.shadow_checker.has_contradiction())
    }

    fn emit_boolean_reduction_contradiction(&mut self) -> Result<(), CodeGenError> {
        let impossible = Clause::impossible();
        if self.emit_derivation_contradiction_trace()? {
            return Ok(());
        }
        if self
            .emit_eager_boolean_reduction_path("false".to_string(), impossible.clone(), false, &[])?
            .is_some()
        {
            return Ok(());
        }
        for source_index in (0..self.step_clauses.len()).rev() {
            if self.emit_boolean_reduction_closure_contradiction_from_step(source_index)? {
                return Ok(());
            }
            if self.emit_boolean_reduction_contradiction_from_step(source_index)? {
                return Ok(());
            }
        }
        for inserted_id in (0..self.derivation_checker.inserted_len()).rev() {
            let Some(inserted) = self.derivation_checker.inserted_clause(inserted_id) else {
                continue;
            };
            let mut checker = self.shadow_checker.clone();
            checker.insert_clause_for_trace(
                &inserted.clause,
                StepReason::PreviousClaim,
                &self.kernel_context,
            );
            let contradicting_step = self.find_contradicting_step(&inserted.clause, None);
            if !checker.has_contradiction() && contradicting_step.is_none() {
                continue;
            }
            let Ok(step_index) = self.emit_inserted_clause(inserted_id) else {
                continue;
            };
            if let Some(source_index) = contradicting_step {
                self.emit_contra_step(source_index, step_index)?;
                return Ok(());
            }
            if self.shadow_checker.has_contradiction()
                || self.emit_boolean_reduction_contradiction_from_step(step_index)?
            {
                return Ok(());
            }
            if self.shadow_checker.has_contradiction() {
                return Ok(());
            }
        }
        for source_index in (0..self.step_clauses.len()).rev() {
            let source_candidates: Vec<Clause> =
                self.step_clauses[source_index].all().cloned().collect();
            if source_candidates.iter().any(|source| {
                self.shadow_checker.equality_resolution_derives_for_trace(
                    source,
                    &impossible,
                    &self.kernel_context,
                )
            }) {
                self.push_step(
                    TraceRule::Er,
                    "false".to_string(),
                    vec![source_index],
                    impossible.clone(),
                    false,
                    vec![],
                )?;
                if self.shadow_checker.has_contradiction() {
                    return Ok(());
                }
            }
        }
        if self
            .emit_multi_premise_eq_step("false".to_string(), impossible.clone(), false)?
            .is_some()
            && self.shadow_checker.has_contradiction()
        {
            return Ok(());
        }
        let mut failed_candidates = vec![];
        let mut progressed = true;
        while progressed {
            progressed = false;
            for inserted_id in (0..self.derivation_checker.inserted_len()).rev() {
                let Some(inserted) = self.derivation_checker.inserted_clause(inserted_id) else {
                    continue;
                };
                if self.available.contains_key(&inserted.clause) {
                    continue;
                }
                let clause = inserted.clause.clone();
                let reason = inserted.reason.clone();
                let before = self.steps.len();
                match self.emit_inserted_clause(inserted_id) {
                    Ok(step_index) => {
                        if self.steps.len() > before {
                            progressed = true;
                        }
                        if let Some(source_index) =
                            self.find_contradicting_step(&clause, Some(step_index))
                        {
                            self.emit_contra_step(source_index, step_index)?;
                            return Ok(());
                        }
                        if self.shadow_checker.has_contradiction()
                            || self.emit_boolean_reduction_contradiction_from_step(step_index)?
                        {
                            return Ok(());
                        }
                    }
                    Err(err) => {
                        if failed_candidates.len() < 8 {
                            failed_candidates.push(format!("{} ({:?}): {}", clause, reason, err));
                        }
                    }
                }
                if self.shadow_checker.has_contradiction() {
                    return Ok(());
                }
            }
        }
        let failed_context = if failed_candidates.is_empty() {
            String::new()
        } else {
            format!("; failed candidates: {}", failed_candidates.join("; "))
        };
        Err(CodeGenError::GeneratedBadCode(format!(
            "certificate trace proof closed in derivation checker, but no explicit contradiction path was found{}{}; emitted steps: {:?}",
            failed_context,
            self.deferred_claim_context(),
            self.steps
        )))
    }

    fn push_step(
        &mut self,
        rule: TraceRule,
        code: String,
        premises: Vec<usize>,
        clause: Clause,
        generic: bool,
        aliases: Vec<Clause>,
    ) -> Result<usize, CodeGenError> {
        self.push_step_with_br_detail(rule, code, premises, clause, generic, aliases, None)
    }

    fn push_step_with_br_detail(
        &mut self,
        rule: TraceRule,
        code: String,
        premises: Vec<usize>,
        clause: Clause,
        generic: bool,
        aliases: Vec<Clause>,
        br_detail: Option<(BooleanReductionKind, usize)>,
    ) -> Result<usize, CodeGenError> {
        if matches!(rule, TraceRule::Br) && br_detail.is_none() {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "certificate trace br step for {} was emitted without exact detail",
                code
            )));
        }
        let index = self.steps.len();
        let step_clauses = StepClauses::new(clause, aliases);
        self.insert_step_clauses(index, &step_clauses);
        self.step_clauses.push(step_clauses);
        self.steps.push(TraceStep::with_br_detail(
            rule, code, premises, generic, br_detail,
        ));
        Ok(index)
    }

    fn boolean_reduction_detail_for_step(
        &self,
        source_index: usize,
        target: &Clause,
    ) -> Option<(BooleanReductionKind, usize)> {
        self.step_clauses
            .get(source_index)
            .and_then(|source_clauses| {
                source_clauses.all().find_map(|source| {
                    self.shadow_checker.boolean_reduction_detail_for_trace(
                        source,
                        target,
                        &self.kernel_context,
                    )
                })
            })
    }

    fn push_br_step(
        &mut self,
        code: String,
        source_index: usize,
        clause: Clause,
        generic: bool,
        aliases: Vec<Clause>,
    ) -> Result<usize, CodeGenError> {
        let br_detail = self
            .boolean_reduction_detail_for_step(source_index, &clause)
            .ok_or_else(|| {
                CodeGenError::GeneratedBadCode(format!(
                    "failed to identify exact boolean-reduction detail for {}",
                    code
                ))
            })?;
        self.push_step_with_br_detail(
            TraceRule::Br,
            code,
            vec![source_index],
            clause,
            generic,
            aliases,
            Some(br_detail),
        )
    }

    fn push_candidate_step(
        &mut self,
        rule: TraceRule,
        code: String,
        premises: Vec<usize>,
        candidate: Clause,
        candidate_generic: bool,
        specialized: &Clause,
    ) -> Result<usize, CodeGenError> {
        let source_index = if matches!(rule, TraceRule::Br) {
            if premises.len() != 1 {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "certificate trace br candidate for {} has {} premises",
                    code,
                    premises.len()
                )));
            }
            self.push_br_step(
                code.clone(),
                premises[0],
                candidate.clone(),
                candidate_generic,
                vec![],
            )?
        } else {
            self.push_step(
                rule,
                code.clone(),
                premises,
                candidate.clone(),
                candidate_generic,
                vec![],
            )?
        };
        if candidate_generic && candidate != *specialized {
            self.push_step(
                TraceRule::Inst,
                code,
                vec![source_index],
                specialized.clone(),
                false,
                vec![],
            )
        } else {
            Ok(source_index)
        }
    }
}

struct TraceChecker<'a> {
    checker: Checker,
    project: &'a dyn ProjectLookup,
    bindings: Cow<'a, BindingMap>,
    kernel_context: Cow<'a, KernelContext>,
    clauses: Vec<StepClauses>,
    lines: Option<Vec<CertificateLine>>,
}

impl<'a> TraceChecker<'a> {
    fn new(
        checker: Checker,
        project: &'a dyn ProjectLookup,
        bindings: Cow<'a, BindingMap>,
        kernel_context: Cow<'a, KernelContext>,
        collect_lines: bool,
    ) -> Self {
        Self {
            checker,
            project,
            bindings,
            kernel_context,
            clauses: vec![],
            lines: collect_lines.then(Vec::new),
        }
    }

    fn into_checked(self, consumed_proof_steps: usize) -> CheckedCertificate {
        CheckedCertificate {
            lines: self.lines.unwrap_or_default(),
            consumed_proof_steps,
        }
    }

    fn check(mut self, proof: &ProofTrace) -> Result<CheckedCertificate, CodeGenError> {
        if self.checker.has_contradiction() {
            return Ok(self.into_checked(0));
        }
        for (index, step) in proof.steps.iter().enumerate() {
            if self.checker.has_contradiction() {
                return Ok(self.into_checked(index));
            }
            self.check_step(index, step)?;
        }
        if !self.checker.has_contradiction() {
            return Err(CodeGenError::GeneratedBadCode(
                "certificate trace proof does not result in a contradiction".to_string(),
            ));
        }
        Ok(self.into_checked(proof.steps.len()))
    }

    fn check_step(&mut self, index: usize, step: &TraceStep) -> Result<(), CodeGenError> {
        match step.rule {
            TraceRule::Fact | TraceRule::Claim => {
                let (generic, specialized, code) =
                    self.parse_required_claim_with_generic(index, step)?;
                let clause = if step.generic {
                    generic.clone()
                } else {
                    specialized.clone()
                };
                let aliases = if is_synthetic_generic_wrapper(&code) {
                    vec![]
                } else {
                    TraceWriter::claim_aliases(generic.clone(), &specialized)
                };
                let reason = self
                    .checker
                    .check_clause_direct_for_trace(&generic, &self.kernel_context)
                    .or_else(|| {
                        self.checker
                            .check_clause_direct_for_trace(&clause, &self.kernel_context)
                    })
                    .or_else(|| {
                        self.checker
                            .check_clause_direct_for_trace(&specialized, &self.kernel_context)
                    })
                    .ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace {:?} step {} is not directly known: {}",
                            step.rule,
                            index + 1,
                            code
                        ))
                    })?;
                self.accept_clause_with_aliases(clause, aliases, reason, code);
            }
            TraceRule::Inst => {
                if step.premises.len() != 1 {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace inst step {} needs exactly one premise",
                        index + 1
                    )));
                }
                let source_index = step.premises[0];
                let sources: Vec<Clause> = self
                    .clauses
                    .get(source_index)
                    .ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace inst step {} references missing premise {}",
                            index + 1,
                            source_index
                        ))
                    })?
                    .all()
                    .cloned()
                    .collect();
                let (generic, specialized, code) =
                    self.parse_required_claim_with_generic(index, step)?;
                let canonical_generic = self
                    .checker
                    .canonical_clause_for_trace(&generic, &self.kernel_context);
                let matches_generic = sources.iter().any(|source| {
                    *source == generic
                        || canonical_generic.as_ref().is_some_and(|canonical| {
                            self.checker
                                .canonical_clause_for_trace(source, &self.kernel_context)
                                .as_ref()
                                == Some(canonical)
                        })
                });
                if !matches_generic {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace inst step {} generic clause does not match premise {}: {}",
                        index + 1,
                        source_index,
                        code
                    )));
                }
                self.accept_clause(specialized, StepReason::PreviousClaim, code);
            }
            TraceRule::Br => {
                if step.premises.len() != 1 {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace br step {} needs exactly one premise",
                        index + 1
                    )));
                }
                let source_index = step.premises[0];
                let sources: Vec<Clause> = self
                    .clauses
                    .get(source_index)
                    .ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace br step {} references missing premise {}",
                            index + 1,
                            source_index
                        ))
                    })?
                    .all()
                    .cloned()
                    .collect();
                let (generic, specialized, code) =
                    self.parse_required_claim_with_generic(index, step)?;
                let result = if step.generic {
                    generic.clone()
                } else {
                    specialized.clone()
                };
                match (step.br_kind, step.br_literal_index) {
                    (Some(kind), Some(literal_index)) => {
                        let canonical_targets: Vec<Clause> = [&result, &generic, &specialized]
                            .iter()
                            .filter_map(|target| {
                                self.checker
                                    .canonical_clause_for_trace(target, &self.kernel_context)
                            })
                            .collect();
                        let reduced = sources.iter().any(|source| {
                            self.checker
                                .apply_boolean_reduction_for_trace(
                                    source,
                                    kind,
                                    literal_index,
                                    &self.kernel_context,
                                )
                                .is_some_and(|candidate| {
                                    candidate == result
                                        || candidate == generic
                                        || candidate == specialized
                                        || canonical_targets.contains(&candidate)
                                })
                        });
                        if !reduced {
                            let source_debug = sources
                                .iter()
                                .map(|source| source.to_string())
                                .collect::<Vec<_>>()
                                .join(" | ");
                            let candidate_debug = sources
                                .iter()
                                .filter_map(|source| {
                                    self.checker.apply_boolean_reduction_for_trace(
                                        source,
                                        kind,
                                        literal_index,
                                        &self.kernel_context,
                                    )
                                })
                                .map(|candidate| candidate.to_string())
                                .collect::<Vec<_>>()
                                .join(" | ");
                            return Err(CodeGenError::GeneratedBadCode(format!(
                                "certificate trace br step {} does not apply {:?}@{} from premise {} to {} (target: {}; candidate: {}; sources: {})",
                                index + 1,
                                kind,
                                literal_index,
                                source_index,
                                code,
                                result,
                                candidate_debug,
                                source_debug
                            )));
                        }
                    }
                    (None, None) => {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace br step {} is missing exact reduction detail",
                            index + 1
                        )));
                    }
                    _ => {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace br step {} has partial exact reduction detail",
                            index + 1
                        )));
                    }
                };
                self.accept_clause(result, StepReason::BooleanReduction(source_index), code);
            }
            TraceRule::BrIntro => {
                let (generic, specialized, code) =
                    self.parse_required_claim_with_generic(index, step)?;
                let result = if step.generic {
                    generic.clone()
                } else {
                    specialized.clone()
                };
                let justified = if step.premises.is_empty() {
                    // Legacy premise-less form: re-derive from known reductions.
                    self.checker
                        .boolean_reduction_proves_for_trace(&generic, &self.kernel_context)
                        || self
                            .checker
                            .boolean_reduction_proves_for_trace(&result, &self.kernel_context)
                        || self
                            .checker
                            .boolean_reduction_proves_for_trace(&specialized, &self.kernel_context)
                } else {
                    // Premise-bearing form: the premises must jointly form one of the
                    // clause's reduction sets, so the check is local to this step.
                    let mut premise_clauses = Vec::new();
                    for &premise in &step.premises {
                        let Some(step_clauses) = self.clauses.get(premise) else {
                            return Err(CodeGenError::GeneratedBadCode(format!(
                                "certificate trace br_intro step {} references missing premise {}",
                                index + 1,
                                premise
                            )));
                        };
                        premise_clauses.extend(step_clauses.all().cloned());
                    }
                    let mut targets = vec![&result];
                    if specialized != result {
                        targets.push(&specialized);
                    }
                    if generic != result && generic != specialized {
                        targets.push(&generic);
                    }
                    targets.iter().any(|target| {
                        self.checker
                            .checker_boolean_reduction_sets(target, &self.kernel_context)
                            .iter()
                            .any(|set| {
                                set.iter().all(|member| {
                                    premise_clauses.iter().any(|premise| {
                                        premise == member
                                            || self
                                                .checker
                                                .canonical_clause_for_trace(
                                                    premise,
                                                    &self.kernel_context,
                                                )
                                                .is_some_and(|canonical_premise| {
                                                    self.checker.canonical_clause_for_trace(
                                                        member,
                                                        &self.kernel_context,
                                                    ) == Some(canonical_premise)
                                                })
                                    })
                                })
                            })
                    })
                };
                if !justified {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace br_intro step {} is not justified by known reductions: {}",
                        index + 1,
                        code
                    )));
                }
                let aliases = if is_synthetic_generic_wrapper(&code) {
                    vec![]
                } else {
                    TraceWriter::claim_aliases(generic, &specialized)
                };
                self.accept_clause_with_aliases(
                    result,
                    aliases,
                    StepReason::BooleanReduction(index),
                    code,
                );
            }
            TraceRule::Eq => {
                let (result, code) = self.parse_required_claim(index, step)?;
                if step.premises.is_empty() {
                    self.checker
                        .check_clause_direct_for_trace(&result, &self.kernel_context)
                        .ok_or_else(|| {
                            CodeGenError::GeneratedBadCode(format!(
                                "certificate trace eq step {} is not justified by current facts: {}",
                                index + 1,
                                code
                            ))
                        })?;
                } else {
                    let mut justified = false;
                    if step.premises.len() == 1 {
                        let source_index = step.premises[0];
                        let sources: Vec<Clause> = self
                            .clauses
                            .get(source_index)
                            .ok_or_else(|| {
                                CodeGenError::GeneratedBadCode(format!(
                                    "certificate trace eq step {} references missing premise {}",
                                    index + 1,
                                    source_index
                                ))
                            })?
                            .all()
                            .cloned()
                            .collect();
                        if sources.iter().any(|source| {
                            self.checker.equality_graph_derives_for_trace(
                                source,
                                &result,
                                &self.kernel_context,
                            )
                        }) {
                            justified = true;
                        }
                    }
                    if !justified {
                        let mut local = Checker::new();
                        local.set_eager_boolean_reductions(false);
                        let mut sources = vec![];
                        let mut ordered_premises = step.premises.clone();
                        ordered_premises.sort_by_key(|premise| {
                            self.clauses
                                .get(*premise)
                                .map(|clauses| clauses.primary.has_any_variable())
                                .unwrap_or(true)
                        });
                        for &premise in &ordered_premises {
                            let clauses = self.clauses.get(premise).ok_or_else(|| {
                                CodeGenError::GeneratedBadCode(format!(
                                    "certificate trace eq step {} references missing premise {}",
                                    index + 1,
                                    premise
                                ))
                            })?;
                            for clause in clauses.all() {
                                sources.push(clause.clone());
                                local.insert_clause_for_trace(
                                    clause,
                                    StepReason::PreviousClaim,
                                    &self.kernel_context,
                                );
                            }
                        }
                        if local
                            .check_clause_direct_for_trace(&result, &self.kernel_context)
                            .is_some()
                        {
                            justified = true;
                        }
                        if !justified
                            && sources.iter().any(|source| {
                                local.equality_graph_derives_for_trace(
                                    source,
                                    &result,
                                    &self.kernel_context,
                                )
                            })
                        {
                            justified = true;
                        }
                    }
                    if !justified {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace eq step {} is not justified by its premises: {}",
                            index + 1,
                            code
                        )));
                    }
                }
                self.accept_clause(result, StepReason::EqualityGraph, code);
            }
            TraceRule::Er | TraceRule::Ef | TraceRule::Ext | TraceRule::Inj => {
                if step.premises.len() != 1 {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace {:?} step {} needs exactly one premise",
                        step.rule,
                        index + 1
                    )));
                }
                let source_index = step.premises[0];
                let sources: Vec<Clause> = self
                    .clauses
                    .get(source_index)
                    .ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace {:?} step {} references missing premise {}",
                            step.rule,
                            index + 1,
                            source_index
                        ))
                    })?
                    .all()
                    .cloned()
                    .collect();
                let (result, code) = self.parse_required_claim(index, step)?;
                let ok = sources.iter().any(|source| match step.rule {
                    TraceRule::Er => self.checker.equality_resolution_derives_for_trace(
                        source,
                        &result,
                        &self.kernel_context,
                    ),
                    TraceRule::Ef => self.checker.equality_factoring_derives_for_trace(
                        source,
                        &result,
                        &self.kernel_context,
                    ),
                    TraceRule::Ext => self.checker.extensionality_derives_for_trace(
                        source,
                        &result,
                        &self.kernel_context,
                    ),
                    TraceRule::Inj => self.checker.injectivity_derives_for_trace(
                        source,
                        &result,
                        &self.kernel_context,
                    ),
                    _ => unreachable!(),
                });
                if !ok {
                    let source_debug = sources
                        .iter()
                        .map(|source| source.to_string())
                        .collect::<Vec<_>>()
                        .join(" | ");
                    let candidate_debug = sources
                        .iter()
                        .flat_map(|source| match step.rule {
                            TraceRule::Er => self.checker.equality_resolution_results_for_trace(
                                source,
                                &self.kernel_context,
                            ),
                            _ => vec![],
                        })
                        .map(|candidate| candidate.to_string())
                        .collect::<Vec<_>>()
                        .join(" | ");
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace {:?} step {} does not derive {} from premise {} (target: {}; candidates: {}; sources: {})",
                        step.rule,
                        index + 1,
                        code,
                        source_index,
                        result,
                        candidate_debug,
                        source_debug
                    )));
                }
                let reason = match step.rule {
                    TraceRule::Er => StepReason::EqualityResolution(source_index),
                    TraceRule::Ef => StepReason::EqualityFactoring(source_index),
                    TraceRule::Ext => StepReason::Extensionality(source_index),
                    TraceRule::Inj => StepReason::Injectivity(source_index),
                    _ => unreachable!(),
                };
                self.accept_clause(result, reason, code);
            }
            TraceRule::Wit => {
                self.check_witness_step(index, step)?;
            }
            TraceRule::Contra => {
                let code = step.claim.clone();
                if step.premises.is_empty() {
                    if !self.checker.has_contradiction() {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} did not close the proof",
                            index + 1
                        )));
                    }
                } else if step.premises.len() == 1 {
                    let source_index = step.premises[0];
                    let source_clauses = self.clauses.get(source_index).ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} references missing premise {}",
                            index + 1,
                            source_index
                        ))
                    })?;
                    let closes = source_clauses.all().any(|source| {
                        self.checker
                            .boolean_reduction_closes_for_trace(source, &self.kernel_context)
                    });
                    if !closes {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} premise does not close by boolean reduction",
                            index + 1
                        )));
                    }
                } else {
                    if step.premises.len() != 2 {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} needs zero, one, or two premises",
                            index + 1
                        )));
                    }
                    let left_index = step.premises[0];
                    let right_index = step.premises[1];
                    let left_clauses = self.clauses.get(left_index).ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} references missing premise {}",
                            index + 1,
                            left_index
                        ))
                    })?;
                    let right_clauses = self.clauses.get(right_index).ok_or_else(|| {
                        CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} references missing premise {}",
                            index + 1,
                            right_index
                        ))
                    })?;
                    let contradicts = left_clauses.all().any(|left| {
                        right_clauses.all().any(|right| {
                            Checker::clauses_contradict_for_trace(left, right, &self.kernel_context)
                        })
                    });
                    if !contradicts {
                        return Err(CodeGenError::GeneratedBadCode(format!(
                            "certificate trace contra step {} premises do not contradict",
                            index + 1
                        )));
                    }
                }
                self.accept_clause(Clause::impossible(), StepReason::Contradiction, code);
            }
        }
        Ok(())
    }

    fn check_witness_step(&mut self, index: usize, step: &TraceStep) -> Result<(), CodeGenError> {
        let code = &step.claim;
        let parsed = Certificate::parse_code_line(
            code,
            self.project,
            &mut self.bindings,
            &mut self.kernel_context,
        )?;
        let CertificateStep::Satisfy(satisfy) = parsed else {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "certificate trace wit step {} must contain a witness declaration: {}",
                index + 1,
                code
            )));
        };
        let generic_clause = satisfy.justification.normalized_generic_clause();
        let justification_clause = satisfy
            .justification
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let justification_ok = self
            .checker
            .check_clause_direct_for_trace(&generic_clause, &self.kernel_context)
            .or_else(|| {
                self.checker
                    .check_clause_direct_for_trace(&justification_clause, &self.kernel_context)
            })
            .is_some();
        if !justification_ok {
            return Err(CodeGenError::GeneratedBadCode(format!(
                "certificate trace wit step {} is missing direct justification: {}",
                index + 1,
                code
            )));
        }

        self.insert_trace_clause(&generic_clause, StepReason::WitnessDeclaration);
        self.insert_trace_clause(&justification_clause, StepReason::WitnessDeclaration);
        if let Some(specialized_clause) = &satisfy.specialized_clause {
            self.insert_trace_clause(specialized_clause, StepReason::WitnessDeclaration);
        }
        for clause in &satisfy.witness_clauses {
            self.insert_trace_clause(clause, StepReason::WitnessDeclaration);
        }
        let mut aliases = vec![generic_clause];
        if let Some(specialized_clause) = satisfy.specialized_clause {
            aliases.push(specialized_clause);
        }
        aliases.extend(satisfy.witness_clauses);
        self.record_clause(
            StepClauses::new(justification_clause, aliases),
            StepReason::WitnessDeclaration,
            code.clone(),
        );
        Ok(())
    }

    fn parse_required_claim(
        &mut self,
        _index: usize,
        step: &TraceStep,
    ) -> Result<(Clause, String), CodeGenError> {
        let code = &step.claim;
        let parsed = Certificate::parse_code_line(
            code,
            self.project,
            &mut self.bindings,
            &mut self.kernel_context,
        )?;
        let clause = match parsed {
            CertificateStep::Claim(claim) => {
                if step.generic {
                    claim.normalized_generic_clause()
                } else {
                    claim
                        .normalized_specialized_clause(&self.kernel_context)
                        .map_err(CodeGenError::GeneratedBadCode)?
                }
            }
            CertificateStep::Satisfy(_) => {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "certificate trace claim position cannot contain witness declaration: {}",
                    code
                )));
            }
        };
        Ok((clause, code.clone()))
    }

    fn parse_required_claim_with_generic(
        &mut self,
        _index: usize,
        step: &TraceStep,
    ) -> Result<(Clause, Clause, String), CodeGenError> {
        let code = &step.claim;
        let parsed = Certificate::parse_code_line(
            code,
            self.project,
            &mut self.bindings,
            &mut self.kernel_context,
        )?;
        match parsed {
            CertificateStep::Claim(claim) => {
                let generic = claim.normalized_generic_clause();
                if step.generic && is_synthetic_generic_wrapper(code) {
                    return Ok((generic.clone(), generic, code.clone()));
                }
                let specialized = claim
                    .normalized_specialized_clause(&self.kernel_context)
                    .map_err(CodeGenError::GeneratedBadCode)?;
                Ok((generic, specialized, code.clone()))
            }
            CertificateStep::Satisfy(_) => Err(CodeGenError::GeneratedBadCode(format!(
                "certificate trace claim position cannot contain witness declaration: {}",
                code
            ))),
        }
    }

    fn accept_clause(&mut self, clause: Clause, reason: StepReason, code: String) {
        self.accept_clause_with_aliases(clause, vec![], reason, code);
    }

    fn insert_trace_clause(&mut self, clause: &Clause, reason: StepReason) {
        self.checker
            .insert_clause_for_trace(clause, reason, &self.kernel_context);
    }

    fn accept_clause_with_aliases(
        &mut self,
        clause: Clause,
        aliases: Vec<Clause>,
        reason: StepReason,
        code: String,
    ) {
        let step_clauses = StepClauses::new(clause, aliases);
        for clause in step_clauses.all() {
            self.insert_trace_clause(clause, StepReason::PreviousClaim);
        }
        self.record_clause(step_clauses, reason, code);
    }

    fn record_clause(&mut self, clauses: StepClauses, reason: StepReason, code: String) {
        if let Some(lines) = &mut self.lines {
            let value = self
                .kernel_context
                .quote_clause(&clauses.primary, None, None, false);
            lines.push(CertificateLine {
                value,
                statement: code,
                reason,
            });
        }
        self.clauses.push(clauses);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certificate::Certificate;
    use crate::processor::Processor;

    #[test]
    fn serialized_certificate_trace_br_step_can_close_simple_goal() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            let p: Bool = axiom
            let q: Bool = axiom
            axiom both {
                p and q
            }

            theorem goal {
                p
            }
            "#,
        );
        let json = r#"{"goal":"goal","p":[{"c":"p and q"},{"r":"br","c":"p","f":[0],"k":"pos_and_left","i":0}]}"#;
        let cert: Certificate =
            serde_json::from_str(json).expect("serialized certificate trace should parse");
        processor
            .check_cert(
                &cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect("serialized certificate trace boolean-reduction proof should check");
    }

    #[test]
    fn serialized_certificate_trace_witness_step_can_close_simple_goal() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            inductive Foo {
                foo
            }
            let p: Foo -> Bool = axiom
            axiom all(x: Foo) {
                p(x)
            }

            theorem goal {
                forall(x: Foo) { p(x) }
            }
            "#,
        );
        let json = r#"{"goal":"goal","p":[{"c":"not forall(x0: Foo) { p(x0) }"},{"r":"br","c":"exists(k0: Foo) { not p(k0) }","f":[0],"k":"neg_forall_exists","i":0},{"r":"wit","c":"let w0: Foo satisfy { not p(w0) }"},{"c":"function(x0: Foo) { p(x0) }(w0)"}]}"#;
        let cert: Certificate =
            serde_json::from_str(json).expect("serialized certificate trace should parse");
        processor
            .check_cert(
                &cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect("serialized certificate trace witness proof should check");
    }

    #[test]
    fn serialized_certificate_trace_er_step_can_close_simple_goal() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            inductive Foo {
                foo
            }
            let p: Bool = axiom
            axiom source(x: Foo) {
                x != x or p
            }

            theorem goal {
                p
            }
            "#,
        );
        let json = r#"{"goal":"goal","p":[{"c":"function(x0: Foo) { x0 != x0 or p }"},{"r":"er","c":"p","f":[0]}]}"#;
        let cert: Certificate =
            serde_json::from_str(json).expect("serialized certificate trace should parse");
        processor
            .check_cert(
                &cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect("serialized certificate trace equality-resolution proof should check");
    }

    #[test]
    fn serialized_certificate_trace_uses_p_for_top_level_proof() {
        let cert = Certificate {
            goal: "goal".to_string(),
            proof: ProofTrace {
                steps: vec![TraceStep::claim("p".to_string())],
            },
        };
        let json = serde_json::to_string(&cert).expect("certificate should serialize");
        assert!(
            json.contains(r#""p":"#),
            "certificate trace certificates should serialize their proof payload as `p`: {}",
            json
        );
        assert!(
            !json.contains(r#""certificate_trace":"#) && !json.contains(r#""proof":"#),
            "certificate trace certificates should not serialize old proof keys: {}",
            json
        );

        serde_json::from_str::<Certificate>(r#"{"goal":"goal","g":[{"c":"p"}]}"#)
            .expect_err("old experimental g key should not deserialize");
    }

    #[test]
    fn certificate_trace_rejects_unknown_rule() {
        let err =
            serde_json::from_str::<Certificate>(r#"{"goal":"goal","p":[{"r":"unknown","c":"p"}]}"#)
                .expect_err("unknown certificate trace rule should not deserialize");
        assert!(
            err.to_string().contains("unknown"),
            "unexpected serde error: {}",
            err
        );
    }

    #[test]
    fn certificate_trace_claim_and_br_helpers_can_close_simple_goal() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            let p: Bool = axiom
            axiom p_true {
                p
            }

            theorem goal {
                p
            }
            "#,
        );
        let cert = Certificate {
            goal: "goal".to_string(),
            proof: ProofTrace {
                steps: vec![TraceStep::claim("p".to_string())],
            },
        };
        processor
            .check_cert(
                &cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect("certificate trace claim proof should check");
    }

    #[test]
    fn certificate_trace_claim_does_not_accept_unproven_serialized_forall() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            inductive Foo {
                foo
            }
            let p: Foo -> Bool = axiom
            axiom p_foo {
                p(Foo.foo)
            }

            theorem goal {
                forall(x: Foo) { p(x) }
            }
            "#,
        );
        let claim_cert: Certificate = serde_json::from_str(
            r#"{"goal":"goal","p":[{"c":"(forall(x0: Foo) { p(x0) } = true)"}]}"#,
        )
        .expect("serialized certificate trace should parse");
        let claim_err = processor
            .check_cert(
                &claim_cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect_err("claim should not hide boolean-reduction introduction");
        assert!(
            claim_err.to_string().contains("is not directly known"),
            "unexpected claim error: {}",
            claim_err
        );
    }

    #[test]
    fn certificate_trace_br_requires_exact_reduction_detail() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            let p: Bool = axiom
            let q: Bool = axiom
            axiom both {
                p and q
            }

            theorem goal {
                p
            }
            "#,
        );
        let cert: Certificate = serde_json::from_str(
            r#"{"goal":"goal","p":[{"c":"p and q"},{"r":"br","c":"p","f":[0]}]}"#,
        )
        .expect("serialized certificate trace should parse");
        let err = processor
            .check_cert(
                &cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect_err("br step should require exact reduction detail");
        assert!(
            err.to_string().contains("missing exact reduction detail"),
            "unexpected br detail error: {}",
            err
        );
    }

    #[test]
    fn certificate_trace_rejects_implicit_boolean_reduction_claim() {
        let (processor, bindings, lowered_goal) = Processor::test_goal(
            r#"
            let p: Bool = axiom
            let q: Bool = axiom
            axiom both {
                p and q
            }

            theorem goal {
                p
            }
            "#,
        );
        let cert: Certificate =
            serde_json::from_str(r#"{"goal":"goal","p":[{"c":"p and q"},{"c":"p"}]}"#)
                .expect("serialized certificate trace should parse");
        let err = processor
            .check_cert(
                &cert,
                Some(&lowered_goal),
                &lowered_goal.kernel_context,
                &crate::project::Project::new_mock(),
                &bindings,
            )
            .expect_err("checker should require an explicit boolean-reduction step");
        assert!(
            err.to_string().contains("is not directly known"),
            "unexpected implicit boolean-reduction error: {}",
            err
        );
    }
}
