use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::certificate::{
    Certificate, CertificateLine, CheckedCertificate, SerializedCertificateStep,
};
use crate::code_generator::Error as CodeGenError;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::certificate_step::{BooleanReductionStep, CertificateStep};
use crate::kernel::checker::{Checker, StepReason};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
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

    #[serde(rename = "c", skip_serializing_if = "Option::is_none")]
    pub claim: Option<String>,

    #[serde(
        rename = "f",
        alias = "from",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub premises: Vec<usize>,

    #[serde(
        rename = "g",
        alias = "generic",
        default,
        skip_serializing_if = "is_false"
    )]
    pub generic: bool,
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
    pub fn fact(claim: String) -> Self {
        Self {
            rule: TraceRule::Fact,
            claim: Some(claim),
            premises: vec![],
            generic: false,
        }
    }

    pub fn claim(claim: String) -> Self {
        Self {
            rule: TraceRule::Claim,
            claim: Some(claim),
            premises: vec![],
            generic: false,
        }
    }

    pub fn br(source: usize, claim: String) -> Self {
        Self {
            rule: TraceRule::Br,
            claim: Some(claim),
            premises: vec![source],
            generic: false,
        }
    }

    fn with_rule(rule: TraceRule, claim: String, premises: Vec<usize>, generic: bool) -> Self {
        Self {
            rule,
            claim: Some(claim),
            premises,
            generic,
        }
    }
}

impl ProofTrace {
    pub(crate) fn from_certificate_steps_checked(
        steps: &[SerializedCertificateStep],
        checker: Checker,
        project: &dyn ProjectLookup,
        bindings: Cow<BindingMap>,
        kernel_context: Cow<KernelContext>,
    ) -> Result<Self, CodeGenError> {
        TraceBuilder::new(checker, project, bindings, kernel_context).compile(steps)
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
                && step
                    .claim
                    .as_deref()
                    .is_some_and(is_serialized_generic_artifact);
            let auxiliary =
                step.generic || matches!(step.rule, TraceRule::Br) || serialized_generic_artifact;
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
        TraceChecker::new(checker, project, bindings, kernel_context).check(self)
    }
}

struct TraceBuilder<'a> {
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
}

impl<'a> TraceBuilder<'a> {
    fn new(
        checker: Checker,
        project: &'a dyn ProjectLookup,
        bindings: Cow<'a, BindingMap>,
        kernel_context: Cow<'a, KernelContext>,
    ) -> Self {
        let mut derivation_checker = checker.clone();
        derivation_checker.set_eager_boolean_reductions(true);
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
        }
    }

    fn compile(mut self, steps: &[SerializedCertificateStep]) -> Result<ProofTrace, CodeGenError> {
        for (line_index, step) in steps.iter().enumerate() {
            if self.derivation_checker.has_contradiction() {
                break;
            }
            self.compile_step(line_index, step)?;
        }
        if !self.derivation_checker.has_contradiction() {
            self.derivation_checker
                .enable_eager_boolean_reductions(&self.kernel_context);
        }
        if !self.derivation_checker.has_contradiction() {
            return Err(CodeGenError::GeneratedBadCode(
                "generated proof steps did not close while compiling certificate trace".to_string(),
            ));
        }
        if !self.shadow_checker.has_contradiction() {
            self.emit_boolean_reduction_contradiction()?;
        }
        Ok(ProofTrace { steps: self.steps })
    }

    fn compile_step(
        &mut self,
        line_index: usize,
        serialized: &SerializedCertificateStep,
    ) -> Result<(), CodeGenError> {
        let code = serialized.code.as_str();
        let parsed = Certificate::parse_code_line(
            code,
            self.project,
            &mut self.bindings,
            &mut self.kernel_context,
        )?;

        let claim_index = match &parsed {
            CertificateStep::Claim(claim) => Some(self.emit_claim_step(code.to_string(), claim)?),
            CertificateStep::BooleanReduction(reduction) => {
                Some(self.emit_boolean_reduction_step(code.to_string(), reduction)?)
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

        let before = self.derivation_checker.inserted_len();
        let code_lines = [code.to_string()];
        match self.derivation_checker.check_cert_steps(
            &[parsed.clone()],
            Some(&code_lines),
            &self.kernel_context,
        ) {
            Ok((_checked, _consumed)) => {}
            Err(err) if err.to_string().contains("proof does not result") => {}
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
                } else {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "proof step {} failed while compiling certificate trace: {} ({})",
                        line_index + 1,
                        code,
                        err
                    )));
                }
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
                }
            }
            Err(err) => {
                return Err(CodeGenError::GeneratedBadCode(format!(
                    "proof step {} failed while compiling certificate trace: {} ({})",
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
                        "missing inserted clause {} while compiling certificate trace",
                        inserted_id
                    ))
                })?;
            let certificate_trace_index =
                match self.emit_clause(inserted.clause, inserted.reason.clone()) {
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
        self.derivation_checker
            .enable_eager_boolean_reductions(&self.kernel_context);
        Ok(())
    }

    fn emit_claim_step(
        &mut self,
        code: String,
        claim: &crate::kernel::certificate_step::Claim,
    ) -> Result<usize, CodeGenError> {
        let generic = claim.normalized_generic_clause();
        let clause = claim
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        if let Some(index) = self.available.get(&clause) {
            return Ok(*index);
        }
        if let Some(index) = self.available.get(&generic) {
            if generic != clause {
                let step_index = self.push_step(
                    TraceRule::Inst,
                    code,
                    vec![*index],
                    clause.clone(),
                    false,
                    vec![],
                )?;
                return Ok(step_index);
            }
            return Ok(*index);
        }

        let reason = self
            .shadow_checker
            .check_clause_direct_for_trace(&clause, &self.kernel_context)
            .or_else(|| {
                self.shadow_checker
                    .check_clause_direct_for_trace(&generic, &self.kernel_context)
            });
        if reason.is_some() {
            return self.push_step(
                TraceRule::Claim,
                code,
                vec![],
                clause.clone(),
                false,
                Self::claim_aliases(generic, &clause),
            );
        }
        if self
            .shadow_checker
            .boolean_reduction_proves_for_trace(&clause, &self.kernel_context)
            || self
                .shadow_checker
                .boolean_reduction_proves_for_trace(&generic, &self.kernel_context)
            || self.boolean_closure_proves_for_trace(&clause)
            || self.boolean_closure_proves_for_trace(&generic)
            || self
                .shadow_checker
                .check_clause(&clause, &self.kernel_context)
                .is_some()
            || self
                .shadow_checker
                .check_clause(&generic, &self.kernel_context)
                .is_some()
        {
            return self.push_step(
                TraceRule::BrIntro,
                code,
                vec![],
                clause.clone(),
                false,
                Self::claim_aliases(generic, &clause),
            );
        }
        for (candidate, candidate_generic) in [(clause.clone(), false), (generic.clone(), true)] {
            for source_index in (0..self.step_clauses.len()).rev() {
                let source_candidates: Vec<Clause> =
                    self.step_clauses[source_index].all().cloned().collect();
                if source_candidates.iter().any(|source| {
                    self.shadow_checker
                        .boolean_reduction_set_contains_for_trace(
                            source,
                            &candidate,
                            &self.kernel_context,
                        )
                }) {
                    return self.push_candidate_step(
                        TraceRule::Br,
                        code,
                        vec![source_index],
                        candidate,
                        candidate_generic,
                        &clause,
                    );
                }
            }
        }
        for (candidate, candidate_generic) in [(clause.clone(), false), (generic.clone(), true)] {
            for inserted_id in (0..self.derivation_checker.inserted_len()).rev() {
                let Some(source_inserted) = self.derivation_checker.inserted_clause(inserted_id)
                else {
                    continue;
                };
                if !self
                    .shadow_checker
                    .boolean_reduction_set_contains_for_trace(
                        &source_inserted.clause,
                        &candidate,
                        &self.kernel_context,
                    )
                {
                    continue;
                }
                let Ok(source_index) =
                    self.emit_clause(source_inserted.clause, source_inserted.reason)
                else {
                    continue;
                };
                return self.push_candidate_step(
                    TraceRule::Br,
                    code,
                    vec![source_index],
                    candidate,
                    candidate_generic,
                    &clause,
                );
            }
        }
        for (candidate, candidate_generic) in [(clause.clone(), false), (generic.clone(), true)] {
            for source_index in (0..self.step_clauses.len()).rev() {
                let premises = vec![source_index];
                if self.equality_closure_derives_from_premises(&premises, &candidate) {
                    return self.push_candidate_step(
                        TraceRule::Eq,
                        code,
                        premises,
                        candidate,
                        candidate_generic,
                        &clause,
                    );
                }
            }
        }
        for (candidate, candidate_generic) in [(clause.clone(), false), (generic.clone(), true)] {
            for inserted_id in (0..self.derivation_checker.inserted_len()).rev() {
                let Some(source_inserted) = self.derivation_checker.inserted_clause(inserted_id)
                else {
                    continue;
                };
                let Ok(source_index) =
                    self.emit_clause(source_inserted.clause, source_inserted.reason)
                else {
                    continue;
                };
                let premises = vec![source_index];
                if !self.equality_closure_derives_from_premises(&premises, &candidate) {
                    continue;
                }
                return self.push_candidate_step(
                    TraceRule::Eq,
                    code,
                    premises,
                    candidate,
                    candidate_generic,
                    &clause,
                );
            }
        }
        Err(CodeGenError::GeneratedBadCode(format!(
            "could not compile claim to certificate trace: {}",
            code
        )))
    }

    fn boolean_closure_proves_for_trace(&self, clause: &Clause) -> bool {
        let mut checker = self.shadow_checker.clone();
        checker.enable_eager_boolean_reductions(&self.kernel_context);
        checker.check_clause(clause, &self.kernel_context).is_some()
    }

    fn emit_boolean_reduction_step(
        &mut self,
        code: String,
        reduction: &BooleanReductionStep,
    ) -> Result<usize, CodeGenError> {
        let source = reduction
            .source
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let result = reduction
            .result
            .normalized_specialized_clause(&self.kernel_context)
            .map_err(CodeGenError::GeneratedBadCode)?;
        let source_index = self
            .emit_clause(source, StepReason::PreviousClaim)
            .map_err(|err| {
                CodeGenError::GeneratedBadCode(format!(
                    "failed to emit source while compiling boolean-reduction step {}: {}",
                    code, err
                ))
            })?;
        self.push_step(
            TraceRule::Br,
            code,
            vec![source_index],
            result,
            false,
            vec![],
        )
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

    fn emit_clause(&mut self, clause: Clause, reason: StepReason) -> Result<usize, CodeGenError> {
        if let Some(index) = self.available.get(&clause) {
            return Ok(*index);
        }
        let (code, generic) = self.serialize_clause_step(&clause)?;

        if let Some(source_id) = reason.dependency() {
            let source_index = if let Some(&source_index) = self.inserted_to_trace.get(&source_id) {
                Some(source_index)
            } else if let Some(source_inserted) = self.derivation_checker.inserted_clause(source_id)
            {
                let source_index = self
                    .emit_clause(source_inserted.clause, source_inserted.reason)
                    .map_err(|err| {
                        CodeGenError::GeneratedBadCode(format!(
                            "failed to emit dependency {} while compiling inserted clause {}: {}",
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
                    StepReason::BooleanReduction(_)
                        if self
                            .shadow_checker
                            .boolean_reduction_set_contains_for_trace(
                                source,
                                &clause,
                                &self.kernel_context,
                            ) =>
                    {
                        Some(TraceRule::Br)
                    }
                    _ => None,
                });
                if let Some(rule) = rule {
                    return self.push_step(rule, code, vec![source_index], clause, generic, vec![]);
                }
            }
        }

        if matches!(reason, StepReason::BooleanReduction(_)) {
            for source_index in (0..self.step_clauses.len()).rev() {
                let source_candidates: Vec<Clause> =
                    self.step_clauses[source_index].all().cloned().collect();
                if source_candidates.iter().any(|source| {
                    self.shadow_checker
                        .boolean_reduction_set_contains_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        )
                }) {
                    return self.push_step(
                        TraceRule::Br,
                        code,
                        vec![source_index],
                        clause,
                        generic,
                        vec![],
                    );
                }
            }
        }

        if !matches!(reason, StepReason::BooleanReduction(_)) {
            for source_index in (0..self.step_clauses.len()).rev() {
                let source_candidates: Vec<Clause> =
                    self.step_clauses[source_index].all().cloned().collect();
                if source_candidates.iter().any(|source| {
                    self.shadow_checker
                        .boolean_reduction_set_contains_for_trace(
                            source,
                            &clause,
                            &self.kernel_context,
                        )
                }) {
                    return self.push_step(
                        TraceRule::Br,
                        code,
                        vec![source_index],
                        clause,
                        generic,
                        vec![],
                    );
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
            if !self
                .shadow_checker
                .boolean_reduction_set_contains_for_trace(
                    &source_inserted.clause,
                    &clause,
                    &self.kernel_context,
                )
            {
                continue;
            }
            let Ok(source_index) = self.emit_clause(source_inserted.clause, source_inserted.reason)
            else {
                continue;
            };
            return self.push_step(
                TraceRule::Br,
                code,
                vec![source_index],
                clause,
                generic,
                vec![],
            );
        }

        if matches!(reason, StepReason::EqualityGraph) {
            for source_index in (0..self.step_clauses.len()).rev() {
                let premises = vec![source_index];
                if self.equality_closure_derives_from_premises(&premises, &clause) {
                    return self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![]);
                }
            }
        }

        if !matches!(reason, StepReason::EqualityGraph) {
            for source_index in (0..self.step_clauses.len()).rev() {
                let premises = vec![source_index];
                if self.equality_closure_derives_from_premises(&premises, &clause) {
                    return self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![]);
                }
            }
        }

        if self
            .shadow_checker
            .boolean_reduction_proves_for_trace(&clause, &self.kernel_context)
        {
            return self.push_step(TraceRule::BrIntro, code, vec![], clause, generic, vec![]);
        }
        if self
            .shadow_checker
            .check_clause_direct_for_trace(&clause, &self.kernel_context)
            .is_some()
        {
            return self.push_step(TraceRule::Claim, code, vec![], clause, generic, vec![]);
        }

        if let Some(index) = self.emit_multi_premise_eq_step(code, clause.clone(), generic)? {
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
        Err(CodeGenError::GeneratedBadCode(format!(
            "could not compile inserted clause to certificate trace: {} ({:?}){}",
            clause, reason, dependency_context
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
        if !self.equality_closure_derives_from_premises(&premises, &clause) {
            return Ok(None);
        }
        self.push_step(TraceRule::Eq, code, premises, clause, generic, vec![])
            .map(Some)
    }

    fn equality_closure_derives_from_premises(&self, premises: &[usize], clause: &Clause) -> bool {
        let mut local = self.base_checker.clone();
        local.set_eager_boolean_reductions(false);
        for &premise in premises {
            let Some(clauses) = self.step_clauses.get(premise) else {
                return false;
            };
            for source in clauses.all() {
                local.insert_clause(source, StepReason::PreviousClaim, &self.kernel_context);
            }
        }
        local.enable_eager_boolean_reductions(&self.kernel_context);
        local.check_clause(clause, &self.kernel_context).is_some()
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
            CertificateStep::BooleanReduction(reduction) => {
                if generic {
                    Ok(reduction.result.normalized_generic_clause())
                } else {
                    reduction
                        .result
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
    ) -> Option<Vec<Clause>> {
        if !seen.insert(source.clone()) {
            return None;
        }
        for reduction_set in self
            .shadow_checker
            .boolean_reduction_sets_for_trace(source, &self.kernel_context)
        {
            for candidate in reduction_set {
                let mut checker = self.shadow_checker.clone();
                checker.insert_clause_for_trace(
                    &candidate,
                    StepReason::PreviousClaim,
                    &self.kernel_context,
                );
                if checker.has_contradiction() {
                    return Some(vec![candidate]);
                }
                if candidate.is_impossible() {
                    return Some(vec![candidate]);
                }
                if let Some(mut path) =
                    self.find_boolean_reduction_contradiction_path(&candidate, seen)
                {
                    path.insert(0, candidate);
                    return Some(path);
                }
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
            for clause in path {
                if let Some(existing_index) = self.available.get(&clause) {
                    premise_index = *existing_index;
                    continue;
                }
                let (code, generic) = if clause.is_impossible() {
                    ("false".to_string(), false)
                } else {
                    self.serialize_clause_step(&clause)?
                };
                premise_index = self.push_step(
                    TraceRule::Br,
                    code,
                    vec![premise_index],
                    clause,
                    generic,
                    vec![],
                )?;
            }
            if self.shadow_checker.has_contradiction() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn emit_boolean_reduction_contradiction(&mut self) -> Result<(), CodeGenError> {
        for source_index in (0..self.step_clauses.len()).rev() {
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
            if !checker.has_contradiction() {
                continue;
            }
            let Ok(step_index) = self.emit_clause(inserted.clause, inserted.reason) else {
                continue;
            };
            if self.shadow_checker.has_contradiction()
                || self.emit_boolean_reduction_contradiction_from_step(step_index)?
            {
                return Ok(());
            }
            if self.shadow_checker.has_contradiction() {
                return Ok(());
            }
        }
        let impossible = Clause::impossible();
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
        let mut closure_checker = self.shadow_checker.clone();
        closure_checker.enable_eager_boolean_reductions(&self.kernel_context);
        if closure_checker.has_contradiction() {
            self.push_contra_step();
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
                match self.emit_clause(inserted.clause, inserted.reason) {
                    Ok(step_index) => {
                        if self.steps.len() > before {
                            progressed = true;
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
            "certificate trace proof closed in derivation checker, but no explicit contradiction path was found{}; emitted steps: {:?}",
            failed_context, self.steps
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
        let index = self.steps.len();
        let step_clauses = StepClauses::new(clause, aliases);
        self.insert_step_clauses(index, &step_clauses);
        self.step_clauses.push(step_clauses);
        self.steps
            .push(TraceStep::with_rule(rule, code, premises, generic));
        Ok(index)
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
        let source_index = self.push_step(
            rule,
            code.clone(),
            premises,
            candidate.clone(),
            candidate_generic,
            vec![],
        )?;
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

    fn push_contra_step(&mut self) -> usize {
        let index = self.steps.len();
        let clause = Clause::impossible();
        let step_clauses = StepClauses::new(clause.clone(), vec![]);
        self.insert_step_clauses(index, &step_clauses);
        self.step_clauses.push(step_clauses);
        self.steps.push(TraceStep {
            rule: TraceRule::Contra,
            claim: None,
            premises: vec![],
            generic: false,
        });
        index
    }
}

struct TraceChecker<'a> {
    base_checker: Checker,
    checker: Checker,
    project: &'a dyn ProjectLookup,
    bindings: Cow<'a, BindingMap>,
    kernel_context: Cow<'a, KernelContext>,
    clauses: Vec<StepClauses>,
    lines: Vec<CertificateLine>,
}

impl<'a> TraceChecker<'a> {
    fn new(
        checker: Checker,
        project: &'a dyn ProjectLookup,
        bindings: Cow<'a, BindingMap>,
        kernel_context: Cow<'a, KernelContext>,
    ) -> Self {
        Self {
            base_checker: checker.clone(),
            checker,
            project,
            bindings,
            kernel_context,
            clauses: vec![],
            lines: vec![],
        }
    }

    fn check(mut self, proof: &ProofTrace) -> Result<CheckedCertificate, CodeGenError> {
        if self.checker.has_contradiction() {
            return Ok(CheckedCertificate {
                lines: self.lines,
                consumed_proof_steps: 0,
            });
        }
        for (index, step) in proof.steps.iter().enumerate() {
            if self.checker.has_contradiction() {
                return Ok(CheckedCertificate {
                    lines: self.lines,
                    consumed_proof_steps: index,
                });
            }
            self.check_step(index, step)?;
        }
        if !self.checker.has_contradiction() {
            return Err(CodeGenError::GeneratedBadCode(
                "certificate trace proof does not result in a contradiction".to_string(),
            ));
        }
        let consumed = proof.steps.len();
        Ok(CheckedCertificate {
            lines: self.lines,
            consumed_proof_steps: consumed,
        })
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
                    TraceBuilder::claim_aliases(generic.clone(), &specialized)
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
                    .or_else(|| {
                        #[cfg(not(feature = "strict-br"))]
                        {
                            self.checker
                                .boolean_reduction_proves_for_trace(&generic, &self.kernel_context)
                                .then_some(StepReason::BooleanReduction(index))
                        }
                        #[cfg(feature = "strict-br")]
                        {
                            None
                        }
                    })
                    .or_else(|| {
                        #[cfg(not(feature = "strict-br"))]
                        {
                            self.checker
                                .boolean_reduction_proves_for_trace(&clause, &self.kernel_context)
                                .then_some(StepReason::BooleanReduction(index))
                        }
                        #[cfg(feature = "strict-br")]
                        {
                            None
                        }
                    })
                    .or_else(|| {
                        #[cfg(not(feature = "strict-br"))]
                        {
                            self.checker
                                .boolean_reduction_proves_for_trace(
                                    &specialized,
                                    &self.kernel_context,
                                )
                                .then_some(StepReason::BooleanReduction(index))
                        }
                        #[cfg(feature = "strict-br")]
                        {
                            None
                        }
                    })
                    .or_else(|| {
                        is_serialized_generic_artifact(&code).then_some(StepReason::PreviousClaim)
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
                if !sources.iter().any(|source| *source == generic) {
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
                let (result, code) = self.parse_required_claim(index, step)?;
                let mut reduced = false;
                for source in &sources {
                    for candidate in self
                        .checker
                        .boolean_reduction_sets_for_trace(source, &self.kernel_context)
                        .into_iter()
                        .flatten()
                    {
                        if candidate == result {
                            reduced = true;
                            break;
                        }
                        let mut local = self.checker.clone();
                        local.insert_clause_for_trace(
                            &candidate,
                            StepReason::BooleanReduction(source_index),
                            &self.kernel_context,
                        );
                        if local.equality_graph_derives_for_trace(
                            &candidate,
                            &result,
                            &self.kernel_context,
                        ) {
                            reduced = true;
                            break;
                        }
                    }
                    if reduced {
                        break;
                    }
                }
                if !reduced {
                    let source_debug = sources
                        .iter()
                        .map(|source| source.to_string())
                        .collect::<Vec<_>>()
                        .join(" | ");
                    let candidate_debug = sources
                        .iter()
                        .flat_map(|source| {
                            self.checker
                                .boolean_reduction_sets_for_trace(source, &self.kernel_context)
                                .into_iter()
                                .flatten()
                        })
                        .map(|candidate| candidate.to_string())
                        .collect::<Vec<_>>()
                        .join(" | ");
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace br step {} does not reduce premise {} to {} (target: {}; candidates: {}; sources: {})",
                        index + 1,
                        source_index,
                        code,
                        result,
                        candidate_debug,
                        source_debug
                    )));
                }
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
                let mut closure_checker = self.checker.clone();
                closure_checker.enable_eager_boolean_reductions(&self.kernel_context);
                if !self
                    .checker
                    .boolean_reduction_proves_for_trace(&generic, &self.kernel_context)
                    && !self
                        .checker
                        .boolean_reduction_proves_for_trace(&result, &self.kernel_context)
                    && !self
                        .checker
                        .boolean_reduction_proves_for_trace(&specialized, &self.kernel_context)
                    && closure_checker
                        .check_clause(&generic, &self.kernel_context)
                        .or_else(|| closure_checker.check_clause(&result, &self.kernel_context))
                        .or_else(|| {
                            closure_checker.check_clause(&specialized, &self.kernel_context)
                        })
                        .is_none()
                    && self
                        .checker
                        .check_clause(&generic, &self.kernel_context)
                        .or_else(|| self.checker.check_clause(&result, &self.kernel_context))
                        .or_else(|| {
                            self.checker
                                .check_clause(&specialized, &self.kernel_context)
                        })
                        .is_none()
                    && self
                        .checker
                        .check_clause_direct_for_trace(&generic, &self.kernel_context)
                        .or_else(|| {
                            self.checker
                                .check_clause_direct_for_trace(&result, &self.kernel_context)
                        })
                        .or_else(|| {
                            self.checker
                                .check_clause_direct_for_trace(&specialized, &self.kernel_context)
                        })
                        .is_none()
                {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace br_intro step {} is not justified by known reductions: {}",
                        index + 1,
                        code
                    )));
                }
                let aliases = if is_synthetic_generic_wrapper(&code) {
                    vec![]
                } else {
                    TraceBuilder::claim_aliases(generic, &specialized)
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
                    #[cfg(not(feature = "strict-br"))]
                    {
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
                            for &premise in &step.premises {
                                let clauses = self.clauses.get(premise).ok_or_else(|| {
                                    CodeGenError::GeneratedBadCode(format!(
                                        "certificate trace eq step {} references missing premise {}",
                                        index + 1,
                                        premise
                                    ))
                                })?;
                                for clause in clauses.all() {
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
                        }
                        if !justified {
                            let mut local = self.base_checker.clone();
                            local.set_eager_boolean_reductions(false);
                            for &premise in &step.premises {
                                let clauses = self.clauses.get(premise).ok_or_else(|| {
                                    CodeGenError::GeneratedBadCode(format!(
                                        "certificate trace eq step {} references missing premise {}",
                                        index + 1,
                                        premise
                                    ))
                                })?;
                                for clause in clauses.all() {
                                    local.insert_clause(
                                        clause,
                                        StepReason::PreviousClaim,
                                        &self.kernel_context,
                                    );
                                }
                            }
                            local.enable_eager_boolean_reductions(&self.kernel_context);
                            if local.check_clause(&result, &self.kernel_context).is_some() {
                                justified = true;
                            }
                        }
                        if !justified
                            && self
                                .checker
                                .check_clause(&result, &self.kernel_context)
                                .is_some()
                        {
                            justified = true;
                        }
                        if !justified {
                            return Err(CodeGenError::GeneratedBadCode(format!(
                                "certificate trace eq step {} is not justified by its premises: {}",
                                index + 1,
                                code
                            )));
                        }
                    }

                    #[cfg(feature = "strict-br")]
                    {
                        let mut local = self.base_checker.clone();
                        local.set_eager_boolean_reductions(false);
                        for &premise in &step.premises {
                            let clauses = self.clauses.get(premise).ok_or_else(|| {
                                CodeGenError::GeneratedBadCode(format!(
                                    "certificate trace eq step {} references missing premise {}",
                                    index + 1,
                                    premise
                                ))
                            })?;
                            for clause in clauses.all() {
                                local.insert_clause(
                                    clause,
                                    StepReason::PreviousClaim,
                                    &self.kernel_context,
                                );
                            }
                        }
                        local.enable_eager_boolean_reductions(&self.kernel_context);
                        local
                            .check_clause(&result, &self.kernel_context)
                            .ok_or_else(|| {
                                CodeGenError::GeneratedBadCode(format!(
                                "certificate trace eq step {} is not justified by its premises: {}",
                                index + 1,
                                code
                            ))
                            })?;
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
                let code = step.claim.clone().unwrap_or_else(|| "false".to_string());
                let mut closure_checker = self.checker.clone();
                closure_checker.enable_eager_boolean_reductions(&self.kernel_context);
                if !closure_checker.has_contradiction() {
                    return Err(CodeGenError::GeneratedBadCode(format!(
                        "certificate trace contra step {} did not close the proof",
                        index + 1
                    )));
                }
                self.accept_clause(Clause::impossible(), StepReason::Contradiction, code);
            }
        }
        Ok(())
    }

    fn check_witness_step(&mut self, index: usize, step: &TraceStep) -> Result<(), CodeGenError> {
        let code = step.claim.as_ref().ok_or_else(|| {
            CodeGenError::GeneratedBadCode(format!(
                "certificate trace wit step {} is missing declaration text",
                index + 1
            ))
        })?;
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

        self.checker.insert_clause_for_trace(
            &generic_clause,
            StepReason::WitnessDeclaration,
            &self.kernel_context,
        );
        self.checker.insert_clause_for_trace(
            &justification_clause,
            StepReason::WitnessDeclaration,
            &self.kernel_context,
        );
        if let Some(specialized_clause) = &satisfy.specialized_clause {
            self.checker.insert_clause_for_trace(
                specialized_clause,
                StepReason::WitnessDeclaration,
                &self.kernel_context,
            );
        }
        for clause in &satisfy.witness_clauses {
            self.checker.insert_clause_for_trace(
                clause,
                StepReason::WitnessDeclaration,
                &self.kernel_context,
            );
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
        index: usize,
        step: &TraceStep,
    ) -> Result<(Clause, String), CodeGenError> {
        let code = step.claim.as_ref().ok_or_else(|| {
            CodeGenError::GeneratedBadCode(format!(
                "certificate trace step {} is missing claim text",
                index + 1
            ))
        })?;
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
            CertificateStep::BooleanReduction(BooleanReductionStep { result, .. }) => {
                if step.generic {
                    result.normalized_generic_clause()
                } else {
                    result
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
        index: usize,
        step: &TraceStep,
    ) -> Result<(Clause, Clause, String), CodeGenError> {
        let code = step.claim.as_ref().ok_or_else(|| {
            CodeGenError::GeneratedBadCode(format!(
                "certificate trace step {} is missing claim text",
                index + 1
            ))
        })?;
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
            CertificateStep::BooleanReduction(BooleanReductionStep { result, .. }) => {
                let generic = result.normalized_generic_clause();
                if step.generic && is_synthetic_generic_wrapper(code) {
                    return Ok((generic.clone(), generic, code.clone()));
                }
                let specialized = result
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

    fn accept_clause_with_aliases(
        &mut self,
        clause: Clause,
        aliases: Vec<Clause>,
        reason: StepReason,
        code: String,
    ) {
        let step_clauses = StepClauses::new(clause, aliases);
        for clause in step_clauses.all() {
            self.checker.insert_clause_for_trace(
                clause,
                StepReason::PreviousClaim,
                &self.kernel_context,
            );
        }
        self.record_clause(step_clauses, reason, code);
    }

    fn record_clause(&mut self, clauses: StepClauses, reason: StepReason, code: String) {
        let value = self
            .kernel_context
            .quote_clause(&clauses.primary, None, None, false);
        self.clauses.push(clauses);
        self.lines.push(CertificateLine {
            value,
            statement: code,
            reason,
        });
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
        let json = r#"{"goal":"goal","p":[{"c":"p and q"},{"r":"br","c":"p","f":[0]}]}"#;
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
        let json = r#"{"goal":"goal","p":[{"r":"br_intro","c":"exists(k0: Foo) { not p(k0) }"},{"r":"wit","c":"let w0: Foo satisfy { not p(w0) }"},{"c":"function(x0: Foo) { p(x0) }(w0)"}]}"#;
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
            proof: Some(ProofTrace {
                steps: vec![TraceStep::claim("p".to_string())],
            }),
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
            proof: Some(ProofTrace {
                steps: vec![TraceStep::claim("p".to_string())],
            }),
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

    #[cfg(feature = "strict-br")]
    #[test]
    fn strict_br_rejects_implicit_boolean_reduction_claim() {
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
            .expect_err("strict-br should require an explicit boolean-reduction step");
        assert!(
            err.to_string().contains("is not directly known"),
            "unexpected strict-br error: {}",
            err
        );
    }
}
