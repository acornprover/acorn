use std::sync::Arc;

use tower_lsp::lsp_types::Range;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::block::BlockPremise;
use crate::elaborator::names::ConstantName;
use crate::elaborator::stack::Stack;
use crate::kernel::atom::AtomId;
use crate::syntax::statement::Body;
use crate::syntax::token::Token;

#[derive(Clone, Debug)]
pub struct LocalPremise {
    premise: BlockPremise,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalClaimExport {
    /// Prove the claim for use inside its proof block only.
    InternalOnly,
    /// Also export the claim to the outer environment, guarded by its local premises.
    Guarded,
}

/// A proof obligation claim together with the branch/match premises it may assume.
///
/// Inside the proof block, the premises are added structurally. When exported out of
/// the local context, the same claim becomes `premises -> claim`.
#[derive(Clone, Debug)]
pub struct GuardedLocalClaim {
    claim: AcornValue,
    premises: Vec<LocalPremise>,
}

#[derive(Clone)]
pub struct LocalProofBlock {
    premises: Vec<LocalPremise>,
    obligations: Vec<LocalObligation>,
}

#[derive(Clone, Debug)]
pub(crate) struct LocalStackContext {
    names: Vec<String>,
    types: Vec<AcornType>,
    values: Vec<AcornValue>,
}

impl LocalStackContext {
    pub(crate) fn from_stack(stack: &Stack) -> LocalStackContext {
        let entries = stack.entries();
        let names = entries.iter().map(|(name, _)| name.clone()).collect();
        let types: Vec<_> = entries
            .iter()
            .map(|(_, acorn_type)| acorn_type.clone())
            .collect();
        let values = types
            .iter()
            .enumerate()
            .map(|(i, acorn_type)| AcornValue::Variable(i as AtomId, acorn_type.clone()))
            .collect();
        LocalStackContext {
            names,
            types,
            values,
        }
    }

    pub(crate) fn synthetic_value(
        &self,
        constant_name: ConstantName,
        return_type: AcornType,
    ) -> AcornValue {
        let hidden_type = AcornType::functional(self.types.clone(), return_type);
        let hidden_function = AcornValue::constant(
            constant_name,
            vec![],
            hidden_type.clone(),
            hidden_type.clone(),
            vec![],
            vec![],
        );
        AcornValue::apply(hidden_function, self.values.clone())
    }
}

#[derive(Clone)]
pub enum LocalObligationKind {
    Claim {
        claim: GuardedLocalClaim,
        export: LocalClaimExport,
    },
    ExistsWitness {
        existence: AcornValue,
        witness: GuardedLocalClaim,
    },
    ProofBlock(LocalProofBlock),
}

#[derive(Clone)]
pub struct LocalObligation {
    pub arg_names: Vec<String>,
    pub arg_types: Vec<AcornType>,
    pub synthetic_names: Vec<ConstantName>,
    pub kind: LocalObligationKind,
    pub range: Range,
    pub first_token: Token,
    pub last_token: Token,
    pub body: Option<Arc<Body>>,
}

/// Shared source context for proof obligations created while elaborating local bindings.
///
/// Local `transport`, `let ... satisfy`, and destructuring lets all lower through this
/// site before becoming either claim or witness obligations.
pub(crate) struct LocalProofSite {
    context: LocalStackContext,
    premises: Vec<LocalPremise>,
    range: Range,
    first_token: Token,
    last_token: Token,
    body: Option<Arc<Body>>,
}

impl LocalProofSite {
    pub(crate) fn new(
        context: LocalStackContext,
        premises: Vec<LocalPremise>,
        range: Range,
        first_token: Token,
        last_token: Token,
        body: Option<Arc<Body>>,
    ) -> LocalProofSite {
        LocalProofSite {
            context,
            premises,
            range,
            first_token,
            last_token,
            body,
        }
    }

    pub(crate) fn claim(&self, claim: AcornValue) -> LocalObligation {
        LocalObligation::claim(
            self.context.clone(),
            self.premises.clone(),
            claim,
            self.range.clone(),
            self.first_token.clone(),
            self.last_token.clone(),
            self.body.clone(),
        )
    }

    pub(crate) fn exported_claim(&self, claim: AcornValue) -> LocalObligation {
        LocalObligation::exported_claim(
            self.context.clone(),
            self.premises.clone(),
            claim,
            self.range.clone(),
            self.first_token.clone(),
            self.last_token.clone(),
            self.body.clone(),
        )
    }

    pub(crate) fn witness(
        &self,
        synthetic_names: Vec<ConstantName>,
        existence: AcornValue,
        witness: AcornValue,
    ) -> LocalObligation {
        LocalObligation::witness(
            self.context.clone(),
            synthetic_names,
            self.premises.clone(),
            existence,
            witness,
            self.range.clone(),
            self.first_token.clone(),
            self.last_token.clone(),
            self.body.clone(),
        )
    }

    pub(crate) fn proof_block(&self, obligations: Vec<LocalObligation>) -> LocalObligation {
        LocalObligation::proof_block(
            self.context.clone(),
            self.premises.clone(),
            obligations,
            self.range.clone(),
            self.first_token.clone(),
            self.last_token.clone(),
        )
    }
}

impl LocalObligation {
    fn new(
        context: LocalStackContext,
        synthetic_names: Vec<ConstantName>,
        kind: LocalObligationKind,
        range: Range,
        first_token: Token,
        last_token: Token,
        body: Option<Arc<Body>>,
    ) -> LocalObligation {
        LocalObligation {
            arg_names: context.names,
            arg_types: context.types,
            synthetic_names,
            kind,
            range,
            first_token,
            last_token,
            body,
        }
    }

    fn claim(
        context: LocalStackContext,
        premises: Vec<LocalPremise>,
        claim: AcornValue,
        range: Range,
        first_token: Token,
        last_token: Token,
        body: Option<Arc<Body>>,
    ) -> LocalObligation {
        LocalObligation::new(
            context,
            vec![],
            LocalObligationKind::Claim {
                claim: GuardedLocalClaim::new(premises, claim),
                export: LocalClaimExport::InternalOnly,
            },
            range,
            first_token,
            last_token,
            body,
        )
    }

    fn exported_claim(
        context: LocalStackContext,
        premises: Vec<LocalPremise>,
        claim: AcornValue,
        range: Range,
        first_token: Token,
        last_token: Token,
        body: Option<Arc<Body>>,
    ) -> LocalObligation {
        LocalObligation::new(
            context,
            vec![],
            LocalObligationKind::Claim {
                claim: GuardedLocalClaim::new(premises, claim),
                export: LocalClaimExport::Guarded,
            },
            range,
            first_token,
            last_token,
            body,
        )
    }

    fn witness(
        context: LocalStackContext,
        synthetic_names: Vec<ConstantName>,
        premises: Vec<LocalPremise>,
        existence: AcornValue,
        witness: AcornValue,
        range: Range,
        first_token: Token,
        last_token: Token,
        body: Option<Arc<Body>>,
    ) -> LocalObligation {
        LocalObligation::new(
            context,
            synthetic_names,
            LocalObligationKind::ExistsWitness {
                existence,
                witness: GuardedLocalClaim::new(premises, witness),
            },
            range,
            first_token,
            last_token,
            body,
        )
    }

    fn proof_block(
        context: LocalStackContext,
        premises: Vec<LocalPremise>,
        obligations: Vec<LocalObligation>,
        range: Range,
        first_token: Token,
        last_token: Token,
    ) -> LocalObligation {
        LocalObligation::new(
            context,
            vec![],
            LocalObligationKind::ProofBlock(LocalProofBlock::new(premises, obligations)),
            range,
            first_token,
            last_token,
            None,
        )
    }

    pub(crate) fn requires_result_spec_export(&self) -> bool {
        match &self.kind {
            LocalObligationKind::ExistsWitness { witness, .. } => {
                !self.synthetic_names.is_empty() && witness.has_premises()
            }
            LocalObligationKind::ProofBlock(block) => {
                block.requires_result_spec_export() || block.obligations_need_result_spec_export()
            }
            LocalObligationKind::Claim { .. } => false,
        }
    }

    fn contains_synthetic_witness(&self) -> bool {
        if !self.synthetic_names.is_empty() {
            return true;
        }
        match &self.kind {
            LocalObligationKind::ProofBlock(block) => block.contains_synthetic_witness(),
            _ => false,
        }
    }

    fn exported_value_for_context_len(&self, context_len: usize) -> Option<AcornValue> {
        if self.arg_types.len() != context_len {
            return None;
        }
        match &self.kind {
            LocalObligationKind::Claim {
                claim,
                export: LocalClaimExport::Guarded,
            } => Some(claim.guarded_value()),
            LocalObligationKind::ProofBlock(block) => block
                .external_value(self.arg_types.clone())
                .and_then(|value| {
                    if context_len == 0 {
                        return Some(value);
                    }
                    if let AcornValue::ForAll(_, body) = value {
                        Some(*body)
                    } else {
                        None
                    }
                }),
            _ => None,
        }
    }

    pub(crate) fn genericize(self, type_params: &[TypeParam]) -> LocalObligation {
        LocalObligation {
            arg_names: self.arg_names,
            arg_types: self
                .arg_types
                .into_iter()
                .map(|arg_type| arg_type.genericize(type_params))
                .collect(),
            synthetic_names: self.synthetic_names,
            kind: match self.kind {
                LocalObligationKind::Claim { claim, export } => LocalObligationKind::Claim {
                    claim: claim.genericize(type_params),
                    export,
                },
                LocalObligationKind::ExistsWitness { existence, witness } => {
                    LocalObligationKind::ExistsWitness {
                        existence: existence.genericize(type_params),
                        witness: witness.genericize(type_params),
                    }
                }
                LocalObligationKind::ProofBlock(block) => {
                    LocalObligationKind::ProofBlock(block.genericize(type_params))
                }
            },
            range: self.range,
            first_token: self.first_token,
            last_token: self.last_token,
            body: self.body,
        }
    }
}

impl LocalPremise {
    pub(crate) fn new(value: AcornValue, range: Range) -> LocalPremise {
        LocalPremise {
            premise: BlockPremise::new(value, range),
        }
    }

    fn genericize(self, type_params: &[TypeParam]) -> LocalPremise {
        LocalPremise {
            premise: BlockPremise::new(
                self.premise.value.genericize(type_params),
                self.premise.range,
            ),
        }
    }

    pub(crate) fn value(&self) -> &AcornValue {
        &self.premise.value
    }

    pub(crate) fn to_block_premise(&self) -> BlockPremise {
        self.premise.clone()
    }
}

impl GuardedLocalClaim {
    fn new(premises: Vec<LocalPremise>, claim: AcornValue) -> GuardedLocalClaim {
        GuardedLocalClaim { claim, premises }
    }

    fn has_premises(&self) -> bool {
        !self.premises.is_empty()
    }

    fn genericize(self, type_params: &[TypeParam]) -> GuardedLocalClaim {
        GuardedLocalClaim {
            claim: self.claim.genericize(type_params),
            premises: self
                .premises
                .into_iter()
                .map(|premise| premise.genericize(type_params))
                .collect(),
        }
    }

    fn conjoin_premises(&self) -> AcornValue {
        let mut iter = self.premises.iter().map(|premise| premise.value().clone());
        let Some(first) = iter.next() else {
            return AcornValue::Bool(true);
        };
        iter.fold(first, AcornValue::and)
    }

    fn guarded_value(&self) -> AcornValue {
        if self.premises.is_empty() {
            self.claim.clone()
        } else {
            AcornValue::implies(self.conjoin_premises(), self.claim.clone())
        }
    }

    pub(crate) fn claim(&self) -> &AcornValue {
        &self.claim
    }

    pub(crate) fn block_premises(&self) -> Vec<BlockPremise> {
        self.premises
            .iter()
            .map(LocalPremise::to_block_premise)
            .collect()
    }

    pub(crate) fn external_value(&self, arg_types: Vec<AcornType>) -> AcornValue {
        AcornValue::forall(arg_types, self.guarded_value())
    }
}

impl LocalProofBlock {
    fn new(premises: Vec<LocalPremise>, obligations: Vec<LocalObligation>) -> LocalProofBlock {
        LocalProofBlock {
            premises,
            obligations,
        }
    }

    fn genericize(self, type_params: &[TypeParam]) -> LocalProofBlock {
        LocalProofBlock {
            premises: self
                .premises
                .into_iter()
                .map(|premise| premise.genericize(type_params))
                .collect(),
            obligations: self
                .obligations
                .into_iter()
                .map(|obligation| obligation.genericize(type_params))
                .collect(),
        }
    }

    fn has_premises(&self) -> bool {
        !self.premises.is_empty()
    }

    fn contains_synthetic_witness(&self) -> bool {
        self.obligations
            .iter()
            .any(LocalObligation::contains_synthetic_witness)
    }

    fn requires_result_spec_export(&self) -> bool {
        self.has_premises() && self.contains_synthetic_witness()
    }

    fn obligations_need_result_spec_export(&self) -> bool {
        self.obligations
            .iter()
            .any(LocalObligation::requires_result_spec_export)
    }

    fn conjoin_premises(&self) -> AcornValue {
        let mut iter = self.premises.iter().map(|premise| premise.value().clone());
        let Some(first) = iter.next() else {
            return AcornValue::Bool(true);
        };
        iter.fold(first, AcornValue::and)
    }

    fn conjoin_values(values: Vec<AcornValue>) -> Option<AcornValue> {
        let mut iter = values.into_iter();
        let first = iter.next()?;
        Some(iter.fold(first, AcornValue::and))
    }

    pub(crate) fn obligations(self) -> Vec<LocalObligation> {
        self.obligations
    }

    pub(crate) fn block_premises(&self) -> Vec<BlockPremise> {
        self.premises
            .iter()
            .map(LocalPremise::to_block_premise)
            .collect()
    }

    pub(crate) fn external_value(&self, arg_types: Vec<AcornType>) -> Option<AcornValue> {
        let mut exported_values = vec![];
        for obligation in &self.obligations {
            if let Some(value) = obligation.exported_value_for_context_len(arg_types.len()) {
                exported_values.push(value);
            }
        }
        let conclusion = Self::conjoin_values(exported_values)?;
        let guarded = if self.premises.is_empty() {
            conclusion
        } else {
            AcornValue::implies(self.conjoin_premises(), conclusion)
        };
        Some(AcornValue::forall(arg_types, guarded))
    }
}
