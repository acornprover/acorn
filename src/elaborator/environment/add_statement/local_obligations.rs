use super::transport::TransportBuilder;
use super::*;
use crate::elaborator::evaluator::{LocalObligation, LocalObligationKind, LocalPremise};
use crate::elaborator::fact::SyntheticWitnessFact;
use crate::syntax::statement::Body;

enum PreparedLocalObligation {
    Claim {
        claim: AcornValue,
        premises: Vec<LocalPremise>,
    },
    ExistsWitness {
        existence: AcornValue,
        witness: AcornValue,
        premises: Vec<LocalPremise>,
    },
}

struct LocalObligationFrame {
    arg_count: usize,
    block_args: Vec<(String, AcornType)>,
    range: Range,
    first_token: Token,
    last_token: Token,
    body: Option<Arc<Body>>,
    arg_types: Vec<AcornType>,
}

impl LocalObligationFrame {
    fn from_obligation(obligation: &LocalObligation) -> LocalObligationFrame {
        let block_args = obligation
            .arg_names
            .iter()
            .cloned()
            .zip(obligation.arg_types.iter().cloned())
            .collect();
        LocalObligationFrame {
            arg_count: obligation.arg_types.len(),
            block_args,
            range: obligation.range.clone(),
            first_token: obligation.first_token.clone(),
            last_token: obligation.last_token.clone(),
            body: obligation.body.clone(),
            arg_types: obligation.arg_types.clone(),
        }
    }
}

fn premise_values(premises: &[LocalPremise]) -> Vec<AcornValue> {
    premises
        .iter()
        .map(|premise| premise.value.clone())
        .collect()
}

fn conjoin_values(values: Vec<AcornValue>) -> AcornValue {
    let mut iter = values.into_iter();
    let Some(first) = iter.next() else {
        return AcornValue::Bool(true);
    };
    iter.fold(first, AcornValue::and)
}

fn imply_premises(premises: &[LocalPremise], conclusion: AcornValue) -> AcornValue {
    if premises.is_empty() {
        conclusion
    } else {
        AcornValue::implies(conjoin_values(premise_values(premises)), conclusion)
    }
}

fn prepare_local_obligation(
    env: &Environment,
    project: &dyn ProjectLookup,
    obligation: &LocalObligation,
) -> error::Result<PreparedLocalObligation> {
    match &obligation.kind {
        LocalObligationKind::Claim { claim, premises } => Ok(PreparedLocalObligation::Claim {
            claim: claim.clone(),
            premises: premises.clone(),
        }),
        LocalObligationKind::ExistsWitness {
            existence,
            witness,
            premises,
        } => Ok(PreparedLocalObligation::ExistsWitness {
            existence: existence.clone(),
            witness: witness.clone(),
            premises: premises.clone(),
        }),
        LocalObligationKind::Transport {
            source_type,
            target_type,
            source_value,
            target_value,
            premises,
            transport_token,
        } => {
            let transport = TransportBuilder::new(env, project);
            let stack_size = obligation.arg_types.len() as AtomId;
            let target_variable = AcornValue::Variable(stack_size, target_type.clone());
            let existence_relation = transport.relation(
                source_type,
                target_type,
                source_value.clone(),
                target_variable,
                transport_token,
                stack_size + 1,
            )?;
            let witness_relation = transport.relation(
                source_type,
                target_type,
                source_value.clone(),
                target_value.clone(),
                transport_token,
                stack_size,
            )?;
            Ok(PreparedLocalObligation::ExistsWitness {
                existence: AcornValue::exists(vec![target_type.clone()], existence_relation),
                witness: witness_relation,
                premises: premises.clone(),
            })
        }
    }
}

impl Environment {
    pub(super) fn add_genericized_local_obligations(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        type_params: &[TypeParam],
        local_obligations: Vec<LocalObligation>,
    ) -> error::Result<()> {
        let local_obligations = local_obligations
            .into_iter()
            .map(|obligation| obligation.genericize(type_params))
            .collect();
        self.add_local_obligations(project, statement, type_params, local_obligations)
    }

    pub(super) fn add_local_obligations(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        type_params: &[TypeParam],
        local_obligations: Vec<LocalObligation>,
    ) -> error::Result<()> {
        for obligation in local_obligations {
            let frame = LocalObligationFrame::from_obligation(&obligation);
            let prepared = prepare_local_obligation(self, project, &obligation)?;

            match prepared {
                PreparedLocalObligation::Claim { claim, premises } => {
                    self.add_local_claim_obligation(project, type_params, frame, claim, premises)?;
                }
                PreparedLocalObligation::ExistsWitness {
                    existence,
                    witness,
                    premises,
                } => {
                    self.add_local_witness_obligation(
                        project,
                        statement,
                        type_params,
                        frame,
                        obligation.synthetic_names,
                        existence,
                        witness,
                        premises,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn add_local_claim_obligation(
        &mut self,
        project: &dyn ProjectLookup,
        type_params: &[TypeParam],
        frame: LocalObligationFrame,
        claim: AcornValue,
        premises: Vec<LocalPremise>,
    ) -> error::Result<()> {
        let block = Block::new(
            project,
            self,
            type_params.to_vec(),
            frame.block_args,
            BlockParams::VariableSatisfyWithPremises {
                goal: claim,
                premises: premises
                    .iter()
                    .map(|premise| BlockPremise::new(premise.value.clone(), premise.range))
                    .collect(),
                range: frame.range.clone(),
            },
            &frame.first_token,
            &frame.last_token,
            frame.body.as_deref(),
        )?;
        let index = self.add_node(Node::Block(block, None));
        self.add_node_lines(index, &frame.range);
        Ok(())
    }

    fn add_local_witness_obligation(
        &mut self,
        project: &dyn ProjectLookup,
        _statement: &Statement,
        type_params: &[TypeParam],
        frame: LocalObligationFrame,
        synthetic_names: Vec<ConstantName>,
        existence: AcornValue,
        witness: AcornValue,
        premises: Vec<LocalPremise>,
    ) -> error::Result<()> {
        // Branch premises may justify the relation we expose for the local witness, but not the
        // witness's existence. The existence proof stays unconditional so that a dead branch can't
        // manufacture an inhabitant of an empty type via `exists w { premise -> R(w) }`.
        let block = Block::new(
            project,
            self,
            type_params.to_vec(),
            frame.block_args,
            BlockParams::VariableSatisfy(existence.clone(), frame.range.clone()),
            &frame.first_token,
            &frame.last_token,
            frame.body.as_deref(),
        )?;
        let external_existence = AcornValue::forall(frame.arg_types.clone(), existence);
        let source = Source::anonymous(self.module_id, frame.range.clone(), self.depth);
        let prop = Proposition::new(external_existence, type_params.to_vec(), source)
            .with_arg_count(frame.arg_count);
        let existence_prop = self.bindings.canonicalize_proposition(prop);
        let index = self.add_node(Node::block(
            project,
            self,
            block,
            Some(existence_prop.clone()),
        ));
        self.add_node_lines(index, &frame.range);

        let witness = AcornValue::forall(frame.arg_types, imply_premises(&premises, witness));
        let source = Source::anonymous(self.module_id, frame.range, self.depth);
        let prop =
            Proposition::new(witness, type_params.to_vec(), source).with_arg_count(frame.arg_count);
        let proposition = self.bindings.canonicalize_proposition(prop);
        self.add_node(Node::Structural(Fact::SyntheticWitness(Arc::new(
            SyntheticWitnessFact {
                proposition: Arc::new(proposition),
                existence: existence_prop,
                synthetic_names,
            },
        ))));
        Ok(())
    }
}
