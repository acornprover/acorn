use super::*;
use crate::elaborator::evaluator::{
    GuardedLocalClaim, LocalClaimExport, LocalObligation, LocalObligationKind,
};
use crate::elaborator::fact::SyntheticWitnessFact;
use crate::syntax::statement::Body;

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

impl Environment {
    pub(super) fn add_genericized_local_obligations(
        &mut self,
        project: &dyn ProjectLookup,
        type_params: &[TypeParam],
        local_obligations: Vec<LocalObligation>,
    ) -> error::Result<()> {
        let local_obligations = local_obligations
            .into_iter()
            .map(|obligation| obligation.genericize(type_params))
            .collect();
        self.add_local_obligations(project, type_params, local_obligations)
    }

    pub(super) fn add_local_obligations(
        &mut self,
        project: &dyn ProjectLookup,
        type_params: &[TypeParam],
        local_obligations: Vec<LocalObligation>,
    ) -> error::Result<()> {
        for obligation in local_obligations {
            let frame = LocalObligationFrame::from_obligation(&obligation);
            let LocalObligation {
                synthetic_names,
                kind,
                ..
            } = obligation;

            match kind {
                LocalObligationKind::Claim { claim, export } => {
                    self.add_local_claim_obligation(project, type_params, frame, claim, export)?;
                }
                LocalObligationKind::ExistsWitness { existence, witness } => {
                    self.add_local_witness_obligation(
                        project,
                        type_params,
                        frame,
                        synthetic_names,
                        existence,
                        witness,
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
        claim: GuardedLocalClaim,
        export: LocalClaimExport,
    ) -> error::Result<()> {
        let block = Block::new(
            project,
            self,
            type_params.to_vec(),
            frame.block_args,
            BlockParams::variable_satisfy_with_premises(
                claim.claim().clone(),
                claim.block_premises(),
                frame.range.clone(),
            ),
            &frame.first_token,
            &frame.last_token,
            frame.body.as_deref(),
        )?;
        let external_fact = match export {
            LocalClaimExport::InternalOnly => None,
            LocalClaimExport::Guarded => {
                let claim = claim.external_value(frame.arg_types);
                let source = Source::anonymous(self.module_id, frame.range.clone(), self.depth);
                Some(
                    Proposition::new(claim, type_params.to_vec(), source)
                        .with_arg_count(frame.arg_count),
                )
            }
        };
        let index = self.add_node(Node::block(project, self, block, external_fact));
        self.add_node_lines(index, &frame.range);
        Ok(())
    }

    fn add_local_witness_obligation(
        &mut self,
        project: &dyn ProjectLookup,
        type_params: &[TypeParam],
        frame: LocalObligationFrame,
        synthetic_names: Vec<ConstantName>,
        existence: AcornValue,
        witness: GuardedLocalClaim,
    ) -> error::Result<()> {
        // Branch premises may justify the relation we expose for the local witness, but not the
        // witness's existence. The existence proof stays unconditional so that a dead branch can't
        // manufacture an inhabitant of an empty type via `exists w { premise -> R(w) }`.
        let block = Block::new(
            project,
            self,
            type_params.to_vec(),
            frame.block_args,
            BlockParams::variable_satisfy(existence.clone(), frame.range.clone()),
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

        let witness = witness.external_value(frame.arg_types);
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
