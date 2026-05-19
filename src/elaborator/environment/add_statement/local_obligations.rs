use super::transport::TransportBuilder;
use super::*;
use crate::elaborator::evaluator::{LocalObligation, LocalObligationKind};
use crate::syntax::statement::Body;

enum PreparedLocalObligation {
    ExistsWitness {
        existence: AcornValue,
        witness: AcornValue,
        premises: Vec<AcornValue>,
    },
    RequirementBackedFact {
        requirements: Vec<AcornValue>,
        fact: AcornValue,
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

fn conjoin_values(values: Vec<AcornValue>) -> AcornValue {
    let mut iter = values.into_iter();
    let Some(first) = iter.next() else {
        return AcornValue::Bool(true);
    };
    iter.fold(first, AcornValue::and)
}

fn imply_premises(premises: Vec<AcornValue>, conclusion: AcornValue) -> AcornValue {
    if premises.is_empty() {
        conclusion
    } else {
        AcornValue::implies(conjoin_values(premises), conclusion)
    }
}

fn prepare_local_obligation(
    env: &Environment,
    project: &dyn ProjectLookup,
    obligation: &LocalObligation,
) -> error::Result<PreparedLocalObligation> {
    match &obligation.kind {
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
            let relation = transport.relation(
                source_type,
                target_type,
                source_value.clone(),
                target_value.clone(),
                transport_token,
                obligation.arg_types.len() as AtomId,
            )?;
            let requirements = transport
                .requirements(source_type, target_type, transport_token)?
                .into_iter()
                .map(|requirement| imply_premises(premises.clone(), requirement))
                .collect();
            Ok(PreparedLocalObligation::RequirementBackedFact {
                requirements,
                fact: imply_premises(premises.clone(), relation),
            })
        }
    }
}

impl Environment {
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
            self.declare_local_hidden_constants(
                statement,
                type_params,
                &obligation.hidden_constants,
            )?;

            match prepared {
                PreparedLocalObligation::ExistsWitness {
                    existence,
                    witness,
                    premises,
                } => {
                    self.add_local_witness_obligation(
                        project,
                        type_params,
                        frame,
                        existence,
                        witness,
                        premises,
                    )?;
                }
                PreparedLocalObligation::RequirementBackedFact { requirements, fact } => {
                    self.add_local_requirement_obligation(
                        project,
                        type_params,
                        frame,
                        requirements,
                        fact,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn declare_local_hidden_constants(
        &mut self,
        statement: &Statement,
        type_params: &[TypeParam],
        hidden_constants: &[(String, AcornType)],
    ) -> error::Result<()> {
        for (name, hidden_type) in hidden_constants {
            let defined_name = DefinedName::unqualified(self.module_id, name);
            if self.bindings.constant_name_in_use(&defined_name) {
                return Err(statement.error(&format!(
                    "generated local destructuring name '{}' is already in use",
                    name
                )));
            }
            self.bindings.add_unqualified_constant(
                name,
                type_params.to_vec(),
                vec![],
                hidden_type.clone(),
                None,
                None,
                vec![],
                None,
                format!("{}: {}", name, hidden_type),
            );
        }
        Ok(())
    }

    fn add_local_witness_obligation(
        &mut self,
        project: &dyn ProjectLookup,
        type_params: &[TypeParam],
        frame: LocalObligationFrame,
        existence: AcornValue,
        witness: AcornValue,
        premises: Vec<AcornValue>,
    ) -> error::Result<()> {
        let existence_goal = imply_premises(premises.clone(), existence.clone());
        let block = Block::new(
            project,
            self,
            type_params.to_vec(),
            frame.block_args,
            BlockParams::VariableSatisfy(existence_goal, frame.range.clone()),
            &frame.first_token,
            &frame.last_token,
            frame.body.as_deref(),
        )?;
        let external_existence = AcornValue::forall(
            frame.arg_types.clone(),
            imply_premises(premises.clone(), existence),
        );
        let source = Source::anonymous(self.module_id, frame.range.clone(), self.depth);
        let prop = Proposition::new(external_existence, type_params.to_vec(), source)
            .with_arg_count(frame.arg_count);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &frame.range);

        let witness = AcornValue::forall(frame.arg_types, imply_premises(premises, witness));
        let source = Source::anonymous(self.module_id, frame.range, self.depth);
        let prop =
            Proposition::new(witness, type_params.to_vec(), source).with_arg_count(frame.arg_count);
        self.add_node(Node::structural(project, self, prop));
        Ok(())
    }

    fn add_local_requirement_obligation(
        &mut self,
        project: &dyn ProjectLookup,
        type_params: &[TypeParam],
        frame: LocalObligationFrame,
        requirements: Vec<AcornValue>,
        fact: AcornValue,
    ) -> error::Result<()> {
        let external_fact = AcornValue::forall(frame.arg_types, fact);
        let source = Source::anonymous(self.module_id, frame.range.clone(), self.depth);
        let prop = Proposition::new(external_fact, type_params.to_vec(), source)
            .with_arg_count(frame.arg_count);
        let node = if requirements.is_empty() && frame.body.is_none() {
            Node::structural(project, self, prop)
        } else {
            let block = Block::new(
                project,
                self,
                type_params.to_vec(),
                frame.block_args,
                BlockParams::TypeRequirement(requirements, frame.range.clone()),
                &frame.first_token,
                &frame.last_token,
                frame.body.as_deref(),
            )?;
            Node::block(project, self, block, Some(prop))
        };
        let index = self.add_node(node);
        self.add_node_lines(index, &frame.range);
        Ok(())
    }
}
