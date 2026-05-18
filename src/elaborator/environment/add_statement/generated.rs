use super::*;
use crate::syntax::statement::Body;

pub(super) enum ExternalFact {
    Proposition(Proposition),
    Fact(Fact),
}

impl From<Proposition> for ExternalFact {
    fn from(prop: Proposition) -> ExternalFact {
        ExternalFact::Proposition(prop)
    }
}

impl From<Fact> for ExternalFact {
    fn from(fact: Fact) -> ExternalFact {
        ExternalFact::Fact(fact)
    }
}

impl ExternalFact {
    fn into_structural_node(self, project: &dyn ProjectLookup, env: &Environment) -> Node {
        match self {
            ExternalFact::Proposition(prop) => Node::structural(project, env, prop),
            ExternalFact::Fact(fact) => Node::Structural(fact),
        }
    }

    fn into_block_node(self, project: &dyn ProjectLookup, env: &Environment, block: Block) -> Node {
        match self {
            ExternalFact::Proposition(prop) => Node::block(project, env, block, Some(prop)),
            ExternalFact::Fact(fact) => Node::Block(block, Some(fact)),
        }
    }
}

impl Environment {
    pub(super) fn requirement_backed_fact_node(
        &self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        type_params: Vec<TypeParam>,
        block_args: Vec<(String, AcornType)>,
        requirements: Vec<AcornValue>,
        requirement_range: Range,
        body: Option<&Body>,
        external_fact: impl Into<ExternalFact>,
    ) -> error::Result<Node> {
        let external_fact = external_fact.into();
        if requirements.is_empty() {
            return Ok(external_fact.into_structural_node(project, self));
        }

        let block = Block::new(
            project,
            self,
            type_params,
            block_args,
            BlockParams::TypeRequirement(requirements, requirement_range),
            &statement.first_token,
            &statement.last_token,
            body,
        )?;
        Ok(external_fact.into_block_node(project, self, block))
    }
}
