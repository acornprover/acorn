use std::fmt;
use std::sync::Arc;

use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::block::Block;
use crate::elaborator::environment::Environment;
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::normalizer::{NormalizedFact, NormalizedGoal};
use crate::project::Project;

/// Environments are structured into a tree of nodes. Environment nodes have access to everything
/// in their parent environment, plus whatever facts are before them in the same environment.
/// Different nodes need to be checked for different properties. Block nodes, for example,
/// have blocks, with their own environments.
/// There are three types of nodes.
/// 1. Structural nodes, that we can assume without proof
/// 2. Plain claims, that we need to prove
/// 3. Nodes with blocks, where we need to recurse into the block and prove those nodes.
pub enum Node {
    /// Some nodes contain propositions that are structurally true.
    /// The prover doesn't need to prove these.
    /// For example, this could be an axiom, or a definition.
    /// It could also be a form like a citation that has already been proven by the prover.
    /// The optional NormalizedFact is populated during prenormalize().
    Structural(Fact, Option<NormalizedFact>),

    /// A claim is something that we need to prove, and then we can subsequently use it.
    /// The Goal represents what needs to be proven; the Fact represents what can be used once proven.
    /// The optional NormalizedGoal is the pre-normalized goal with captured normalizer state.
    /// The optional NormalizedFact is the pre-normalized fact.
    /// Both are populated during prenormalize().
    Claim(Goal, Fact, Option<NormalizedGoal>, Option<NormalizedFact>),

    /// A block has its own environment inside. We need to validate everything in the block.
    /// The block might not exist in the code, but it at least needs to exist for the prover.
    /// The optional fact is what we can use externally once the block is proven.
    /// It is relative to the outside environment.
    /// Other than the external claim, nothing else in the block is visible outside the block.
    /// The optional NormalizedFact is the pre-normalized external fact, populated during prenormalize().
    Block(Block, Option<Fact>, Option<NormalizedFact>),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Node::Structural(fact, _) => write!(f, "structural: {}", fact),
            Node::Claim(goal, _, _, _) => write!(f, "claim: {}", goal),
            Node::Block(_, Some(fact), _) => write!(f, "block: {}", fact),
            Node::Block(_, None, _) => write!(f, "block: None"),
        }
    }
}

impl Node {
    pub fn structural(project: &Project, env: &Environment, prop: Proposition) -> Node {
        let prop = env.bindings.expand_theorems(prop, project);
        Node::Structural(Fact::Proposition(Arc::new(prop)), None)
    }

    pub fn claim(project: &Project, env: &Environment, prop: Proposition) -> Result<Node, String> {
        let prop = env.bindings.expand_theorems(prop, project);
        let prop = Arc::new(prop);
        let goal = Goal::interior(env, prop.clone())?;
        let fact = Fact::Proposition(prop);
        Ok(Node::Claim(goal, fact, None, None))
    }

    /// This does not expand theorems. I can imagine this coming up, but it would be weird.
    pub fn definition(constant: PotentialValue, definition: AcornValue, source: Source) -> Node {
        let fact = Fact::Definition(constant, definition, source);
        Node::Structural(fact, None)
    }

    /// The optional proposition is the claim that we can use externally once the block is proven.
    /// It is relative to the outside environment.
    pub fn block(
        project: &Project,
        env: &Environment,
        block: Block,
        prop: Option<Proposition>,
    ) -> Node {
        let fact = match prop {
            Some(prop) => Some(Fact::Proposition(Arc::new(
                env.bindings.expand_theorems(prop, project),
            ))),
            None => None,
        };
        Node::Block(block, fact, None)
    }

    pub fn instance(block: Option<Block>, fact: Fact) -> Node {
        match block {
            Some(b) => Node::Block(b, Some(fact), None),
            None => Node::Structural(fact, None),
        }
    }

    /// Whether this node corresponds to a goal that needs to be proved.
    /// Block nodes no longer have goals directly - their goals are child nodes.
    pub fn has_goal(&self) -> bool {
        match self {
            Node::Structural(_, _) => false,
            Node::Claim(_, _, _, _) => true,
            Node::Block(_, _, _) => false,
        }
    }

    /// Whether this node is a block-level goal (as opposed to an internal claim in a proof).
    /// Block-level goals include theorem goals and constraint block goals.
    pub fn is_block_level_goal(&self) -> bool {
        if let Some(prop) = self.proposition() {
            matches!(
                prop.source.source_type,
                crate::elaborator::source::SourceType::BlockGoal
                    | crate::elaborator::source::SourceType::Theorem(_)
            )
        } else {
            false
        }
    }

    pub fn first_line(&self) -> u32 {
        match self {
            Node::Structural(f, _) => f.source().range.start.line,
            Node::Claim(g, _, _, _) => g.proposition.source.range.start.line,
            Node::Block(block, _, _) => block.env.first_line,
        }
    }

    pub fn last_line(&self) -> u32 {
        match self {
            Node::Structural(f, _) => f.source().range.end.line,
            Node::Claim(g, _, _, _) => g.proposition.source.range.end.line,
            Node::Block(block, _, _) => block.env.last_line(),
        }
    }

    pub fn get_block(&self) -> Option<&Block> {
        match self {
            Node::Block(block, _, _) => Some(block),
            _ => None,
        }
    }

    /// The source of this node, if there is one.
    pub fn source(&self) -> Option<&Source> {
        match self {
            Node::Structural(f, _) => Some(f.source()),
            Node::Claim(g, _, _, _) => Some(&g.proposition.source),
            Node::Block(_, Some(f), _) => Some(f.source()),
            Node::Block(_, None, _) => None,
        }
    }

    /// The proposition at this node, if there is one.
    pub fn proposition(&self) -> Option<&Proposition> {
        match self {
            Node::Structural(Fact::Proposition(p), _) => Some(p.as_ref()),
            Node::Claim(g, _, _, _) => Some(g.proposition.as_ref()),
            Node::Block(_, Some(Fact::Proposition(p)), _) => Some(p.as_ref()),
            _ => None,
        }
    }

    /// Whether the fact at this node is importable.
    pub fn importable(&self) -> bool {
        self.source().map_or(false, |s| s.importable)
    }

    /// Returns the fact at this node, if there is one.
    pub fn get_fact(&self) -> Option<Fact> {
        match self {
            Node::Structural(f, _) => Some(f.clone()),
            Node::Claim(_, f, _, _) => Some(f.clone()),
            Node::Block(_, Some(f), _) => Some(f.clone()),
            _ => None,
        }
    }

    /// Returns the pre-normalized fact at this node, if there is one.
    pub fn get_normalized_fact(&self) -> Option<&NormalizedFact> {
        match self {
            Node::Structural(_, Some(nf)) => Some(nf),
            Node::Claim(_, _, _, Some(nf)) => Some(nf),
            Node::Block(_, _, Some(nf)) => Some(nf),
            _ => None,
        }
    }

    /// The source name is used to describe the premise when caching block -> premise dependencies.
    /// All importable facts should have a source name.
    pub fn source_name(&self) -> Option<String> {
        self.source()?.name()
    }

    /// Returns the name and value, if this node is a theorem.
    pub fn as_theorem(&self) -> Option<(&str, &AcornValue)> {
        let prop = self.proposition()?;
        if let Some(theorem_name) = prop.theorem_name() {
            Some((theorem_name, &prop.value))
        } else {
            None
        }
    }

    pub fn is_axiom(&self) -> bool {
        self.source().map_or(false, |s| s.is_axiom())
    }
}

/// A NodeCursor points at a node. It is used to traverse the nodes in an environment.
#[derive(Clone)]
pub struct NodeCursor<'a> {
    /// All the environments that surround this node.
    /// (env, index) pairs tell you that the node env.nodes[index] to get to
    /// the next environment.
    annotated_path: Vec<(&'a Environment, usize)>,
}

impl fmt::Display for NodeCursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.path())
    }
}

impl fmt::Debug for NodeCursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NodeCursor(path: {:?}", self.path())?;

        // Add information about the node
        let node = self.node();
        if node.has_goal() {
            write!(f, ", has_goal: true")?;
            match node {
                Node::Claim(goal, _, _, _) => write!(f, ", claim: {}", goal)?,
                _ => {}
            }
        }

        write!(f, ")")
    }
}

impl<'a> NodeCursor<'a> {
    pub fn from_path(env: &'a Environment, path: &[usize]) -> Self {
        assert!(!path.is_empty());
        let mut iter = NodeCursor::new(env, path[0]);
        for &i in &path[1..] {
            iter.descend(i);
        }
        iter
    }

    /// Only call this on a module level environment.
    /// Returns None if there are no nodes in the environment.
    pub fn new(env: &'a Environment, index: usize) -> Self {
        assert_eq!(env.depth, 0);
        assert!(env.nodes.len() > index);
        NodeCursor {
            annotated_path: vec![(env, index)],
        }
    }

    /// The environment that contains the current node.
    pub fn env(&self) -> &'a Environment {
        self.annotated_path.last().unwrap().0
    }

    pub fn node(&self) -> &'a Node {
        let (env, index) = self.annotated_path.last().unwrap();
        &env.nodes[*index]
    }

    /// Can use this as an identifier for the iterator, to compare two of them
    pub fn path(&self) -> Vec<usize> {
        self.annotated_path.iter().map(|(_, i)| *i).collect()
    }

    pub fn num_children(&self) -> usize {
        match self.node().get_block() {
            Some(ref b) => b.env.nodes.len(),
            None => 0,
        }
    }

    /// A node requires verification if it has a goal itself, or if it might have a goal
    /// in its children.
    pub fn requires_verification(&self) -> bool {
        self.node().has_goal() || self.num_children() > 0
    }

    /// child_index must be less than num_children
    pub fn descend(&mut self, child_index: usize) {
        let new_env = match &self.node().get_block() {
            Some(b) => &b.env,
            None => panic!("descend called on a node without a block"),
        };
        assert!(child_index < new_env.nodes.len());
        self.annotated_path.push((new_env, child_index));
    }

    /// Whether we can advance to the next sibling, keeping environment the same.
    pub fn has_next(&self) -> bool {
        let (env, index) = self.annotated_path.last().unwrap();
        index + 1 < env.nodes.len()
    }

    /// Advances to the next sibling, keeping environment the same.
    pub fn next(&mut self) {
        let (env, index) = self.annotated_path.last_mut().unwrap();
        assert!(*index + 1 < env.nodes.len());
        *index += 1;
    }

    pub fn can_ascend(&self) -> bool {
        self.annotated_path.len() > 1
    }

    pub fn ascend(&mut self) {
        assert!(self.can_ascend());
        self.annotated_path.pop();
    }

    /// Facts from this module that can be used to prove the current node.
    /// This does not include imported facts.
    pub fn module_facts(&self) -> Vec<Fact> {
        let mut facts = vec![];
        let (env, i) = &self.annotated_path[0];
        for node in &env.nodes[0..*i] {
            if let Some(fact) = node.get_fact() {
                facts.push(fact);
            }
        }

        facts.extend(self.block_facts());
        facts
    }

    /// Pre-normalized facts from this module that are visible at the current node.
    /// This does not include imported facts.
    pub fn visible_normalized_facts(&self) -> Result<Vec<&NormalizedFact>, String> {
        let mut facts = vec![];
        let (env, i) = &self.annotated_path[0];
        for node in &env.nodes[0..*i] {
            if node.get_fact().is_some() {
                match node.get_normalized_fact() {
                    Some(nf) => facts.push(nf),
                    None => {
                        return Err(format!("missing prenormalized fact for node {}", node));
                    }
                }
            }
        }

        for (env, i) in self.annotated_path.iter().skip(1) {
            for node in &env.nodes[0..*i] {
                if node.get_fact().is_some() {
                    match node.get_normalized_fact() {
                        Some(nf) => facts.push(nf),
                        None => {
                            return Err(format!("missing prenormalized fact for node {}", node));
                        }
                    }
                }
            }
        }

        if let Some(block) = &self.node().get_block() {
            for node in &block.env.nodes {
                if node.get_fact().is_some() {
                    match node.get_normalized_fact() {
                        Some(nf) => facts.push(nf),
                        None => {
                            return Err(format!("missing prenormalized fact for node {}", node));
                        }
                    }
                }
            }
        }
        Ok(facts)
    }

    /// Get all facts that are inside the block of this cursor.
    /// This does not include imported facts, and it does not include facts that
    /// are top-level in the module.
    pub fn block_facts(&self) -> Vec<Fact> {
        let mut facts = vec![];
        for (env, i) in self.annotated_path.iter().skip(1) {
            for node in &env.nodes[0..*i] {
                if let Some(fact) = node.get_fact() {
                    facts.push(fact);
                }
            }
        }

        if let Some(block) = &self.node().get_block() {
            for node in &block.env.nodes {
                if let Some(fact) = node.get_fact() {
                    facts.push(fact);
                }
            }
        }
        facts
    }

    /// Get the goal for the current node.
    /// Returns None for Structural and Block nodes.
    /// Block nodes don't have goals directly - their goals are child nodes.
    pub fn goal(&self) -> Option<&'a Goal> {
        match self.node() {
            Node::Claim(goal, _, _, _) => Some(goal),
            _ => None,
        }
    }

    /// Get the pre-normalized goal for the current node, if available.
    /// Returns None for Structural and Block nodes, or if the goal hasn't been pre-normalized.
    pub fn normalized_goal(&self) -> Option<&'a NormalizedGoal> {
        match self.node() {
            Node::Claim(_, _, Some(normalized), _) => Some(normalized),
            _ => None,
        }
    }

    /// Gets the environment for the goal at the current node.
    pub fn goal_env(&self) -> Result<&Environment, String> {
        let node = self.node();
        if let Node::Structural(_, _) = node {
            return Err(format!(
                "node {} does not need a proof, so it has no goal environment",
                self
            ));
        }

        if let Some(block) = &node.get_block() {
            Ok(&block.env)
        } else {
            Ok(self.env())
        }
    }

    /// Does a postorder traversal of everything with a goal, at and below this node
    pub fn find_goals(&mut self, output: &mut Vec<NodeCursor<'a>>) {
        for i in 0..self.num_children() {
            self.descend(i);
            self.find_goals(output);
            self.ascend();
        }
        if self.node().has_goal() {
            output.push(self.clone());
        }
    }
}
