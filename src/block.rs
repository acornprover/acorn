use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::compilation::{self, ErrorSource};
use crate::environment::{Environment, LineType};
use crate::fact::Fact;
use crate::goal::{Goal, GoalContext};
use crate::project::Project;
use crate::proof_step::Truthiness;
use crate::proposition::{Proposition, SourceType};
use crate::statement::Body;
use crate::token::Token;

// Proofs are structured into blocks.
// The environment specific to this block can have a bunch of propositions that need to be
// proved, along with helper statements to express those propositions, but they are not
// visible to the outside world.
pub struct Block {
    // The arguments to this block.
    // They can either be "forall" arguments, or the arguments to a theorem.
    // This does not include pattern-matched variables because those have additional constraints.
    // Internally to the block, the arguments are constants.
    // Externally, these arguments are variables.
    args: Vec<(String, AcornType)>,

    // Sometimes the user specifies a goal for a block, that must be proven.
    // The goal for a block is relative to its internal environment.
    // In particular, the goal should not be generic. It should use arbitrary fixed types instead.
    //
    // Everything in the block can be used to achieve this goal.
    // If there is no goal for the block, we can still use its conclusion externally,
    // but we let the conclusion be determined by the code in the block.
    pub goal: Option<Goal>,

    // The environment created inside the block.
    pub env: Environment,
}

// The different ways to construct a block.
// Note that these don't necessarily have anything to do with type params.
// I should probably rename this object.
#[derive(Debug)]
pub enum BlockParams<'a> {
    // (theorem name, theorem range, premise, goal)
    //
    // The premise and goal are unbound, to be proved based on the args of the theorem.
    //
    // The theorem should already be defined by this name in the external environment.
    // It is either a bool, or a function from something -> bool.
    // The meaning of the theorem is that it is true for all args.
    //
    // The premise is optional.
    //
    // The premise and goal should not have type variables in them.
    Theorem(
        Option<&'a str>,
        Range,
        Option<(AcornValue, Range)>,
        AcornValue,
    ),

    // The assumption to be used by the block, and the range of this assumption.
    Conditional(&'a AcornValue, Range),

    // The expression to solve for, and the range of the "solve <target>" component.
    Solve(AcornValue, Range),

    // (unbound goal, function return type, range of condition)
    // This goal has one more unbound variable than the block args account for.
    // The last one, we are trying to prove there exists a variable that satisfies the goal.
    FunctionSatisfy(AcornValue, AcornType, Range),

    // MatchCase represents a single case within a match statement.
    // The scrutinee, the constructor, the pattern arguments, and the range of the pattern.
    MatchCase(AcornValue, AcornValue, Vec<(String, AcornType)>, Range),

    // A block that is required by the type system.
    // This can either be proving that a constrained type is inhabited, or proving
    // that a type obeys a typeclass relationship.
    // Either way, there is some value that needs to be proved, that's synthetic in the sense
    // that nothing like it explicitly appears in the code.
    // The range tells us what to squiggle if this block fails.
    TypeRequirement(AcornValue, Range),

    // No special params needed
    ForAll,
    Problem,
}

impl Block {
    // Creates a new block, as a direct child of the given environment.
    pub fn new(
        project: &mut Project,
        env: &Environment,
        type_params: Vec<TypeParam>,
        args: Vec<(String, AcornType)>,
        params: BlockParams,
        first_line: u32,
        last_line: u32,
        body: Option<&Body>,
    ) -> compilation::Result<Block> {
        let mut subenv = env.create_child(first_line, body.is_none());

        // Inside the block, the type parameters are arbitrary types.
        let param_pairs: Vec<(String, AcornType)> = type_params
            .iter()
            .map(|param| {
                (
                    param.name.clone(),
                    subenv.bindings.add_arbitrary_type(param.clone()),
                )
            })
            .collect();

        // Inside the block, the arguments are constants.
        for (arg_name, generic_arg_type) in &args {
            let specific_arg_type = generic_arg_type.instantiate(&param_pairs);
            subenv
                .bindings
                .add_constant(&arg_name, vec![], specific_arg_type, None, None);
        }

        let goal = match params {
            BlockParams::Conditional(condition, range) => {
                subenv.add_node(
                    project,
                    true,
                    Proposition::premise(condition.clone(), env.module_id, range),
                    None,
                );
                None
            }
            BlockParams::Theorem(theorem_name, theorem_range, premise, unbound_goal) => {
                let arg_values = args
                    .iter()
                    .map(|(name, _)| {
                        subenv
                            .bindings
                            .get_constant_value(name)
                            .unwrap()
                            .force_value()
                    })
                    .collect::<Vec<_>>();

                if let Some(name) = theorem_name {
                    // Within the theorem block, the theorem is treated like a function,
                    // with propositions to define its identity.
                    // This makes it less annoying to define inductive hypotheses.
                    subenv.add_identity_props(project, name);
                }

                if let Some((unbound_premise, premise_range)) = premise {
                    // Add the premise to the environment, when proving the theorem.
                    // The premise is unbound, so we need to bind the block's arg values.
                    let bound = unbound_premise.bind_values(0, 0, &arg_values);

                    subenv.add_node(
                        project,
                        true,
                        Proposition::premise(bound, env.module_id, premise_range),
                        None,
                    );
                }

                let bound_goal = unbound_goal.bind_values(0, 0, &arg_values).to_arbitrary();
                Some(Goal::Prove(Proposition::theorem(
                    false,
                    bound_goal,
                    env.module_id,
                    theorem_range,
                    theorem_name.map(|s| s.to_string()),
                )))
            }
            BlockParams::FunctionSatisfy(unbound_goal, return_type, range) => {
                // In the block, we need to prove this goal in bound form, so bind args to it.
                let arg_values = args
                    .iter()
                    .map(|(name, _)| {
                        subenv
                            .bindings
                            .get_constant_value(name)
                            .unwrap()
                            .force_value()
                    })
                    .collect::<Vec<_>>();
                // The partial goal has variables 0..args.len() bound to the block's args,
                // but there is one last variable that needs to be existentially quantified.
                let partial_goal = unbound_goal.bind_values(0, 0, &arg_values);
                let bound_goal = AcornValue::new_exists(vec![return_type], partial_goal);
                assert!(!bound_goal.has_generic());
                let prop = Proposition::anonymous(bound_goal, env.module_id, range);
                Some(Goal::Prove(prop))
            }
            BlockParams::MatchCase(scrutinee, constructor, pattern_args, range) => {
                // Inside the block, the pattern arguments are constants.
                let mut arg_values = vec![];
                for (arg_name, arg_type) in pattern_args {
                    subenv
                        .bindings
                        .add_constant(&arg_name, vec![], arg_type, None, None);
                    arg_values.push(
                        subenv
                            .bindings
                            .get_constant_value(&arg_name)
                            .unwrap()
                            .force_value(),
                    );
                }
                // Inside the block, we can assume the pattern matches.
                let applied = AcornValue::new_apply(constructor, arg_values);
                let equality = AcornValue::new_equals(scrutinee, applied);
                subenv.add_node(
                    project,
                    true,
                    Proposition::premise(equality, env.module_id, range),
                    None,
                );
                None
            }
            BlockParams::TypeRequirement(constraint, range) => {
                // We don't add any other given theorems.
                Some(Goal::Prove(Proposition::anonymous(
                    constraint,
                    env.module_id,
                    range,
                )))
            }
            BlockParams::Solve(target, range) => Some(Goal::Solve(target, range)),
            BlockParams::ForAll | BlockParams::Problem => None,
        };

        match body {
            Some(body) => {
                subenv.add_line_types(
                    LineType::Opening,
                    first_line,
                    body.left_brace.line_number as u32,
                );
                for s in &body.statements {
                    subenv.add_statement(project, s)?;
                }
                subenv.add_line_types(
                    LineType::Closing,
                    body.right_brace.line_number as u32,
                    body.right_brace.line_number as u32,
                );
            }
            None => {
                // The subenv is an implicit block, so consider all the lines to be "opening".
                subenv.add_line_types(LineType::Opening, first_line, last_line);
            }
        };
        Ok(Block {
            args,
            env: subenv,
            goal,
        })
    }

    // Convert a boolean value from the block's environment to a value in the outer environment.
    fn export_bool(&self, outer_env: &Environment, inner_value: &AcornValue) -> AcornValue {
        // The constants that were block arguments will export as "forall" variables.
        let mut forall_names: Vec<String> = vec![];
        let mut forall_types: Vec<AcornType> = vec![];
        for (name, t) in &self.args {
            forall_names.push(name.clone());
            forall_types.push(t.clone());
        }

        // Find all unexportable constants
        let mut unexportable: HashMap<String, AcornType> = HashMap::new();
        outer_env
            .bindings
            .find_unknown_local_constants(inner_value, &mut unexportable);

        // Unexportable constants that are not arguments export as "exists" variables.
        let mut exists_names = vec![];
        let mut exists_types = vec![];
        for (name, t) in unexportable {
            if forall_names.contains(&name) {
                continue;
            }
            exists_names.push(name);
            exists_types.push(t);
        }

        // Internal variables need to be shifted over
        let shift_amount = (forall_names.len() + exists_names.len()) as AtomId;

        // The forall must be outside the exists, so order stack variables appropriately
        let mut map: HashMap<String, AtomId> = HashMap::new();
        for (i, name) in forall_names
            .into_iter()
            .chain(exists_names.into_iter())
            .enumerate()
        {
            map.insert(name, i as AtomId);
        }

        // Replace the internal constants with variables
        let replaced = inner_value.clone().insert_stack(0, shift_amount);
        let replaced = replaced.replace_constants(0, &|c| {
            if c.module_id == outer_env.module_id {
                if let Some(i) = map.get(&c.name) {
                    assert!(c.params.is_empty());
                    Some(AcornValue::Variable(*i, c.instance_type.clone()))
                } else {
                    None
                }
            } else {
                None
            }
        });

        AcornValue::new_forall(forall_types, AcornValue::new_exists(exists_types, replaced))
    }

    // Returns a claim usable in the outer environment, and a range where it comes from.
    // Note that this will not generalize arbitrary types.
    pub fn export_last_claim(
        &self,
        outer_env: &Environment,
        token: &Token,
    ) -> compilation::Result<(AcornValue, Range)> {
        let (inner_claim, range) = match self.env.nodes.last() {
            Some(p) => (&p.claim.value, p.claim.source.range),
            None => {
                return Err(token.error("expected a claim in this block"));
            }
        };
        let outer_claim = self.export_bool(outer_env, inner_claim);
        Ok((outer_claim, range))
    }

    // Checks if this block solves for the given target.
    // If it does, returns an exported proposition with the solution, and the range where it
    // occurs.
    pub fn solves(
        &self,
        outer_env: &Environment,
        target: &AcornValue,
    ) -> Option<(AcornValue, Range)> {
        let (outer_claim, range) = match self.export_last_claim(outer_env, &Token::empty()) {
            Ok((c, r)) => (c, r),
            Err(_) => return None,
        };
        match &outer_claim {
            // We only allow <target> == <solution>, rather than the other way around.
            AcornValue::Binary(BinaryOp::Equals, left, _) => {
                if left.as_ref() == target {
                    Some((outer_claim, range))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

// Logically, the Environment is arranged like a tree structure.
// There are three types of nodes.
// 1. Structural nodes, that we can assume without proof
// 2. Plain claims, that we need to prove
// 3. Nodes with blocks, where we need to recurse into the block and prove those nodes.
pub struct Node {
    // Whether this proposition has already been proved structurally.
    // For example, this could be an axiom, or a definition.
    pub structural: bool,

    // The proposition represented by this tree.
    // If this proposition has a block, this represents the "external claim".
    // It is the value we can assume is true, in the outer environment, when everything
    // in the inner environment has been proven.
    // Besides the claim, nothing else from the block is visible externally.
    //
    // This claim needs to be proved for nonstructural propositions, when there is no block.
    pub claim: Proposition,

    // The body of the proposition, when it has an associated block.
    // When there is a block, proving every proposition in the block implies that the
    // claim is proven as well.
    pub block: Option<Block>,
}

impl Node {
    pub fn new(
        project: &Project,
        env: &Environment,
        structural: bool,
        proposition: Proposition,
        block: Option<Block>,
    ) -> Self {
        // Make sure we aren't adding an invalid claim.
        proposition
            .value
            .validate()
            .unwrap_or_else(|e| panic!("invalid claim: {:#?} ({})", proposition.value, e));

        if structural {
            assert!(block.is_none());
        }

        // Expand theorems in the proposition.
        let value = proposition.value.replace_constants(0, &|c| {
            let bindings = if env.module_id == c.module_id {
                &env.bindings
            } else {
                &project
                    .get_env_by_id(c.module_id)
                    .expect("missing module during add_proposition")
                    .bindings
            };
            if bindings.is_theorem(&c.name) {
                match bindings.get_definition_and_params(&c.name) {
                    Some((def, params)) => {
                        let mut pairs = vec![];
                        for (param, t) in params.iter().zip(c.params.iter()) {
                            pairs.push((param.name.clone(), t.clone()));
                        }
                        Some(def.instantiate(&pairs))
                    }
                    None => None,
                }
            } else {
                None
            }
        });

        let claim = proposition.with_value(value);
        Node {
            structural,
            claim,
            block,
        }
    }

    // Whether this node corresponds to a goal that needs to be proved.
    pub fn has_goal(&self) -> bool {
        if self.structural {
            return false;
        }
        match &self.block {
            Some(b) => b.goal.is_some(),
            None => true,
        }
    }

    pub fn last_line(&self) -> u32 {
        if let Some(block) = &self.block {
            block.env.last_line()
        } else {
            self.claim.source.range.end.line
        }
    }

    // The block name is used to cache the premises used for the entire block.
    pub fn block_name(&self) -> Option<String> {
        match &self.claim.source.source_type {
            SourceType::Theorem(name) => name.clone(),
            SourceType::ConstantDefinition(_, name) => Some(name.clone()),
            SourceType::TypeDefinition(type_name, suffix) => {
                Some(format!("{}.{}", type_name, suffix))
            }
            _ => None,
        }
    }
}

// A NodeCursor points at a node. It is used to traverse the nodes in an environment.
#[derive(Clone)]
pub struct NodeCursor<'a> {
    // All the environments that surround this node.
    // (env, index) pairs tell you that the node env.nodes[index] to get to
    // the next environment.
    annotated_path: Vec<(&'a Environment, usize)>,
}

impl fmt::Display for NodeCursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.path())
    }
}

impl<'a> NodeCursor<'a> {
    pub fn from_path(env: &'a Environment, path: &[usize]) -> Self {
        assert!(path.len() > 0);
        let mut iter = NodeCursor::new(env, path[0]);
        for &i in &path[1..] {
            iter.descend(i);
        }
        iter
    }

    // Only call this on a module level environment.
    // Returns None if there are no nodes in the environment.
    pub fn new(env: &'a Environment, index: usize) -> Self {
        assert_eq!(env.depth, 0);
        assert!(env.nodes.len() > index);
        NodeCursor {
            annotated_path: vec![(env, index)],
        }
    }

    // The environment that contains the current node.
    pub fn env(&self) -> &'a Environment {
        self.annotated_path.last().unwrap().0
    }

    pub fn current(&self) -> &'a Node {
        let (env, index) = self.annotated_path.last().unwrap();
        &env.nodes[*index]
    }

    pub fn top_index(&self) -> usize {
        let (_, index) = self.annotated_path[0];
        index
    }

    // Can use this as an identifier for the iterator, to compare two of them
    pub fn path(&self) -> Vec<usize> {
        self.annotated_path.iter().map(|(_, i)| *i).collect()
    }

    pub fn num_children(&self) -> usize {
        match self.current().block {
            Some(ref b) => b.env.nodes.len(),
            None => 0,
        }
    }

    // child_index must be less than num_children
    pub fn descend(&mut self, child_index: usize) {
        let new_env = match &self.current().block {
            Some(b) => &b.env,
            None => panic!("descend called on a node without a block"),
        };
        assert!(child_index < new_env.nodes.len());
        self.annotated_path.push((new_env, child_index));
    }

    // Whether we can advance to the next sibling, keeping environment the same.
    pub fn has_next(&self) -> bool {
        let (env, index) = self.annotated_path.last().unwrap();
        index + 1 < env.nodes.len()
    }

    // Advances to the next sibling, keeping environment the same.
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

    // The fact at the current node.
    pub fn get_fact(&self) -> Fact {
        let truthiness = if self.env().depth == 0 {
            Truthiness::Factual
        } else {
            Truthiness::Hypothetical
        };
        Fact::new(self.current().claim.clone(), truthiness)
    }

    // All facts that can be used to prove the current node.
    // This includes imported facts.
    pub fn usable_facts(&self, project: &Project) -> Vec<Fact> {
        let mut facts = project.imported_facts(self.env().module_id, None);
        for (env, i) in &self.annotated_path {
            for prop in &env.nodes[0..*i] {
                let truthiness = if env.depth == 0 {
                    Truthiness::Factual
                } else {
                    Truthiness::Hypothetical
                };
                facts.push(Fact::new(prop.claim.clone(), truthiness));
            }
        }

        if let Some(block) = &self.current().block {
            for p in &block.env.nodes {
                facts.push(Fact::new(p.claim.clone(), Truthiness::Hypothetical));
            }
        }

        facts
    }

    // Get a goal context for the current node.
    pub fn goal_context(&self) -> Result<GoalContext, String> {
        let node = self.current();
        if node.structural {
            return Err(format!(
                "node {} does not need a proof, so it has no goal context",
                self
            ));
        }

        if let Some(block) = &node.block {
            let first_line = block.env.first_line;
            let last_line = block.env.last_line();
            let goal = match &block.goal {
                Some(goal) => goal,
                None => return Err(format!("block at {} has no goal", self)),
            };
            Ok(GoalContext::new(
                &block.env,
                goal.clone(),
                last_line,
                first_line,
                last_line,
            ))
        } else {
            let first_line = node.claim.source.range.start.line;
            let last_line = node.claim.source.range.end.line;
            return Ok(GoalContext::new(
                self.env(),
                Goal::Prove(node.claim.clone()),
                first_line,
                first_line,
                last_line,
            ));
        }
    }

    // Does a postorder traversal of everything with a goal, at and below this node
    pub fn find_goals(&mut self, output: &mut Vec<NodeCursor<'a>>) {
        for i in 0..self.num_children() {
            self.descend(i);
            self.find_goals(output);
            self.ascend();
        }
        if self.current().has_goal() {
            output.push(self.clone());
        }
    }
}
