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
use crate::names::DefinedName;
use crate::potential_value::PotentialValue;
use crate::project::Project;
use crate::proposition::Proposition;
use crate::source::{Source, SourceType};
use crate::statement::Body;
use crate::token::Token;

/// Proofs are structured into blocks.
/// The environment specific to this block can have a bunch of propositions that need to be
/// proved, along with helper statements to express those propositions, but they are not
/// visible to the outside world.
pub struct Block {
    /// The arguments to this block.
    /// They can either be "forall" arguments, or the arguments to a theorem.
    /// This does not include pattern-matched variables because those have additional constraints.
    /// Internally to the block, the arguments are constants.
    /// Externally, these arguments are variables.
    args: Vec<(String, AcornType)>,

    /// Sometimes the user specifies a goal for a block, that must be proven.
    /// The goal for a block is relative to its internal environment.
    /// In particular, the goal should not be generic. It should use arbitrary fixed types instead.
    ///
    /// Everything in the block can be used to achieve this goal.
    /// If there is no goal for the block, we can still use its conclusion externally,
    /// but we let the conclusion be determined by the code in the block.
    pub goal: Option<Goal>,

    /// The environment created inside the block.
    pub env: Environment,

    /// Whether this block is a todo block (goals inside should not be collected)
    pub is_todo: bool,

    /// Whether this block is a duplicate theorem (should return an error)
    pub is_duplicate_theorem: bool,
}

/// The different ways to construct a block.
/// Note that these don't necessarily have anything to do with type params.
/// I should probably rename this object.
#[derive(Debug)]
pub enum BlockParams<'a> {
    /// (theorem name, theorem range, premise, goal, duplicate)
    ///
    /// The premise and goal are unbound, to be proved based on the args of the theorem.
    ///
    /// The theorem should already be defined by this name in the external environment.
    /// It is either a bool, or a function from something -> bool.
    /// The meaning of the theorem is that it is true for all args.
    ///
    /// The premise is optional.
    ///
    /// The premise and goal should not have type variables in them.
    Theorem(
        Option<&'a str>,
        Range,
        Option<(AcornValue, Range)>,
        AcornValue,
        bool
    ),

    /// The assumption to be used by the block, and the range of this assumption.
    Conditional(&'a AcornValue, Range),

    /// The expression to solve for, and the range of the "solve <target>" component.
    Solve(AcornValue, Range),

    /// (unbound goal, function return type, range of condition)
    /// This goal has one more unbound variable than the block args account for.
    /// The last one, we are trying to prove there exists a variable that satisfies the goal.
    FunctionSatisfy(AcornValue, AcornType, Range),

    /// MatchCase represents a single case within a match statement.
    /// The scrutinee, the constructor, the pattern arguments, and the range of the pattern.
    MatchCase(AcornValue, AcornValue, Vec<(String, AcornType)>, Range),

    /// A block that is required by the type system.
    /// This can either be proving that a constrained type is inhabited, or proving
    /// that a type obeys a typeclass relationship.
    /// Either way, there is some value that needs to be proved, that's synthetic in the sense
    /// that nothing like it explicitly appears in the code.
    /// The range tells us what to squiggle if this block fails.
    TypeRequirement(AcornValue, Range),

    /// No special params needed
    ForAll,
    Problem,
    Todo,
}

impl Block {
    /// Creates a new block, as a direct child of the given environment.
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
        let mut internal_args = vec![];
        for (arg_name, generic_arg_type) in &args {
            let specific_arg_type = generic_arg_type.instantiate(&param_pairs);
            let def_str = format!("{}: {}", arg_name, specific_arg_type);
            let potential = subenv.bindings.add_unqualified_constant(
                arg_name,
                vec![],
                specific_arg_type,
                None,
                None,
                vec![],
                None,
                def_str,
            );
            internal_args.push(potential.force_value());
        }

        let is_todo = matches!(params, BlockParams::Todo);
        let mut is_duplicate_theorem = false;
        let goal = match params {
            BlockParams::Conditional(condition, range) => {
                let source = Source::premise(env.module_id, range, subenv.depth);
                let prop = Proposition::monomorphic(condition.clone(), source);
                subenv.add_node(Node::structural(project, &subenv, prop));
                None
            }
            BlockParams::Theorem(theorem_name, theorem_range, premise, unbound_goal, duplicate) => {
                if let Some(name) = theorem_name {
                    // Within the theorem block, the theorem is treated like a function,
                    // with propositions to define its identity.
                    // This makes it less annoying to define inductive hypotheses.
                    subenv.add_definition(&DefinedName::unqualified(env.module_id, name));
                }

                if let Some((unbound_premise, premise_range)) = premise {
                    // Add the premise to the environment, when proving the theorem.
                    // The premise is unbound, so we need to bind the block's arg values.
                    let bound = unbound_premise.bind_values(0, 0, &internal_args);
                    let source = Source::premise(env.module_id, premise_range, subenv.depth);
                    let prop = Proposition::monomorphic(bound, source);
                    subenv.add_node(Node::structural(project, &subenv, prop));
                }

                is_duplicate_theorem = duplicate;

                let bound_goal = unbound_goal
                    .bind_values(0, 0, &internal_args)
                    .to_arbitrary();
                // This is the goal we need to prove, therefore, it is not importable.
                let source = Source::theorem(
                    false,
                    env.module_id,
                    theorem_range,
                    false,
                    subenv.depth,
                    theorem_name.map(|s| s.to_string()),
                );
                Some(Goal::Prove(Proposition::monomorphic(bound_goal, source)))
            }
            BlockParams::FunctionSatisfy(unbound_goal, return_type, range) => {
                // In the block, we need to prove this goal in bound form, so bind args to it.
                // The partial goal has variables 0..args.len() bound to the block's args,
                // but there is one last variable that needs to be existentially quantified.
                let partial_goal = unbound_goal.bind_values(0, 0, &internal_args);
                let bound_goal = AcornValue::exists(vec![return_type], partial_goal);
                assert!(!bound_goal.has_generic());
                let source = Source::anonymous(env.module_id, range, env.depth);
                let prop = Proposition::monomorphic(bound_goal, source);
                Some(Goal::Prove(prop))
            }
            BlockParams::MatchCase(scrutinee, constructor, pattern_args, range) => {
                // Inside the block, the pattern arguments are constants.
                let mut arg_values = vec![];
                for (arg_name, arg_type) in pattern_args {
                    let def_str = format!("{}: {}", arg_name, arg_type);
                    let potential = subenv.bindings.add_unqualified_constant(
                        &arg_name,
                        vec![],
                        arg_type,
                        None,
                        None,
                        vec![],
                        None,
                        def_str,
                    );
                    arg_values.push(potential.force_value());
                }
                // Inside the block, we can assume the pattern matches.
                let applied = AcornValue::apply(constructor, arg_values);
                let equality = AcornValue::equals(scrutinee, applied);
                let source = Source::premise(env.module_id, range, subenv.depth);
                let prop = Proposition::monomorphic(equality, source);
                subenv.add_node(Node::structural(project, &subenv, prop));
                None
            }
            BlockParams::TypeRequirement(constraint, range) => {
                // We don't add any other given theorems.
                let source = Source::anonymous(env.module_id, range, env.depth);
                Some(Goal::Prove(Proposition::monomorphic(constraint, source)))
            }
            BlockParams::Solve(target, range) => Some(Goal::Solve(target, range)),
            BlockParams::ForAll | BlockParams::Problem | BlockParams::Todo => None,
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
            is_todo,
            is_duplicate_theorem
        })
    }

    /// Convert a boolean value from the block's environment to a value in the outer environment.
    fn externalize_bool(&self, outer_env: &Environment, inner_value: &AcornValue) -> AcornValue {
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
            if c.name.module_id() == outer_env.module_id {
                if let Some(i) = map.get(&c.name.to_string()) {
                    assert!(c.params.is_empty());
                    Some(AcornValue::Variable(*i, c.instance_type.clone()))
                } else {
                    None
                }
            } else {
                None
            }
        });

        AcornValue::forall(forall_types, AcornValue::exists(exists_types, replaced))
    }

    /// Returns a claim usable in the outer environment, and a range where it comes from.
    /// Note that this will not generalize arbitrary types.
    pub fn externalize_last_claim(
        &self,
        outer_env: &Environment,
        token: &Token,
    ) -> compilation::Result<(AcornValue, Range)> {
        let prop = match self.env.nodes.last() {
            Some(node) => match node.proposition() {
                Some(p) => p,
                None => {
                    return Err(token.error("expected a proposition in this block"));
                }
            },
            None => {
                return Err(token.error("expected a proposition in this block"));
            }
        };
        let outer_claim = self.externalize_bool(outer_env, &prop.value);
        Ok((outer_claim, prop.source.range))
    }

    /// Checks if this block solves for the given target.
    /// If it does, returns an externalized proposition with the solution, and the range where it
    /// occurs.
    /// "Externalized" means that it is valid in the environment outside the block.
    pub fn solves(
        &self,
        outer_env: &Environment,
        target: &AcornValue,
    ) -> Option<(AcornValue, Range)> {
        let (outer_claim, range) = match self.externalize_last_claim(outer_env, &Token::empty()) {
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

/// The Environment is arranged like a tree structure. It contains many nodes. Some nodes
/// have blocks, with their own environments.
/// There are three types of nodes.
/// 1. Structural nodes, that we can assume without proof
/// 2. Plain claims, that we need to prove
/// 3. Nodes with blocks, where we need to recurse into the block and prove those nodes.
pub enum Node {
    /// Some nodes contain propositions that are structurally true.
    /// The prover doesn't need to prove these.
    /// For example, this could be an axiom, or a definition.
    /// It could also be a form like a citation that has already been proven by the compiler.
    Structural(Fact),

    /// A claim is something that we need to prove, and then we can subsequently use it.
    Claim(Proposition),

    /// A block has its own environment inside. We need to validate everything in the block.
    /// The block might not exist in the code, but it at least needs to exist for the prover.
    /// The optional fact is what we can use externally once the block is proven.
    /// It is relative to the outside environment.
    /// Other than the external claim, nothing else in the block is visible outside the block.
    Block(Block, Option<Fact>),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Node::Structural(fact) => write!(f, "structural: {}", fact),
            Node::Claim(prop) => write!(f, "claim: {}", prop),
            Node::Block(_, Some(fact)) => write!(f, "block: {}", fact),
            Node::Block(_, None) => write!(f, "block: None"),
        }
    }
}

impl Node {
    pub fn structural(project: &Project, env: &Environment, prop: Proposition) -> Node {
        let prop = env.bindings.expand_theorems(prop, project);
        Node::Structural(Fact::Proposition(prop))
    }

    pub fn claim(project: &Project, env: &Environment, prop: Proposition) -> Node {
        let prop = env.bindings.expand_theorems(prop, project);
        Node::Claim(prop)
    }

    /// This does not expand theorems. I can imagine this coming up, but it would be weird.
    pub fn definition(constant: PotentialValue, definition: AcornValue, source: Source) -> Node {
        let fact = Fact::Definition(constant, definition, source);
        Node::Structural(fact)
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
            Some(prop) => Some(Fact::Proposition(
                env.bindings.expand_theorems(prop, project),
            )),
            None => None,
        };
        Node::Block(block, fact)
    }

    pub fn instance(block: Option<Block>, fact: Fact) -> Node {
        match block {
            Some(b) => Node::Block(b, Some(fact)),
            None => Node::Structural(fact),
        }
    }

    /// Whether this node corresponds to a goal that needs to be proved.
    pub fn has_goal(&self) -> bool {
        match self {
            Node::Structural(_) => false,
            Node::Claim(_) => true,
            Node::Block(block, _) => block.goal.is_some(),
        }
    }

    pub fn first_line(&self) -> u32 {
        match self {
            Node::Structural(f) => f.source().range.start.line,
            Node::Claim(p) => p.source.range.start.line,
            Node::Block(block, _) => block.env.first_line,
        }
    }

    pub fn last_line(&self) -> u32 {
        match self {
            Node::Structural(f) => f.source().range.end.line,
            Node::Claim(p) => p.source.range.end.line,
            Node::Block(block, _) => block.env.last_line(),
        }
    }

    pub fn get_block(&self) -> Option<&Block> {
        match self {
            Node::Block(block, _) => Some(block),
            _ => None,
        }
    }

    /// The source of this node, if there is one.
    pub fn source(&self) -> Option<&Source> {
        match self {
            Node::Structural(f) => Some(f.source()),
            Node::Claim(p) => Some(&p.source),
            Node::Block(_, Some(f)) => Some(f.source()),
            Node::Block(_, None) => None,
        }
    }

    /// The proposition at this node, if there is one.
    pub fn proposition(&self) -> Option<&Proposition> {
        match self {
            Node::Structural(Fact::Proposition(p)) => Some(p),
            Node::Claim(p) => Some(p),
            Node::Block(_, Some(Fact::Proposition(p))) => Some(p),
            _ => None,
        }
    }

    /// The block name is used to describe the block when caching block -> premise dependencies.
    /// good_block_name finds whether we have a comprehensible name.
    fn good_block_name(&self) -> Option<String> {
        match &self.source()?.source_type {
            SourceType::Theorem(name) => match name {
                Some(name) => Some(name.clone()),
                None => None,
            },
            SourceType::ConstantDefinition(_, name) => Some(name.clone()),
            SourceType::TypeDefinition(type_name, suffix) => {
                Some(format!("{}.{}", type_name, suffix))
            }
            SourceType::Instance(c, tc) => Some(format!("{}.{}", c, tc)),
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
            Node::Structural(f) => Some(f.clone()),
            Node::Claim(p) => Some(Fact::Proposition(p.clone())),
            Node::Block(_, Some(f)) => Some(f.clone()),
            _ => None,
        }
    }

    /// The source name is used to describe the premise when caching block -> premise dependencies.
    /// All importable facts should have a source name.
    pub fn source_name(&self) -> Option<String> {
        self.source()?.name()
    }

    /// Returns the block name for this node, using the same logic as NodeCursor::block_name
    pub fn block_name(&self) -> String {
        match self.good_block_name() {
            Some(s) => s,
            None => self.first_line().to_string(),
        }
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
                Node::Claim(prop) => write!(f, ", claim: {}", prop)?,
                Node::Block(block, _) => {
                    if let Some(goal) = &block.goal {
                        write!(f, ", block_goal: {:?}", goal)?;
                    }
                }
                _ => {}
            }
        }

        write!(f, ")")
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

    /// Get the top-level node above this cursor.
    fn top_node(&self) -> &'a Node {
        let (env, index) = self.annotated_path[0];
        &env.nodes[index]
    }

    /// The block name is used to describe the block when caching block -> premise dependencies.
    /// This always returns the name of the top-level node, regardless of the current position.
    pub fn block_name(&self) -> String {
        self.top_node().block_name()
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
        match self.node() {
            Node::Block(block, _o) => {
                if block.is_todo {
                    return false;
                }else{
                    return self.node().has_goal() || self.num_children() > 0
                }
            },
            _ => return self.node().has_goal() || self.num_children() > 0
        }
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

    /// All facts that can be used to prove the current node.
    /// This includes imported facts.
    pub fn usable_facts(&self, project: &Project) -> Vec<Fact> {
        let mut facts = project.imported_facts(self.env().module_id, None);
        let (env, i) = &self.annotated_path[0];
        for node in &env.nodes[0..*i] {
            if let Some(fact) = node.get_fact() {
                facts.push(fact);
            }
        }

        facts.extend(self.block_facts());
        facts
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

    /// Get a goal context for the current node.
    pub fn goal_context(&self) -> Result<GoalContext, String> {
        let node = self.node();
        if let Node::Structural(_) = node {
            return Err(format!(
                "node {} does not need a proof, so it has no goal context",
                self
            ));
        }

        if let Some(block) = &node.get_block() {
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
            let prop = node.proposition().unwrap();
            let first_line = prop.source.range.start.line;
            let last_line = prop.source.range.end.line;
            return Ok(GoalContext::new(
                self.env(),
                Goal::Prove(prop.clone()),
                first_line,
                first_line,
                last_line,
            ));
        }
    }

    /// Gets the environment for the goal at the current node.
    pub fn goal_env(&self) -> Result<&Environment, String> {
        let node = self.node();
        if let Node::Structural(_) = node {
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
        // Check if the current node is a todo block
        if let Some(block) = self.node().get_block() {
            if block.is_todo {
                // Don't recurse into todo blocks
                return;
            }
        }

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
