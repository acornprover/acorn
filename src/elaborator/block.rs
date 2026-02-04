use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use tower_lsp::lsp_types::Range;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp};
use crate::elaborator::environment::{Environment, LineType};
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::names::DefinedName;
use crate::elaborator::node::Node;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::kernel::atom::AtomId;
use crate::project::Project;
use crate::syntax::expression::Expression;
use crate::syntax::statement::{Body, StatementInfo};
use crate::syntax::token::{Token, TokenType};

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

    /// The environment created inside the block.
    /// Goals for this block are now represented as child nodes at the end of env.nodes,
    /// rather than in a separate field. This allows blocks to have multiple goals and
    /// ensures proper fact dependencies between goals.
    pub env: Environment,

    /// The source range for this block, if it came from source code.
    /// This spans from the opening keyword (forall, if, by, etc.) to the closing brace.
    /// Synthetic blocks created by the elaborator will have None.
    pub source_range: Option<Range>,
}

/// The different ways to construct a block.
/// Note that these don't necessarily have anything to do with type params.
/// I should probably rename this object.
#[derive(Debug)]
pub enum BlockParams<'a> {
    /// (theorem name, theorem range, premise, goal)
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
    ),

    /// The assumption to be used by the block, and the range of this assumption.
    Conditional(&'a AcornValue, Range),

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
    /// The values are constraints that need to be proved, synthetic in the sense
    /// that nothing like them explicitly appears in the code.
    /// When there are multiple values, each becomes a separate goal in the block.
    /// The range tells us what to squiggle if this block fails.
    TypeRequirement(Vec<AcornValue>, Range),

    /// No special params needed
    ForAll,
}

/// Checks if a statement is an explicit `false` claim.
fn is_explicit_false_claim(statement: &crate::syntax::statement::Statement) -> bool {
    if let StatementInfo::Claim(cs) = &statement.statement {
        if let Expression::Singleton(token) = &cs.claim {
            return token.token_type == TokenType::False;
        }
    }
    false
}

/// Checks if a body contains an explicit `false` claim (non-recursively).
fn body_contains_explicit_false(body: &Body) -> bool {
    body.statements.iter().any(is_explicit_false_claim)
}

impl Block {
    /// Creates a new block, as a direct child of the given environment.
    ///
    /// Note: The range from first_token to last_token may include part of the surrounding
    /// statement that introduces the block (e.g., "if", "theorem", etc.). If you just want
    /// the range within braces, you should look at the "body" parameter.
    pub fn new(
        project: &mut Project,
        env: &Environment,
        type_params: Vec<TypeParam>,
        args: Vec<(String, AcornType)>,
        params: BlockParams,
        first_token: &Token,
        last_token: &Token,
        body: Option<&Body>,
    ) -> error::Result<Block> {
        let mut subenv = env.create_child(first_token.line_number, body.is_none());

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

        let goal_prop = match params {
            BlockParams::Conditional(condition, range) => {
                let source = Source::premise(env.module_id, range, subenv.depth);
                let prop = Proposition::new(condition.clone(), vec![], source);
                subenv.add_node(Node::structural(project, &subenv, prop));
                None
            }
            BlockParams::Theorem(theorem_name, theorem_range, ref premise, ref unbound_goal) => {
                if let Some(name) = theorem_name {
                    // Within the theorem block, the theorem is treated like a function,
                    // with propositions to define its identity.
                    // This makes it less annoying to define inductive hypotheses.
                    subenv.add_definition(&DefinedName::unqualified(env.module_id, name));
                }

                if let Some((unbound_premise, premise_range)) = premise {
                    // Add the premise to the environment, when proving the theorem.
                    // The premise is unbound, so we need to bind the block's arg values.
                    let bound = unbound_premise.clone().bind_values(0, 0, &internal_args);
                    let source = Source::premise(env.module_id, *premise_range, subenv.depth);
                    let prop = Proposition::new(bound, vec![], source);
                    subenv.add_node(Node::structural(project, &subenv, prop));
                }

                let bound_goal = unbound_goal
                    .clone()
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
                Some(Proposition::new(bound_goal, vec![], source))
            }
            BlockParams::FunctionSatisfy(ref unbound_goal, ref return_type, range) => {
                // In the block, we need to prove this goal in bound form, so bind args to it.
                // The partial goal has variables 0..args.len() bound to the block's args,
                // but there is one last variable that needs to be existentially quantified.
                let partial_goal = unbound_goal
                    .clone()
                    .bind_values(0, 0, &internal_args)
                    .to_arbitrary();
                let bound_goal = AcornValue::exists(vec![return_type.to_arbitrary()], partial_goal);
                let source = Source::block_goal(env.module_id, range, subenv.depth);
                let prop = Proposition::new(bound_goal, vec![], source);
                Some(prop)
            }
            BlockParams::MatchCase(ref scrutinee, ref constructor, ref pattern_args, range) => {
                // Inside the block, the pattern arguments are constants.
                let mut arg_values = vec![];
                for (arg_name, arg_type) in pattern_args {
                    let def_str = format!("{}: {}", arg_name, arg_type);
                    let potential = subenv.bindings.add_unqualified_constant(
                        arg_name,
                        vec![],
                        arg_type.clone(),
                        None,
                        None,
                        vec![],
                        None,
                        def_str,
                    );
                    arg_values.push(potential.force_value());
                }
                // Inside the block, we can assume the pattern matches.
                let applied = AcornValue::apply(constructor.clone(), arg_values);
                let equality = AcornValue::equals(scrutinee.clone(), applied);
                let source = Source::premise(env.module_id, range, subenv.depth);
                let prop = Proposition::new(equality, vec![], source);
                subenv.add_node(Node::structural(project, &subenv, prop));
                None
            }
            BlockParams::TypeRequirement(ref constraints, range) => {
                // For backward compatibility, if there's exactly one constraint,
                // return it as goal_prop for the old single-goal path.
                // Multiple constraints will be handled separately below.
                if constraints.len() == 1 {
                    let source = Source::block_goal(env.module_id, range, subenv.depth);
                    Some(Proposition::new(constraints[0].clone(), vec![], source))
                } else {
                    None
                }
            }
            BlockParams::ForAll => None,
        };

        match body {
            Some(body) => {
                // Look ahead: if the block contains an explicit `false` claim,
                // mark the environment so that finding inconsistencies in
                // earlier claims is okay (the proof is heading towards `false`).
                if body_contains_explicit_false(body) {
                    subenv.will_include_explicit_false = true;
                }

                subenv.add_line_types(
                    LineType::Opening,
                    first_token.line_number,
                    body.left_brace.line_number,
                );
                for s in &body.statements {
                    subenv.add_statement(project, s)?;
                }
                subenv.add_line_types(
                    LineType::Closing,
                    body.right_brace.line_number,
                    body.right_brace.line_number,
                );
            }
            None => {
                // The subenv is an implicit block, so consider all the lines to be "opening".
                subenv.add_line_types(
                    LineType::Opening,
                    first_token.line_number,
                    last_token.line_number,
                );
            }
        };

        // If there is a goal proposition, add it as a child node at the end of the environment.
        // This allows the goal to use all facts from the block's internal nodes.
        if let Some(prop) = goal_prop {
            let goal_range = prop.source.range;
            let prop = Arc::new(prop);
            let goal = Goal::interior(&subenv, prop.clone())
                .map_err(|e| error::Error::new(first_token, last_token, &e))?;
            let fact = Fact::Proposition(prop);
            let goal_node = Node::Claim(goal, fact, None, None);
            let goal_index = subenv.add_node(goal_node);
            // Map the goal node to the appropriate source lines
            subenv.add_node_lines(goal_index, &goal_range);
        }

        // Handle multiple type requirements by adding each as a separate goal node
        if let BlockParams::TypeRequirement(constraints, range) = params {
            if constraints.len() > 1 {
                for constraint in constraints {
                    let source = Source::block_goal(env.module_id, range, env.depth);
                    let prop = Arc::new(Proposition::new(constraint, vec![], source));
                    let goal = Goal::interior(&subenv, prop.clone())
                        .map_err(|e| error::Error::new(first_token, last_token, &e))?;
                    let fact = Fact::Proposition(prop);
                    let goal_node = Node::Claim(goal, fact, None, None);
                    let goal_index = subenv.add_node(goal_node);
                    subenv.add_node_lines(goal_index, &range);
                }
            }
        }

        // Create the source range from first_token to last_token
        let source_range = Some(Range {
            start: first_token.start_pos(),
            end: last_token.end_pos(),
        });

        Ok(Block {
            args,
            env: subenv,
            source_range,
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

        // Find all unexportable constants.
        // This is a btree to make the ordering deterministic.
        let mut unexportable: BTreeMap<String, AcornType> = BTreeMap::new();
        outer_env
            .bindings
            .find_unknown_scoped_constants(inner_value, &mut unexportable);

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
    ) -> error::Result<(AcornValue, Range)> {
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
