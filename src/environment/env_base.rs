use std::collections::HashSet;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::{AcornType, Datatype, TypeParam};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::binding_map::BindingMap;
use crate::block::{Block, BlockParams, Node, NodeCursor};
use crate::compilation::{self, ErrorSource, PanicOnError};
use crate::evaluator::Evaluator;
use crate::fact::Fact;
use crate::module::ModuleId;
use crate::names::DefinedName;
use crate::project::Project;
use crate::proposition::Proposition;
use crate::source::Source;
use crate::statement::{Body, Statement};
use crate::token::{Token, TokenIter};
use crate::token_map::{TokenInfo, TokenKey, TokenMap};

/// The Environment takes Statements as input and processes them.
/// It does not prove anything directly, but it is responsible for determining which
/// things need to be proved, and which statements are usable in which proofs.
/// It creates subenvironments for nested blocks.
/// It does not have to be efficient enough to run in the inner loop of the prover.
pub struct Environment {
    pub module_id: ModuleId,

    /// What all the names mean in this environment
    pub bindings: BindingMap,

    /// The nodes structure is fundamentally linear.
    /// Each node depends only on the nodes before it.
    pub nodes: Vec<Node>,

    /// Theorems consist of theorem statements that need to be proven.
    /// Used to check for duplicate theorems
    pub theorems: HashSet<AcornValue>,

    /// Whether a plain "false" is anywhere in this environment.
    /// This indicates that the environment is supposed to have contradictory facts.
    pub includes_explicit_false: bool,

    /// For the base environment, first_line is zero.
    /// first_line is usually nonzero when the environment is a subenvironment.
    /// line_types[0] corresponds to first_line in the source document.
    pub first_line: u32,
    pub line_types: Vec<LineType>,

    /// Implicit blocks aren't written in the code; they are created for theorems that
    /// the user has asserted without proof.
    pub implicit: bool,

    /// The depth if you think of the environments in a module like a tree structure.
    /// The root environment for a module has depth zero.
    /// Each child node has a depth of one plus its parent.
    pub depth: u32,

    /// A map from tokens to information about them.
    /// This is not copied for child environments.
    pub token_map: TokenMap,

    /// Used during statement parsing. Cleared whenever they are attached to something.
    /// Each line is one entry.
    pub doc_comments: Vec<String>,

    /// Module-level documentation from doc comments at the top of the file.
    pub module_doc_comments: Vec<String>,

    /// Whether we're still at the beginning of the file and can collect module doc comments.
    pub at_module_beginning: bool,

    /// The line number of the last statement we processed (for detecting blank lines).
    pub last_statement_line: Option<u32>,
}

impl Environment {
    pub fn new(module_id: ModuleId) -> Self {
        Environment {
            module_id,
            bindings: BindingMap::new(module_id),
            nodes: Vec::new(),
            theorems: HashSet::new(),
            includes_explicit_false: false,
            first_line: 0,
            line_types: Vec::new(),
            implicit: false,
            depth: 0,
            token_map: TokenMap::new(),
            doc_comments: Vec::new(),
            module_doc_comments: Vec::new(),
            at_module_beginning: true,
            last_statement_line: None,
        }
    }

    /// Create a child environment.
    pub fn create_child(&self, first_line: u32, implicit: bool) -> Self {
        Environment {
            module_id: self.module_id,
            bindings: self.bindings.clone(),
            nodes: Vec::new(),
            theorems: HashSet::new(),
            includes_explicit_false: false,
            first_line,
            line_types: Vec::new(),
            implicit,
            depth: self.depth + 1,
            token_map: TokenMap::new(),
            doc_comments: Vec::new(),
            module_doc_comments: Vec::new(), // Child environments don't inherit module doc comments
            at_module_beginning: false,      // Child environments are never at module beginning
            last_statement_line: None,
        }
    }

    fn next_line(&self) -> u32 {
        self.line_types.len() as u32 + self.first_line
    }

    pub fn last_line(&self) -> u32 {
        self.next_line() - 1
    }

    /// Add line types for the given range, inserting empties as needed.
    /// If the line already has a type, do nothing.
    pub fn add_line_types(&mut self, line_type: LineType, first: u32, last: u32) {
        while self.next_line() < first {
            self.line_types.push(LineType::Empty);
        }
        while self.next_line() <= last {
            self.line_types.push(line_type);
        }
    }

    /// Add all the lines covered by the statement as the "Other" type.
    pub fn add_other_lines(&mut self, statement: &Statement) {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            statement.last_line(),
        );
    }

    /// Associate the node with the given index with all lines in the range.
    pub fn add_node_lines(&mut self, index: usize, range: &Range) {
        self.add_line_types(LineType::Node(index), range.start.line, range.end.line);
    }

    pub fn get_line_type(&self, line: u32) -> Option<LineType> {
        if line < self.first_line {
            return None;
        }
        let index = (line - self.first_line) as usize;
        if index < self.line_types.len() {
            Some(self.line_types[index])
        } else {
            None
        }
    }

    /// Adds a node to the environment tree.
    /// Returns the index of the newly added node.
    pub fn add_node(&mut self, node: Node) -> usize {
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    /// Returns an evaluator that modifies the token map.
    pub fn evaluator<'a>(&'a mut self, project: &'a Project) -> Evaluator<'a> {
        Evaluator::new(project, &self.bindings, Some(&mut self.token_map))
    }

    /// Adds a node to represent the definition of the provided
    /// constant.
    pub fn add_definition(&mut self, defined_name: &DefinedName) {
        let Some(definition) = self.bindings.get_definition(defined_name) else {
            return;
        };

        // This constant can be generic, with type variables in it.
        let potential = self
            .bindings
            .get_constant_value(defined_name, &PanicOnError)
            .expect("bad add_definition call");
        let range = self
            .bindings
            .get_definition_range(defined_name)
            .unwrap()
            .clone();
        let name = defined_name.to_string();
        let source = Source::constant_definition(
            self.module_id,
            range,
            self.depth,
            potential.clone().to_generic_value(),
            &name,
        );

        self.add_node(Node::definition(potential, definition.clone(), source));
    }

    /// Takes the currently collected doc comments and returns them, clearing the collection.
    pub fn take_doc_comments(&mut self) -> Vec<String> {
        std::mem::take(&mut self.doc_comments)
    }

    /// Returns the module documentation.
    pub fn get_module_doc_comments(&self) -> &Vec<String> {
        &self.module_doc_comments
    }

    /// Defines a new constant, adding a node for its definition and also tracking its definition range.
    pub fn define_constant(
        &mut self,
        name: DefinedName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        range: Range,
        definition_string: Option<String>,
    ) {
        let doc_comments = self.take_doc_comments();
        self.bindings.add_defined_name(
            &name,
            params,
            constant_type,
            definition,
            None,
            doc_comments,
            Some(range.clone()),
            definition_string,
        );
        self.add_definition(&name);
    }

    pub fn get_definition(&self, name: &DefinedName) -> Option<&AcornValue> {
        self.bindings.get_definition(name)
    }

    /// Finds the token at the given line and character position, along with the environment that
    /// it should be evaluated in.
    pub fn find_token(
        &self,
        line_number: u32,
        character: u32,
    ) -> Option<(&Environment, &TokenKey, &TokenInfo)> {
        if let Some((key, token_info)) = self.token_map.get(line_number, character) {
            return Some((&self, &key, &token_info));
        }

        if let Some(child_env) = self.env_for_line_step(line_number) {
            return child_env.find_token(line_number, character);
        }
        None
    }

    /// Returns an error if you are not allowed to add attributes to this type.
    pub fn check_can_add_attributes<'a>(
        &self,
        name_token: &Token,
        datatype_type: &'a AcornType,
    ) -> compilation::Result<&'a Datatype> {
        match &datatype_type {
            AcornType::Data(datatype, _) => {
                if &datatype.name != &name_token.text() {
                    Err(name_token.error("you cannot add attributes to aliases"))
                } else {
                    Ok(&datatype)
                }
            }
            _ => Err(name_token.error("only data types can have attributes")),
        }
    }

    /// Adds a conditional block to the environment.
    /// Takes the condition, the range to associate with the condition, the first line of
    /// the conditional block, and finally the body itself.
    /// If this is an "else" block, we pass in the claim from the "if" part of the block.
    /// This way, if the claim is the same, we can simplify by combining them when externalized.
    /// Returns the last claim in the block, if we didn't have an if-claim to match against.
    pub fn add_conditional(
        &mut self,
        project: &mut Project,
        condition: AcornValue,
        range: Range,
        first_line: u32,
        last_line: u32,
        body: &Body,
        if_claim: Option<AcornValue>,
    ) -> compilation::Result<Option<AcornValue>> {
        if body.statements.is_empty() {
            // Conditional blocks with an empty body can just be ignored
            return Ok(None);
        }
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Conditional(&condition, range),
            first_line,
            last_line,
            Some(body),
        )?;
        let (outer_claim, claim_range) = block.externalize_last_claim(self, &body.right_brace)?;

        let matching_branches = if let Some(if_claim) = if_claim {
            if outer_claim == if_claim {
                true
            } else {
                false
            }
        } else {
            false
        };
        let (external_claim, last_claim) = if matching_branches {
            (outer_claim, None)
        } else {
            (
                AcornValue::Binary(
                    BinaryOp::Implies,
                    Box::new(condition),
                    Box::new(outer_claim.clone()),
                ),
                Some(outer_claim),
            )
        };
        let source = Source::anonymous(self.module_id, claim_range, self.depth);
        let prop = Proposition::monomorphic(external_claim, source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_line_types(
            LineType::Node(index),
            first_line,
            body.right_brace.line_number,
        );
        Ok(last_claim)
    }

    /// Get all facts that can be imported into other modules from this one.
    /// If the filter is provided, we only return facts whose qualified name is in the filter.
    /// In particular, if you want to import only a minimal set of facts, you have to
    /// provide an empty hash set as a filter.
    ///
    /// Extends and instance facts are always included regardless of filtering,
    /// as they represent structural type system information that's always needed.
    pub fn importable_facts(&self, filter: Option<&HashSet<String>>) -> Vec<Fact> {
        assert_eq!(self.depth, 0);
        let mut facts = vec![];
        for node in &self.nodes {
            if !node.importable() {
                continue;
            }
            if let Some(fact) = node.get_fact() {
                if fact.used_in_normalization() {
                    facts.push(fact);
                    continue;
                }

                // For other facts, apply the filter if provided
                if let Some(filter) = filter {
                    let name = node.source_name().expect("importable fact has no name");
                    if !filter.contains(&name) {
                        continue;
                    }
                }
                facts.push(fact);
            }
        }
        facts
    }

    /// Returns a NodeCursor for all nodes that correspond to a goal within this environment,
    /// or subenvironments, recursively.
    /// The order is "proving order", ie the goals inside the block are listed before the
    /// root goal of a block.
    pub fn iter_goals(&self) -> impl Iterator<Item = NodeCursor> {
        let mut answer = vec![];
        for i in 0..self.nodes.len() {
            let mut cursor = NodeCursor::new(self, i);
            cursor.find_goals(&mut answer);
        }
        answer.into_iter()
    }

    /// Used for integration testing.
    /// Not good for general use because it's based on the human-readable description.
    pub fn get_node_by_description(&self, description: &str) -> NodeCursor {
        let mut descriptions = Vec::new();
        for node in self.iter_goals() {
            let context = node.goal_context().unwrap();
            if context.description == description {
                return node;
            }
            descriptions.push(context.description);
        }

        panic!(
            "no context found for {} in:\n{}\n",
            description,
            descriptions.join("\n")
        );
    }

    /// Returns the path to a given zero-based line.
    /// This is a UI heuristic.
    /// Either returns a path to a proposition, or an error message explaining why this
    /// line is unusable.
    /// Error messages use one-based line numbers.
    pub fn path_for_line(&self, line: u32) -> Result<Vec<usize>, String> {
        let mut path = vec![];
        let mut block: Option<&Block> = None;
        let mut env = self;
        loop {
            match env.get_line_type(line) {
                Some(LineType::Node(i)) => {
                    path.push(i);
                    let node = &env.nodes[i];
                    if node.is_axiom() {
                        return Err(format!("line {} is an axiom", line + 1));
                    }
                    match node.get_block() {
                        Some(b) => {
                            block = Some(b);
                            env = &b.env;
                            continue;
                        }
                        None => {
                            return Ok(path);
                        }
                    }
                }
                Some(LineType::Opening) | Some(LineType::Closing) => match block {
                    Some(block) => {
                        if block.goal.is_none() {
                            return Err(format!("no claim for block at line {}", line + 1));
                        }
                        return Ok(path);
                    }
                    None => return Err(format!("brace but no block, line {}", line + 1)),
                },
                Some(LineType::Other) => return Err(format!("line {} is not a prop", line + 1)),
                None => return Err(format!("line {} is out of range", line + 1)),
                Some(LineType::Empty) => {
                    // We let the user insert a proof in an area by clicking on an empty
                    // line where the proof would go.
                    // To find the statement we're proving, we "slide" into the next prop.
                    let mut slide = line;
                    loop {
                        slide += 1;
                        match env.get_line_type(slide) {
                            Some(LineType::Node(i)) => {
                                let node = &env.nodes[i];
                                if node.is_axiom() {
                                    return Err(format!("slide to axiom, line {}", slide + 1));
                                }
                                if node.get_block().is_none() {
                                    path.push(i);
                                    return Ok(path);
                                }
                                // We can't slide into a block, because the proof would be
                                // inserted into the block, rather than here.
                                return Err(format!("blocked slide {} -> {}", line + 1, slide + 1));
                            }
                            Some(LineType::Empty) => {
                                // Keep sliding
                                continue;
                            }
                            Some(LineType::Closing) => {
                                // Sliding into the end of our block is okay
                                match block {
                                    Some(block) => {
                                        if block.goal.is_none() {
                                            return Err("slide to end but no claim".to_string());
                                        }
                                        return Ok(path);
                                    }
                                    None => {
                                        return Err(format!(
                                            "close brace but no block, line {}",
                                            slide + 1
                                        ))
                                    }
                                }
                            }
                            Some(LineType::Opening) => {
                                return Err(format!("slide to open brace, line {}", slide + 1));
                            }
                            Some(LineType::Other) => {
                                return Err(format!("slide to non-prop {}", slide + 1));
                            }
                            None => return Err(format!("slide to end, line {}", slide + 1)),
                        }
                    }
                }
            }
        }
    }

    pub fn covers_line(&self, line: u32) -> bool {
        if line < self.first_line {
            return false;
        }
        if line >= self.next_line() {
            return false;
        }
        true
    }

    /// Finds an environment one step deeper if there is one that covers the given line.
    fn env_for_line_step(&self, line: u32) -> Option<&Environment> {
        if let Some(LineType::Node(i)) = self.get_line_type(line) {
            if let Some(block) = self.nodes[i].get_block() {
                return Some(&block.env);
            }
        }
        None
    }

    /// Finds the narrowest environment that covers the given line.
    pub fn env_for_line(&self, line: u32) -> &Environment {
        match self.env_for_line_step(line) {
            Some(env) => env.env_for_line(line),
            None => self,
        }
    }
}

/// Methods used for integration testing.
impl Environment {
    /// Create a test version of the environment.
    pub fn test() -> Self {
        Environment::new(ModuleId(0))
    }

    /// Adds a possibly multi-line statement to the environment.
    /// Panics on failure.
    pub fn add(&mut self, input: &str) {
        let start_line = self.next_line();
        let tokens = Token::scan_with_start_line(input, start_line);

        if let Err(e) = self.add_tokens(&mut Project::new_mock(), tokens) {
            panic!("error in add_tokens: {}", e);
        }
    }

    /// Makes sure the lines are self-consistent
    pub fn check_lines(&self) {
        // Check that each proposition's block covers the lines it claims to cover
        for (line, line_type) in self.line_types.iter().enumerate() {
            if let LineType::Node(prop_index) = line_type {
                let node = &self.nodes[*prop_index];
                if let Some(block) = node.get_block() {
                    assert!(block.env.covers_line(line as u32));
                }
            }
        }

        // Recurse
        for node in &self.nodes {
            if let Some(block) = node.get_block() {
                block.env.check_lines();
            }
        }
    }

    /// Expects the given line to be bad
    pub fn bad(&mut self, input: &str) {
        let start_line = self.next_line();
        let tokens = Token::scan_with_start_line(input, start_line);
        let mut tokens = TokenIter::new(tokens);

        if let Ok((Some(statement), _)) = Statement::parse(&mut tokens, false) {
            assert!(
                self.add_statement(&mut Project::new_mock(), &statement)
                    .is_err(),
                "expected error in: {}",
                input
            );
        }
        // Clear the token map to prevent duplicate token insertion errors in subsequent tests
        self.token_map = TokenMap::new();
    }

    /// Check that the given name actually does have this type in the environment.
    pub fn expect_type(&mut self, name: &str, type_string: &str) {
        self.bindings.expect_type(name, type_string)
    }

    /// Check that the given name is defined to be this value
    pub fn expect_def(&mut self, name: &str, value_string: &str) {
        let name = DefinedName::unqualified(self.module_id, name);
        let env_value = match self.bindings.get_definition(&name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(env_value.to_string(), value_string);
    }

    /// Assert that these two names are defined to equal the same thing
    pub fn assert_def_eq(&self, name1: &str, name2: &str) {
        let name1 = DefinedName::unqualified(self.module_id, name1);
        let def1 = self.bindings.get_definition(&name1).unwrap();
        let name2 = DefinedName::unqualified(self.module_id, name2);
        let def2 = self.bindings.get_definition(&name2).unwrap();
        assert_eq!(def1, def2);
    }

    /// Assert that these two names are defined to be different things
    pub fn assert_def_ne(&self, name1: &str, name2: &str) {
        let name1 = DefinedName::unqualified(self.module_id, name1);
        let def1 = self.bindings.get_definition(&name1).unwrap();
        let name2 = DefinedName::unqualified(self.module_id, name2);
        let def2 = self.bindings.get_definition(&name2).unwrap();
        assert_ne!(def1, def2);
    }

    /// Get the bindings for the theorem block with the given name.
    pub fn get_bindings(&self, theorem_name: &str) -> &BindingMap {
        let mut cursor = self.get_node_by_description(theorem_name);
        cursor.descend(0);
        &cursor.env().bindings
    }

    /// Find the index of a block by its name.
    /// Uses the same logic as NodeCursor::block_name to determine the name.
    pub fn get_block_index(&self, block_name: &str) -> Option<usize> {
        self.nodes
            .iter()
            .position(|node| node.block_name() == block_name)
    }
}

/// Each line has a LineType, to handle line-based user interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LineType {
    /// Only used within subenvironments.
    /// The line relates to the block, but is outside the opening brace for this block.
    Opening,

    /// This line corresponds to a node inside the environment.
    /// The usize is an index into the nodes array.
    /// If the node represents a block, this line should also have a line type in the
    /// subenvironment within the block.
    Node(usize),

    /// Either only whitespace is here, or a comment.
    Empty,

    /// Lines with other sorts of statements besides prop statements.
    Other,

    /// Only used within subenvironments.
    /// The line has the closing brace for this block.
    Closing,
}
