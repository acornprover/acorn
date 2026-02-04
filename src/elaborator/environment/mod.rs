mod add_statement;

use std::collections::HashSet;
use std::sync::Arc;

use tower_lsp::lsp_types::Range;

use crate::elaborator::acorn_type::{AcornType, Datatype, TypeParam};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp};
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::block::{Block, BlockParams};
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::fact::Fact;
use crate::elaborator::names::DefinedName;
use crate::elaborator::node::{Node, NodeCursor};
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::module::ModuleId;
use crate::normalizer::{NormalizedFact, Normalizer};
use crate::project::Project;
use crate::syntax::statement::{Body, Statement};
use crate::syntax::token::{Token, TokenIter};
use crate::syntax::token_map::{TokenInfo, TokenKey, TokenMap};

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

    /// Whether a plain "false" is anywhere in this environment.
    /// This indicates that the environment is supposed to have contradictory facts.
    pub includes_explicit_false: bool,

    /// Whether this block WILL include an explicit "false" claim (set by look-ahead).
    /// This is separate from `includes_explicit_false` because we need to know about
    /// upcoming `false` claims before we process them, so that intermediate claims
    /// can correctly have `inconsistency_okay = true`.
    pub will_include_explicit_false: bool,

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

    /// Stores the normalizer state after processing imports.
    /// This can be cloned to create a Processor without re-normalizing imports.
    pub import_normalizer: Option<Normalizer>,

    /// Stores normalized facts from imports.
    pub normalized_imports: Vec<NormalizedFact>,

    /// Stores the normalizer state after processing all facts.
    pub normalizer: Option<Normalizer>,

    /// Stores normalized facts from this module's nodes.
    pub normalized_module_facts: Vec<NormalizedFact>,
}

impl Environment {
    pub fn new(module_id: ModuleId) -> Self {
        Environment {
            module_id,
            bindings: BindingMap::new(module_id),
            nodes: Vec::new(),
            includes_explicit_false: false,
            will_include_explicit_false: false,
            first_line: 0,
            line_types: Vec::new(),
            implicit: false,
            depth: 0,
            token_map: TokenMap::new(),
            doc_comments: Vec::new(),
            module_doc_comments: Vec::new(),
            at_module_beginning: true,
            last_statement_line: None,
            import_normalizer: None,
            normalized_imports: Vec::new(),
            normalizer: None,
            normalized_module_facts: Vec::new(),
        }
    }

    /// Create a child environment.
    pub fn create_child(&self, first_line: u32, implicit: bool) -> Self {
        Environment {
            module_id: self.module_id,
            bindings: self.bindings.clone(),
            nodes: Vec::new(),
            includes_explicit_false: false,
            will_include_explicit_false: false,
            first_line,
            line_types: Vec::new(),
            implicit,
            depth: self.depth + 1,
            token_map: TokenMap::new(),
            doc_comments: Vec::new(),
            module_doc_comments: Vec::new(), // Child environments don't inherit module doc comments
            at_module_beginning: false,      // Child environments are never at module beginning
            last_statement_line: None,
            import_normalizer: None,
            normalized_imports: Vec::new(),
            normalizer: None,
            normalized_module_facts: Vec::new(),
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
    /// This can overwrite existing `Other` or `Empty` lines.
    pub fn add_node_lines(&mut self, index: usize, range: &Range) {
        let first = range.start.line;
        let last = range.end.line;
        let node_type = LineType::Node(index);

        // First, ensure we have enough entries
        while self.next_line() <= last {
            self.line_types.push(LineType::Empty);
        }

        // Then update the lines in range
        for line in first..=last {
            if line >= self.first_line {
                let idx = (line - self.first_line) as usize;
                if idx < self.line_types.len() {
                    // Node can overwrite Other or Empty
                    match self.line_types[idx] {
                        LineType::Other | LineType::Empty => {
                            self.line_types[idx] = node_type;
                        }
                        LineType::Node(_) | LineType::Opening | LineType::Closing => {
                            // Don't overwrite existing Node/Opening/Closing assignments
                        }
                    }
                }
            }
        }
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
        let index = self.nodes.len() - 1;
        index
    }

    /// Returns an evaluator that modifies the token map.
    pub fn evaluator<'a>(&'a mut self, project: &'a Project) -> Evaluator<'a> {
        Evaluator::new(project, &self.bindings, Some(&mut self.token_map))
    }

    /// Adds a node to represent the definition of the provided
    /// constant.
    pub fn add_definition(&mut self, defined_name: &DefinedName) {
        // This constant can be generic, with type variables in it.
        let potential = self
            .bindings
            .get_constant_value(defined_name)
            .expect("bad add_definition call");
        let range = self
            .bindings
            .get_definition_range(defined_name)
            .unwrap()
            .clone();
        let name = defined_name.to_string();
        let source = Source::constant_definition(
            self.module_id,
            range.clone(),
            self.depth,
            Arc::new(potential.clone().to_generic_value()),
            &name,
        );

        // For axiom constants (no definition), create a tautological definition (c = c)
        // This ensures the constant is registered in the symbol table as an inhabitant of its type.
        let definition = match self.bindings.get_definition(defined_name) {
            Some(def) => def.clone(),
            None => potential.clone().to_generic_value(),
        };

        let index = self.add_node(Node::definition(potential, definition, source));
        // Only set line types for top-level definitions. Definitions inside blocks
        // (depth > 0) have their line types managed by the parent block.
        if self.depth == 0 {
            self.add_node_lines(index, &range);
        }
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
    ) -> error::Result<&'a Datatype> {
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

    /// Checks that new specific attributes don't conflict with existing generic attributes.
    pub fn check_no_conflicting_attributes(
        &self,
        datatype: &Datatype,
        body: &crate::syntax::statement::Body,
    ) -> error::Result<()> {
        use crate::syntax::statement::StatementInfo;

        // Check if any of the new specific attributes conflict with existing generic ones
        for stmt in &body.statements {
            let attr_name = match &stmt.statement {
                StatementInfo::Let(ls) => Some(ls.name_token.text()),
                StatementInfo::Define(ds) => Some(ds.name_token.text()),
                _ => None,
            };

            if let Some(name) = attr_name {
                // Check if a generic attribute with this name already exists
                if self.bindings.has_type_attr(datatype, name) {
                    return Err(stmt.error(&format!(
                        "attribute '{}' conflicts with existing generic attribute on {}",
                        name, datatype.name
                    )));
                }
            }
        }

        Ok(())
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
        first_token: &Token,
        last_token: &Token,
        body: &Body,
        if_claim: Option<AcornValue>,
    ) -> error::Result<Option<AcornValue>> {
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
            first_token,
            last_token,
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
        let prop = Proposition::new(external_claim, vec![], source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_line_types(
            LineType::Node(index),
            first_token.line_number,
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
    pub fn iter_goals(&self) -> impl Iterator<Item = NodeCursor<'_>> {
        let mut answer = vec![];
        for i in 0..self.nodes.len() {
            let mut cursor = NodeCursor::new(self, i);
            cursor.find_goals(&mut answer);
        }
        answer.into_iter()
    }

    /// Used for integration testing.
    pub fn get_node_by_goal_name(&self, name: &str) -> NodeCursor<'_> {
        let mut names = Vec::new();
        for node in self.iter_goals() {
            let context = node.goal().unwrap();
            if context.name == name {
                return node;
            }
            names.push(context.name.clone());
        }

        panic!("no context found for {} in:\n{}\n", name, names.join("\n"));
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
                        // Check if the block has any block-level goal nodes
                        let has_block_goals = block
                            .env
                            .nodes
                            .iter()
                            .any(|node| node.is_block_level_goal());
                        if !has_block_goals {
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
                                        // Check if the block has any block-level goal nodes
                                        let has_block_goals = block
                                            .env
                                            .nodes
                                            .iter()
                                            .any(|node| node.is_block_level_goal());
                                        if !has_block_goals {
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

    /// Helper to collect all transitive dependencies for this environment.
    /// Used by prenormalize since the module isn't in the project yet.
    fn collect_dependencies(
        &self,
        project: &Project,
        seen: &mut std::collections::HashSet<crate::module::ModuleId>,
        output: &mut Vec<crate::module::ModuleId>,
    ) {
        for dep_id in self.bindings.direct_dependencies() {
            if !seen.insert(dep_id) {
                continue;
            }
            // Recursively collect dependencies of this dependency
            if let Some(dep_env) = project.get_env_by_id(dep_id) {
                dep_env.collect_dependencies(project, seen, output);
            }
            output.push(dep_id);
        }
    }

    /// Populates the prenormalized fields by processing all facts.
    /// This should be called after elaboration is complete.
    ///
    /// For dependencies that have already been prenormalized, we merge their
    /// normalizer state and reuse their pre-normalized facts, avoiding redundant
    /// normalization work.
    ///
    /// Returns Ok(()) if all facts normalized successfully, or Err if any failed.
    /// Even on error, the normalizer states are set to what was achieved before the error.
    pub fn prenormalize(&mut self, project: &Project) -> Result<(), String> {
        use std::collections::HashSet;

        let mut normalizer = Normalizer::new();
        let mut first_error: Option<String> = None;

        // Collect all dependencies (including transitive) using the environment's bindings.
        // We can't use project.all_dependencies() because this module isn't in the project yet.
        let mut deps = Vec::new();
        let mut seen = HashSet::new();
        self.collect_dependencies(project, &mut seen, &mut deps);

        // Add imported facts from dependencies.
        // If a dependency has prenormalized state, merge it and reuse the pre-normalized facts.
        // Otherwise, fall back to normalizing (shouldn't happen in practice).
        //
        // Important: we only copy normalized_module_facts (the dependency's own facts),
        // not normalized_imports. The transitive imports are handled by processing
        // dependencies in topological order - each dependency's own facts are added
        // when we process that dependency directly.
        for dep_id in deps {
            if let Some(dep_env) = project.get_env_by_id(dep_id) {
                if let Some(ref dep_normalizer) = dep_env.normalizer {
                    // Dependency has prenormalized state - merge and reuse
                    normalizer.merge_imports(dep_normalizer);
                    // Add only the dependency's own facts (not its imports)
                    for normalized in &dep_env.normalized_module_facts {
                        self.normalized_imports.push(normalized.clone());
                    }
                } else {
                    // This should never happen - dependencies are processed first
                    panic!("Dependency {} not prenormalized", dep_id.0);
                }
            }
        }

        // Store the normalizer state after processing imports.
        // This can be cloned by Processor::with_imports to avoid re-normalizing.
        self.import_normalizer = Some(normalizer.clone());

        // Normalize top-level facts for backwards compatibility and for goal normalization.
        // Due to Rc::make_mut cloning behavior in verification, only top-level facts
        // (added in verify_module's loop) are visible - internal facts from blocks
        // are added to cloned processors that get dropped.
        for node in &self.nodes {
            if let Some(fact) = node.get_fact() {
                match normalizer.normalize_fact(&fact) {
                    Ok(normalized) => self.normalized_module_facts.push(normalized),
                    Err(e) => {
                        if first_error.is_none() {
                            first_error = Some(e.message);
                        }
                    }
                }
            }
        }

        // Now normalize goals. For each goal, we compute the normalizer state that matches
        // what verification sees. This iterates through nodes in order, adding facts to
        // the normalizer as we go (mirroring verify_node behavior).
        let import_normalizer = self.import_normalizer.clone().unwrap();
        Self::prenormalize_goals(&mut self.nodes, &import_normalizer, &mut first_error);

        self.normalizer = Some(normalizer);
        match first_error {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    /// Recursively normalizes goals in nodes, computing the correct normalizer state for each.
    ///
    /// The normalizer state for a goal depends on:
    /// 1. Import facts (from base_normalizer)
    /// 2. Facts from nodes processed BEFORE the goal in the current traversal
    ///
    /// At the top level, verify_module's loop adds facts after each node is verified.
    /// Inside a block, verify_node's loop adds facts after each child is verified.
    /// The Rc::make_mut behavior means facts added inside a block stay inside that block's
    /// cloned processor, visible to later siblings but not to the parent.
    ///
    /// This function mirrors that behavior: we iterate through nodes in order, adding facts
    /// to the normalizer as we go. When recursing into a block, we clone the current
    /// normalizer and process the block's nodes independently.
    fn prenormalize_goals(
        nodes: &mut [Node],
        base_normalizer: &Normalizer,
        first_error: &mut Option<String>,
    ) {
        // Clone the normalizer to track state as we process nodes.
        // We need to track state for this level only.
        let mut current_normalizer = base_normalizer.clone();

        for node in nodes.iter_mut() {
            match node {
                Node::Structural(fact, normalized_fact_slot) => {
                    // Normalize the fact and store it
                    match current_normalizer.normalize_fact(fact) {
                        Ok(normalized) => {
                            *normalized_fact_slot = Some(normalized);
                        }
                        Err(e) => {
                            if first_error.is_none() {
                                *first_error = Some(e.message);
                            }
                        }
                    }
                }
                Node::Claim(goal, fact, normalized_goal_slot, normalized_fact_slot) => {
                    // Runtime order: verify_goal (which calls set_goal) runs BEFORE add_fact.
                    // So we normalize the goal FIRST, then add the fact for subsequent nodes.

                    // Normalize the goal on a CLONE of current_normalizer (without the claim's fact).
                    // This captures the state that would exist after set_goal is called.
                    // The NormalizedGoal.normalizer will include the negated goal.
                    let mut goal_normalizer = current_normalizer.clone();
                    match goal_normalizer.normalize_goal(goal) {
                        Ok(normalized) => {
                            *normalized_goal_slot = Some(normalized);
                        }
                        Err(e) => {
                            if first_error.is_none() {
                                *first_error = Some(e.message);
                            }
                        }
                    }

                    // AFTER goal verification, add the claim's fact to current_normalizer.
                    // This matches runtime: add_fact is called after verify_node returns.
                    match current_normalizer.normalize_fact(fact) {
                        Ok(normalized) => {
                            *normalized_fact_slot = Some(normalized);
                        }
                        Err(e) => {
                            if first_error.is_none() {
                                *first_error = Some(e.message);
                            }
                        }
                    }
                }
                Node::Block(block, external_fact, normalized_fact_slot) => {
                    // Recurse into the block's nodes with current normalizer state.
                    // This mirrors how verify_node clones the processor when entering a block.
                    Self::prenormalize_goals(
                        &mut block.env.nodes,
                        &current_normalizer,
                        first_error,
                    );
                    // After the block, add the external fact (if any) for subsequent nodes
                    if let Some(fact) = external_fact {
                        match current_normalizer.normalize_fact(fact) {
                            Ok(normalized) => {
                                *normalized_fact_slot = Some(normalized);
                            }
                            Err(e) => {
                                if first_error.is_none() {
                                    *first_error = Some(e.message);
                                }
                            }
                        }
                    }
                }
            }
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

        if let Err(e) = self.add_tokens(&mut Project::new_mock(), tokens, false) {
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

    /// Expects the given line to be bad and returns the error message
    pub fn bad(&mut self, input: &str) -> String {
        let start_line = self.next_line();
        let tokens = Token::scan_with_start_line(input, start_line);
        let mut tokens = TokenIter::new(tokens);

        match Statement::parse(&mut tokens, false, false) {
            Ok((Some(statement), _)) => {
                match self.add_statement(&mut Project::new_mock(), &statement) {
                    Err(e) => {
                        // Clear the token map to prevent duplicate token insertion errors in subsequent tests
                        self.token_map = TokenMap::new();
                        return e.to_string();
                    }
                    Ok(_) => {
                        panic!("expected error in: {}", input);
                    }
                }
            }
            Ok((None, _)) => {
                return "failed to parse (no statement)".to_string();
            }
            Err(e) => {
                return format!("parse error: {}", e);
            }
        }
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
        let cursor = self.get_node_by_goal_name(theorem_name);
        // The cursor is now pointing to a goal node. The bindings we want are from
        // the environment that contains this goal node.
        &cursor.env().bindings
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
