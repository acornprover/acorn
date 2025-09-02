use tower_lsp::lsp_types::Range;

use crate::acorn_type::{AcornType, Datatype, TypeParam, Typeclass};
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::binding_map::ConstructorInfo;
use crate::block::{Block, BlockParams, Node};
use crate::compilation::{self, Error, ErrorSource};
use crate::evaluator::Evaluator;
use crate::expression::{Declaration, Expression};
use crate::fact::Fact;
use crate::named_entity::NamedEntity;
use crate::names::{ConstantName, DefinedName};
use crate::potential_value::PotentialValue;
use crate::project::{ImportError, Project};
use crate::proposition::Proposition;
use crate::source::{Source, SourceType};
use crate::stack::Stack;
use crate::statement::{
    AttributesStatement, Body, ClaimStatement, DefineStatement, ForAllStatement,
    FunctionSatisfyStatement, IfStatement, ImportStatement, InductiveStatement, InstanceStatement,
    LetStatement, MatchStatement, NumeralsStatement, SolveStatement, Statement, StatementInfo,
    StructureStatement, TheoremStatement, TodoStatement, TypeStatement, TypeclassStatement,
    VariableSatisfyStatement,
};
use crate::token::{Token, TokenIter, TokenType};
use crate::type_unifier::TypeclassRegistry;

use super::{Environment, LineType};

// This file generally contains the logic for creating an environment.
// It would be nice for the separation to be cleaner.

impl Environment {
    /// Adds a "let" statement to the environment.
    /// This can also be in a class, typeclass, or instance block.
    /// If this is in an attributes block, the datatype parameters are provided.

    /// Adds a "define" statement to the environment, that may be within an attributes block.
    ///
    /// The self type is the type of the "self" variable. If it's None, there can't be a self.
    ///
    /// The datatype params are the parameters for the overall attributes statement, if we are within one.
    /// They will become the parameters of the newly defined function.

    /// Parse these tokens and add them to the environment.
    /// If project is not provided, we won't be able to handle import statements.
    pub fn add_tokens(
        &mut self,
        project: &mut Project,
        tokens: Vec<Token>,
    ) -> compilation::Result<()> {
        let mut tokens = TokenIter::new(tokens);
        loop {
            match Statement::parse(&mut tokens, false) {
                Ok((Some(statement), _)) => {
                    if let Err(e) = self.add_statement(project, &statement) {
                        return Err(e);
                    }
                }
                Ok((None, _)) => return Ok(()),
                Err(e) => return Err(e),
            }
        }
    }

    /// Adds a statement to the environment.
    /// If the statement has a body, this call creates a sub-environment and adds the body
    /// to that sub-environment.
    pub fn add_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
    ) -> compilation::Result<()> {
        if self.includes_explicit_false {
            return Err(
                statement.error("an explicit 'false' may not be followed by other statements")
            );
        }

        // Handle module doc collection logic before processing the statement
        if !matches!(&statement.statement, StatementInfo::DocComment(_)) {
            let current_line = statement.first_line();

            // Check if this is the first non-doc statement and there was a gap
            if self.at_module_beginning {
                if let Some(last_line) = self.last_statement_line {
                    if current_line > last_line + 1 {
                        // There was a gap between last doc comment and this statement
                        // Move accumulated doc comments to module documentation
                        self.module_doc_comments.extend(self.doc_comments.drain(..));
                    }
                }
                self.at_module_beginning = false;
            }
        }

        let result = match &statement.statement {
            StatementInfo::Type(ts) => self.add_type_statement(project, statement, ts),

            StatementInfo::Let(ls) => {
                self.add_other_lines(statement);
                self.add_let_statement(
                    project,
                    statement,
                    DefinedName::unqualified(self.module_id, ls.name_token.text()),
                    ls,
                    ls.name_token.range(),
                    None,
                )
            }

            StatementInfo::Define(ds) => {
                self.add_other_lines(statement);
                self.add_define_statement(
                    project,
                    statement,
                    DefinedName::unqualified(self.module_id, ds.name_token.text()),
                    None,
                    None,
                    ds,
                    ds.name_token.range(),
                )
            }

            StatementInfo::Theorem(ts) => self.add_theorem_statement(project, statement, ts),

            StatementInfo::Claim(cs) => self.add_claim_statement(project, statement, cs),

            StatementInfo::ForAll(fas) => self.add_forall_statement(project, statement, fas),

            StatementInfo::If(is) => self.add_if_statement(project, statement, is),

            StatementInfo::VariableSatisfy(vss) => {
                self.add_variable_satisfy_statement(project, statement, vss)
            }

            StatementInfo::FunctionSatisfy(fss) => {
                self.add_function_satisfy_statement(project, statement, fss)
            }

            StatementInfo::Structure(ss) => self.add_structure_statement(project, statement, ss),

            StatementInfo::Inductive(is) => self.add_inductive_statement(project, statement, is),

            StatementInfo::Import(is) => self.add_import_statement(project, statement, is),

            StatementInfo::Attributes(ats) => {
                self.add_attributes_statement(project, statement, ats)
            }

            StatementInfo::Numerals(ds) => self.add_numerals_statement(project, statement, ds),

            StatementInfo::Solve(ss) => self.add_solve_statement(project, statement, ss),

            StatementInfo::Problem(body) => self.add_problem_statement(project, statement, body),

            StatementInfo::Match(ms) => self.add_match_statement(project, statement, ms),

            StatementInfo::Typeclass(ts) => self.add_typeclass_statement(project, statement, ts),

            StatementInfo::Instance(is) => self.add_instance_statement(project, statement, is),

            StatementInfo::Todo(ts) => self.add_todo_statement(project, statement, ts),

            StatementInfo::DocComment(s) => {
                let current_line = statement.first_line();

                // Check if there's a gap before this doc comment
                if self.at_module_beginning {
                    if let Some(last_line) = self.last_statement_line {
                        if current_line > last_line + 1 {
                            // There was a gap before this doc comment
                            // Move any accumulated doc comments to module documentation
                            self.module_doc_comments.extend(self.doc_comments.drain(..));
                            self.at_module_beginning = false;
                        }
                    }
                }

                self.doc_comments.push(s.clone());
                self.last_statement_line = Some(current_line);
                Ok(())
            }
        };

        // Clear doc comments after any non-doc-comment statement
        if !matches!(&statement.statement, StatementInfo::DocComment(_)) {
            self.doc_comments.clear();
            self.last_statement_line = Some(statement.first_line());
        }

        result
    }

    /// Adds a "let" statement to the environment.
    /// This can also be in a class, typeclass, or instance block.
    /// If this is in an attributes block, the datatype parameters are provided.
    fn add_let_statement(
        &mut self,
        project: &Project,
        statement: &Statement,
        defined_name: DefinedName,
        ls: &LetStatement,
        range: Range,
        datatype_params: Option<&Vec<TypeParam>>,
    ) -> compilation::Result<()> {
        ls.name_token.check_not_reserved()?;

        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(ls.name_token.error(&format!(
                "constant name '{}' already defined in this scope",
                &defined_name
            )));
        }

        if self.depth > 0 && !ls.type_params.is_empty() {
            return Err(ls
                .name_token
                .error("parametrized constants may only be defined at the top level"));
        }

        let local_type_params = self
            .evaluator(project)
            .evaluate_type_params(&ls.type_params)?;
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let (acorn_type, value) = match &ls.type_expr {
            Some(type_expr) => {
                // Traditional let with explicit type: let name: Type = value
                let acorn_type = self.evaluator(project).evaluate_type(type_expr)?;
                if ls.name_token.token_type == TokenType::Numeral {
                    // Check if this is a datatype attribute or instance definition
                    match &defined_name {
                        DefinedName::Constant(constant_name) => {
                            // Regular datatype attribute
                            let datatype_name = match constant_name.as_attribute() {
                                Some((_, datatype_name, _)) => datatype_name.to_string(),
                                _ => {
                                    return Err(ls
                                        .name_token
                                        .error("numeric literals must be datatype members"))
                                }
                            };
                            let datatype = Datatype {
                                module_id: self.module_id,
                                name: datatype_name,
                            };
                            if acorn_type != AcornType::Data(datatype, vec![]) {
                                return Err(type_expr.error(
                                    "numeric datatype variables must be the datatype type",
                                ));
                            }
                        }
                        DefinedName::Instance(instance_name) => {
                            // Instance definition - check against the instance datatype
                            if acorn_type != AcornType::Data(instance_name.datatype.clone(), vec![])
                            {
                                return Err(type_expr.error(
                                    "numeric instance variables must be the instance datatype type",
                                ));
                            }
                        }
                    }
                }
                let value = if ls.value.is_axiom() {
                    None
                } else {
                    let v = self
                        .evaluator(project)
                        .evaluate_value(&ls.value, Some(&acorn_type))?;
                    Some(v)
                };
                (acorn_type, value)
            }
            None => {
                // Type inference, let name = value
                if ls.value.is_axiom() {
                    return Err(ls
                        .value
                        .first_token()
                        .error("axiom constants require explicit type annotation"));
                }
                // Evaluate the value first to infer its type
                let value = self.evaluator(project).evaluate_value(&ls.value, None)?;
                let acorn_type = value.get_type();
                (acorn_type, Some(value))
            }
        };

        // Reset the bindings
        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        // Genericize the value being defined
        let type_params = match datatype_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(ls
                        .name_token
                        .error("datatype parameters and let parameters cannot be used together"));
                }
                p.clone()
            }
            None => local_type_params,
        };
        let acorn_type = acorn_type.genericize(&type_params);
        let value = value.map(|v| v.genericize(&type_params));
        let def_str = statement.to_string();

        // Check for aliasing
        if let Some(value) = &value {
            if let Some(simple_name) = value.as_simple_constant() {
                match &defined_name {
                    // For local names, 'let x = y' should create an alias for y, not a new constant.
                    // Aliases for local names are handled in the binding map.
                    DefinedName::Constant(constant_name) => {
                        self.bindings.add_constant_alias(
                            constant_name.clone(),
                            simple_name.clone(),
                            PotentialValue::Resolved(value.clone()),
                            Some(def_str),
                        );
                        return Ok(());
                    }
                    // Aliases for instance names are handled in normalization.
                    // Just do nothing here.
                    DefinedName::Instance(_) => {}
                }
            }
        }
        self.define_constant(
            defined_name,
            type_params,
            acorn_type,
            value,
            range,
            Some(def_str),
        );
        Ok(())
    }

    fn add_define_statement(
        &mut self,
        project: &Project,
        statement: &Statement,
        defined_name: DefinedName,
        self_type: Option<&AcornType>,
        datatype_params: Option<&Vec<TypeParam>>,
        ds: &DefineStatement,
        range: Range,
    ) -> compilation::Result<()> {
        ds.name_token.check_not_reserved()?;
        if self.depth > 0 && !ds.type_params.is_empty() {
            return Err(ds
                .name_token
                .error("parametrized functions may only be defined at the top level"));
        }
        if self_type.is_some() && !ds.type_params.is_empty() {
            return Err(ds
                .name_token
                .error("member functions may not have type parameters"));
        }
        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(ds.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                defined_name
            )));
        }

        // Calculate the function value
        let (fn_param_names, _, arg_types, unbound_value, value_type) =
            self.bindings.evaluate_scoped_value(
                &ds.type_params,
                &ds.args,
                Some(&ds.return_type),
                &ds.return_value,
                self_type,
                defined_name.as_constant(),
                project,
                Some(&mut self.token_map),
            )?;

        if let Some(datatype_type) = self_type {
            if &arg_types[0] != datatype_type {
                return Err(ds.args[0].token().error("self must be the datatype type"));
            }

            if ds.name_token.text() == "read" {
                if arg_types.len() != 2
                    || &arg_types[1] != datatype_type
                    || &value_type != datatype_type
                {
                    return Err(ds.name_token.error(&format!(
                        "{}.read should be type ({}, {}) -> {}",
                        datatype_type, datatype_type, datatype_type, datatype_type
                    )));
                }
            }
        }

        // The typical definition case
        if let Some(v) = unbound_value {
            let mut fn_value = AcornValue::lambda(arg_types, v);

            let params = if let Some(datatype_params) = datatype_params {
                // When a datatype is parametrized, the member gets parameters from the datatype.
                fn_value = fn_value.genericize(&datatype_params);
                datatype_params.clone()
            } else {
                // When there's no datatype, we just have the function's own type parameters.
                fn_param_names
            };

            // Add the function value to the environment
            self.define_constant(
                defined_name,
                params,
                fn_value.get_type(),
                Some(fn_value),
                range,
                Some(statement.to_string()),
            );
            return Ok(());
        }

        // Defining an axiom
        let new_axiom_type = AcornType::functional(arg_types, value_type);
        self.define_constant(
            defined_name,
            fn_param_names,
            new_axiom_type,
            None,
            range,
            Some(statement.to_string()),
        );
        Ok(())
    }

    fn add_theorem_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TheoremStatement,
    ) -> compilation::Result<()> {
        // Figure out the range for this theorem definition.
        // It's smaller than the whole theorem statement because it doesn't
        // include the proof block.
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ts.claim_right_brace.end_pos(),
        };

        if let Some(name_token) = &ts.name_token {
            self.bindings
                .check_unqualified_name_available(name_token.text(), &statement.first_token)?;
        }

        let (type_params, arg_names, arg_types, value, _) = self.bindings.evaluate_scoped_value(
            &ts.type_params,
            &ts.args,
            None,
            &ts.claim,
            None,
            None,
            project,
            Some(&mut self.token_map),
        )?;

        let unbound_claim = value.ok_or_else(|| ts.claim.error("theorems must have values"))?;
        unbound_claim.check_type(Some(&AcornType::Bool), &ts.claim)?;

        let is_citation = self.bindings.is_citation(&unbound_claim, project);
        if is_citation && ts.body.is_some() {
            return Err(statement.error("citations do not need proof blocks"));
        }

        let mut block_args = vec![];
        for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
            block_args.push((arg_name.clone(), arg_type.clone()));
        }

        // Externally we use the theorem in unnamed, "forall" form
        let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone());
        if let Err(message) = external_claim.validate() {
            return Err(ts.claim.error(&message));
        }

        let duplicate;

        if self.theorems.contains(&external_claim) {
            duplicate = true;
        }else {
            duplicate = false;
            self.theorems.insert(external_claim.clone());
        }

        let (premise, goal) = match &unbound_claim {
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                let premise_range = match ts.claim.premise() {
                    Some(p) => p.range(),
                    None => {
                        // I don't think this should happen, but it's awkward for the
                        // compiler to enforce, so pick a not-too-wrong default.
                        ts.claim.range()
                    }
                };
                (
                    Some((left.to_arbitrary(), premise_range)),
                    right.to_arbitrary(),
                )
            }
            c => (None, c.to_arbitrary()),
        };

        // We define the theorem using "lambda" form.
        // The definition happens here, in the outside environment, because the
        // theorem is usable by name in this environment.
        let lambda_claim = AcornValue::lambda(arg_types, unbound_claim);
        let theorem_type = lambda_claim.get_type();
        if let Some(name_token) = &ts.name_token {
            let doc_comments = self.take_doc_comments();
            // Use the name token range
            let name_range = name_token.range();
            self.bindings.add_unqualified_constant(
                name_token.text(),
                type_params.clone(),
                theorem_type.clone(),
                Some(lambda_claim.clone()),
                None,
                doc_comments,
                Some(name_range),
                statement.to_string(),
            );
        }

        let already_proven = ts.axiomatic || is_citation;
        let source = Source::theorem(
            already_proven,
            self.module_id,
            range,
            true,
            self.depth,
            ts.name_token.as_ref().map(|t| t.text().to_string()),
        );
        let prop = Proposition::new(external_claim, type_params.clone(), source);

        let node = if already_proven {
            Node::structural(project, self, prop)
        } else {
            let block = Block::new(
                project,
                &self,
                type_params,
                block_args,
                BlockParams::Theorem(
                    ts.name_token.as_ref().map(|t| t.text()),
                    range,
                    premise,
                    goal,
                    duplicate
                ),
                statement.first_line(),
                statement.last_line(),
                ts.body.as_ref(),
            )?;
            Node::block(project, self, block, Some(prop))
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        if let Some(name_token) = &ts.name_token {
            let name = ConstantName::unqualified(self.module_id, name_token.text());
            self.bindings.mark_as_theorem(&name);
        }

        Ok(())
    }

    fn add_variable_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        vss: &VariableSatisfyStatement,
    ) -> compilation::Result<()> {
        // First, evaluate the type expressions with token tracking
        for declaration in &vss.declarations {
            if let Declaration::Typed(_, type_expr) = declaration {
                self.evaluator(project).evaluate_type(type_expr)?;
            }
        }

        // We need to prove the general existence claim
        let mut stack = Stack::new();
        let mut no_token_evaluator = Evaluator::new(project, &self.bindings, None);
        let (quant_names, quant_types) =
            no_token_evaluator.bind_args(&mut stack, &vss.declarations, None)?;
        let general_claim_value = no_token_evaluator.evaluate_value_with_stack(
            &mut stack,
            &vss.condition,
            Some(&AcornType::Bool),
        )?;
        let general_claim = AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let general_prop = Proposition::monomorphic(general_claim, source);
        let index = self.add_node(Node::claim(project, self, general_prop));
        self.add_node_lines(index, &statement.range());

        // Define the quantifiers as constants
        for (quant_name, quant_type) in quant_names.iter().zip(quant_types.iter()) {
            let def_str = format!("{}: {}", quant_name, quant_type);
            self.bindings.add_unqualified_constant(
                quant_name,
                vec![],
                quant_type.clone(),
                None,
                None,
                vec![],
                None,
                def_str,
            );
        }

        // We can then assume the specific existence claim with the named constants
        let specific_claim = self
            .evaluator(project)
            .evaluate_value(&vss.condition, Some(&AcornType::Bool))?;
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let specific_prop = Proposition::monomorphic(specific_claim, source);
        self.add_node(Node::structural(project, self, specific_prop));

        Ok(())
    }

    fn add_function_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fss: &FunctionSatisfyStatement,
    ) -> compilation::Result<()> {
        fss.name_token.check_not_reserved()?;
        self.bindings
            .check_unqualified_name_available(fss.name_token.text(), statement)?;

        // Figure out the range for this function definition.
        // It's smaller than the whole function statement because it doesn't
        // include the proof block.
        let definition_range = Range {
            start: statement.first_token.start_pos(),
            end: fss.satisfy_token.end_pos(),
        };

        let (_, mut arg_names, mut arg_types, condition, _) = self.bindings.evaluate_scoped_value(
            &[],
            &fss.declarations,
            None,
            &fss.condition,
            None,
            None,
            project,
            Some(&mut self.token_map),
        )?;

        let unbound_condition = condition.ok_or_else(|| statement.error("missing condition"))?;
        if unbound_condition.get_type() != AcornType::Bool {
            return Err(fss.condition.error("condition must be a boolean"));
        }

        // The return variable shouldn't become a block arg, because we're trying to
        // prove its existence.
        let _return_name = arg_names.pop().unwrap();
        let return_type = arg_types.pop().unwrap();
        let block_args: Vec<_> = arg_names
            .iter()
            .cloned()
            .zip(arg_types.iter().cloned())
            .collect();
        let num_args = block_args.len() as AtomId;

        let block = Block::new(
            project,
            &self,
            vec![],
            block_args,
            BlockParams::FunctionSatisfy(
                unbound_condition.clone(),
                return_type.clone(),
                fss.condition.range(),
            ),
            statement.first_line(),
            statement.last_line(),
            fss.body.as_ref(),
        )?;

        // We define this function not with an equality, but via the condition.
        let function_type = AcornType::functional(arg_types.clone(), return_type);
        let doc_comments = self.take_doc_comments();
        self.bindings.add_unqualified_constant(
            fss.name_token.text(),
            vec![],
            function_type.clone(),
            None,
            None,
            doc_comments,
            Some(fss.name_token.range()),
            statement.to_string(),
        );
        let const_name = ConstantName::unqualified(self.module_id, fss.name_token.text());
        let function_constant = AcornValue::constant(const_name, vec![], function_type);
        let function_term = AcornValue::apply(
            function_constant.clone(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| AcornValue::Variable(i as AtomId, t.clone()))
                .collect(),
        );
        let return_bound = unbound_condition.bind_values(num_args, num_args, &[function_term]);
        let external_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

        let source = Source::constant_definition(
            self.module_id,
            definition_range,
            self.depth,
            function_constant,
            fss.name_token.text(),
        );
        let prop = Proposition::monomorphic(external_condition, source);

        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    fn add_structure_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ss: &StructureStatement,
    ) -> compilation::Result<()> {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            ss.first_right_brace.line_number,
        );
        self.bindings
            .check_typename_available(ss.name_token.text(), statement)?;

        let mut arbitrary_params = vec![];
        let type_params = self
            .evaluator(project)
            .evaluate_type_params(&ss.type_params)?;
        for type_param in &type_params {
            // Internally to the structure definition, the type parameters are
            // treated as arbitrary types.
            arbitrary_params.push(self.bindings.add_arbitrary_type(type_param.clone()));
        }

        // Parse the fields before adding the struct type so that we can't have
        // self-referential structs.
        let mut member_fn_names = vec![];
        let mut field_types = vec![];
        let mut field_doc_comments = vec![];
        for (field_name_token, field_type_expr, doc_comments) in &ss.fields {
            let field_type = self.evaluator(project).evaluate_type(&field_type_expr)?;
            field_types.push(field_type.clone());
            if TokenType::is_magic_method_name(&field_name_token.text()) {
                return Err(field_name_token.error(&format!(
                    "'{}' is a reserved word. use a different name",
                    field_name_token.text()
                )));
            }
            member_fn_names.push(field_name_token.text());
            field_doc_comments.push(doc_comments.clone());
        }

        // If there's a constraint, add a block to prove it can be satisfied.
        // The stack for the unbound constraint is the fields of the structure.
        // This happens before adding any names of methods, so that the block
        // can't use them.
        let unbound_constraint = if let Some(constraint) = &ss.constraint {
            let mut stack = Stack::new();
            for ((name_token, _, _), t) in ss.fields.iter().zip(&field_types) {
                stack.insert(name_token.to_string(), t.clone());
            }
            let unbound = self.evaluator(project).evaluate_value_with_stack(
                &mut stack,
                &constraint,
                Some(&AcornType::Bool),
            )?;
            let inhabited = AcornValue::Exists(field_types.clone(), Box::new(unbound.clone()));
            let block_params = BlockParams::TypeRequirement(inhabited, constraint.range());
            let block = Block::new(
                project,
                &self,
                vec![], // no type params
                vec![], // no args, because we already handled them
                block_params,
                statement.first_line(),
                statement.last_line(),
                ss.body.as_ref(),
            )?;
            let index = self.add_node(Node::block(project, self, block, None));
            self.add_node_lines(index, &statement.range());
            Some(unbound)
        } else {
            None
        };

        // The member functions take the type itself to a particular member.
        // These may be unresolved values.
        let datatype = Datatype {
            module_id: self.module_id,
            name: ss.name_token.text().to_string(),
        };
        let typeclasses = type_params.iter().map(|tp| tp.typeclass.clone()).collect();
        let doc_comments = self.take_doc_comments();
        let definition_string = Some(statement.to_string());
        let potential_type = self.bindings.add_potential_type(
            ss.name_token.text(),
            typeclasses,
            doc_comments,
            Some(ss.name_token.range()),
            definition_string,
        );
        let struct_type = potential_type.resolve(arbitrary_params, &ss.name_token)?;
        let mut member_fns = vec![];
        for ((member_fn_name, field_type), doc_comments) in member_fn_names
            .into_iter()
            .zip(&field_types)
            .zip(&field_doc_comments)
        {
            let member_fn_type =
                AcornType::functional(vec![struct_type.clone()], field_type.clone());
            let def_str = format!(
                "{}.{}: {}",
                ss.name_token.text(),
                member_fn_name,
                member_fn_type
            );
            let potential = self.bindings.add_datatype_attribute(
                &datatype,
                member_fn_name,
                type_params.clone(),
                member_fn_type.genericize(&type_params),
                None,
                None,
                doc_comments.clone(),
                def_str,
            );
            member_fns.push(potential);
        }

        // A "new" function to create one of these struct types.
        let new_fn_type = AcornType::functional(field_types.clone(), struct_type.clone());
        let constructor_info = ConstructorInfo {
            datatype: datatype.clone(),
            index: 0,
            total: 1,
        };
        let def_str = format!("{}.new: {}", ss.name_token.text(), new_fn_type);
        let new_fn = self.bindings.add_datatype_attribute(
            &datatype,
            "new",
            type_params.clone(),
            new_fn_type.genericize(&type_params),
            None,
            Some(constructor_info),
            vec![],
            def_str,
        );

        // Each object of this new type has certain properties.
        // member_args are expressions for each of these properties, with x0
        // assigned to a variable of our new type.
        let object_var = AcornValue::Variable(0, struct_type.clone());
        let mut member_args = vec![];
        for (i, member_fn) in member_fns.iter().enumerate() {
            let member_arg = self.bindings.apply_potential(
                member_fn.clone(),
                vec![object_var.clone()],
                None,
                &ss.fields[i].0,
            )?;
            member_args.push(member_arg);
        }
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ss.name_token.end_pos(),
        };

        // If there is a constraint, it applies to all instances of the type.
        // constraint(Pair.first(p), Pair.second(p))
        // This is the "constraint equation".
        if let Some(unbound_constraint) = &unbound_constraint {
            // As we start, the stack is all the members of p.
            // First, add a stack spot for p.
            let c = unbound_constraint.clone().insert_stack(0, 1);
            // Then, bind the members of p.
            let partially_bound = c.bind_values(1, 1, &member_args);
            // Then, bind a variable for p.
            let constraint_claim =
                AcornValue::ForAll(vec![struct_type.clone()], Box::new(partially_bound))
                    .genericize(&type_params);
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name_token.text().to_string(),
                "constraint".to_string(),
            );
            let prop = Proposition::new(constraint_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        // An object can be recreated by new'ing from its members. Ie:
        // Pair.new(Pair.first(p), Pair.second(p)) = p.
        // This is the "new equation" for a struct type.
        let recreated =
            self.bindings
                .apply_potential(new_fn.clone(), member_args, None, &ss.name_token)?;
        let new_eq =
            AcornValue::Binary(BinaryOp::Equals, Box::new(recreated), Box::new(object_var));
        let new_claim =
            AcornValue::ForAll(vec![struct_type], Box::new(new_eq)).genericize(&type_params);
        let source = Source::type_definition(
            self.module_id,
            range,
            self.depth,
            ss.name_token.text().to_string(),
            "new".to_string(),
        );
        let prop = Proposition::new(new_claim, type_params.clone(), source);
        self.add_node(Node::structural(project, self, prop));

        // There are also formulas for new followed by member functions. Ie:
        //   Pair.first(Pair.new(a, b)) = a.
        // These are the "member equations".
        //
        // When there's a constraint, we need to add it as a condition here, like:
        //   constraint(a, b) -> Pair.first(Pair.new(a, b)) = a.
        let var_args = (0..ss.fields.len())
            .map(|i| AcornValue::Variable(i as AtomId, field_types[i].clone()))
            .collect::<Vec<_>>();
        let new_application =
            self.bindings
                .apply_potential(new_fn, var_args, None, &ss.name_token)?;
        for i in 0..ss.fields.len() {
            let (field_name_token, field_type_expr, _) = &ss.fields[i];
            let member_fn = &member_fns[i];
            let applied = self.bindings.apply_potential(
                member_fn.clone(),
                vec![new_application.clone()],
                None,
                field_name_token,
            )?;
            let member_eq = AcornValue::Binary(
                BinaryOp::Equals,
                Box::new(applied),
                Box::new(AcornValue::Variable(i as AtomId, field_types[i].clone())),
            );
            let unbound_member_claim = if let Some(constraint) = &unbound_constraint {
                AcornValue::implies(constraint.clone(), member_eq)
            } else {
                member_eq
            };
            let member_claim =
                AcornValue::ForAll(field_types.clone(), Box::new(unbound_member_claim))
                    .genericize(&type_params);
            let range = Range {
                start: field_name_token.start_pos(),
                end: field_type_expr.last_token().end_pos(),
            };
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name_token.text().to_string(),
                field_name_token.text().to_string(),
            );
            let prop = Proposition::new(member_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        // Clean up the type parameters
        for type_param in &ss.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    fn add_inductive_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &InductiveStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        self.bindings
            .check_typename_available(is.name_token.text(), statement)?;
        let range = Range {
            start: statement.first_token.start_pos(),
            end: is.name_token.end_pos(),
        };

        // Add the new type first, because we can have self-reference in the inductive type.
        let mut arbitrary_params = vec![];
        let type_params = self
            .evaluator(project)
            .evaluate_type_params(&is.type_params)?;
        for type_param in &type_params {
            // Internally to the structure definition, the type parameters are
            // treated as arbitrary types.
            arbitrary_params.push(self.bindings.add_arbitrary_type(type_param.clone()));
        }
        let typeclasses = type_params.iter().map(|tp| tp.typeclass.clone()).collect();
        let doc_comments = self.take_doc_comments();
        let definition_string = Some(statement.to_string());
        let potential_type = self.bindings.add_potential_type(
            is.name_token.text(),
            typeclasses,
            doc_comments,
            Some(is.name_token.range()),
            definition_string,
        );
        let arb_inductive_type =
            potential_type.resolve(arbitrary_params.clone(), &is.name_token)?;

        // Parse (member name, list of arg types, doc comments) for each constructor.
        // This uses the arbitrary types.
        let mut constructors = vec![];
        let mut has_base = false;
        for (name_token, type_list_expr, doc_comments) in &is.constructors {
            let type_list = match type_list_expr {
                Some(expr) => {
                    let mut type_list = vec![];
                    self.evaluator(project)
                        .evaluate_type_list(expr, &mut type_list)?;
                    type_list
                }
                None => vec![],
            };
            if !type_list.contains(&arb_inductive_type) {
                // This provides a base case
                has_base = true;
            }
            constructors.push((name_token.text(), type_list, doc_comments.clone()));
        }
        if !has_base {
            return Err(statement.error("inductive type must have a base case"));
        }

        // Define the constructors.
        // constructor_fns contains the functions in their arbitrary forms, as AcornValue.
        let datatype = Datatype {
            module_id: self.module_id,
            name: is.name_token.text().to_string(),
        };
        let mut constructor_fns = vec![];
        let total = constructors.len();
        for (i, (constructor_name, type_list, doc_comments)) in constructors.iter().enumerate() {
            let arb_constructor_type =
                AcornType::functional(type_list.clone(), arb_inductive_type.clone());
            let gen_constructor_type = arb_constructor_type.genericize(&type_params);
            let constructor_info = ConstructorInfo {
                datatype: datatype.clone(),
                index: i,
                total,
            };
            let def_str = format!(
                "{}.{}: {}",
                is.name_token.text(),
                constructor_name,
                arb_constructor_type
            );
            let gen_constructor_fn = self.bindings.add_datatype_attribute(
                &datatype,
                constructor_name,
                type_params.clone(),
                gen_constructor_type,
                None,
                Some(constructor_info),
                doc_comments.clone(),
                def_str,
            );
            let arb_constructor_fn =
                gen_constructor_fn.resolve_constant(&arbitrary_params, &is.name_token)?;

            constructor_fns.push(arb_constructor_fn);
        }

        // The "no confusion" property. Different constructors give different results.
        for i in 0..constructors.len() {
            let (member_name, i_arg_types, _) = &constructors[i];
            let i_fn = constructor_fns[i].clone();
            let i_vars: Vec<_> = i_arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let i_app = AcornValue::apply(i_fn, i_vars);
            for j in 0..i {
                let (_, j_arg_types, _) = &constructors[j];
                let j_fn = constructor_fns[j].clone();
                let j_vars: Vec<_> = j_arg_types
                    .iter()
                    .enumerate()
                    .map(|(k, t)| {
                        AcornValue::Variable((k + i_arg_types.len()) as AtomId, t.clone())
                    })
                    .collect();
                let j_app = AcornValue::apply(j_fn, j_vars);
                let inequality = AcornValue::not_equals(i_app.clone(), j_app);
                let mut quantifiers = i_arg_types.clone();
                quantifiers.extend(j_arg_types.clone());
                let arb_claim = AcornValue::forall(quantifiers, inequality);
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    is.name_token.text().to_string(),
                    member_name.to_string(),
                );
                let gen_claim = arb_claim.genericize(&type_params);
                let prop = Proposition::new(gen_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));
            }
        }

        // The "canonical form" principle. Any item of this type must be created by one
        // of the constructors.
        // It seems like this is implied by induction but let's just stick it in.
        // x0 is going to be the "generic item of this type".
        let mut disjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types, _) = &constructors[i];
            let args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + 1) as AtomId, t.clone()))
                .collect();
            let app = AcornValue::apply(constructor_fn.clone(), args);
            let var = AcornValue::Variable(0, arb_inductive_type.clone());
            let equality = AcornValue::equals(var, app);
            let exists = AcornValue::exists(arg_types.clone(), equality);
            disjuncts.push(exists);
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
        let arb_claim = AcornValue::forall(vec![arb_inductive_type.clone()], disjunction);
        // There is no "new" for this type, but it's kind of thematically appropriate.
        let source = Source::type_definition(
            self.module_id,
            range,
            self.depth,
            is.name_token.text().to_string(),
            "new".to_string(),
        );
        let gen_claim = arb_claim.genericize(&type_params);
        let prop = Proposition::new(gen_claim, type_params.clone(), source);
        self.add_node(Node::structural(project, self, prop));

        // The next principle is that each constructor is injective.
        // Ie if Type.construct(x0, x1) = Type.construct(x2, x3) then x0 = x2 and x1 = x3.
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (member_name, arg_types, _) = &constructors[i];
            if arg_types.is_empty() {
                continue;
            }

            // First construct the equality.
            // "Type.construct(x0, x1) = Type.construct(x2, x3)"
            let left_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let lhs = AcornValue::apply(constructor_fn.clone(), left_args);
            let right_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + arg_types.len()) as AtomId, t.clone()))
                .collect();
            let rhs = AcornValue::apply(constructor_fn.clone(), right_args);
            let equality = AcornValue::equals(lhs, rhs);

            // Then construct the implication, that the corresponding args are equal.
            let mut conjuncts = vec![];
            for (i, arg_type) in arg_types.iter().enumerate() {
                let left = AcornValue::Variable(i as AtomId, arg_type.clone());
                let right = AcornValue::Variable((i + arg_types.len()) as AtomId, arg_type.clone());
                let arg_equality = AcornValue::equals(left, right);
                conjuncts.push(arg_equality);
            }
            let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
            let mut forall_types = arg_types.clone();
            forall_types.extend_from_slice(&arg_types);
            let arb_claim =
                AcornValue::forall(forall_types, AcornValue::implies(equality, conjunction));
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                is.name_token.text().to_string(),
                member_name.to_string(),
            );
            let gen_claim = arb_claim.genericize(&type_params);
            let prop = Proposition::new(gen_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        // Structural induction.
        // The type for the inductive hypothesis.
        let hyp_type = AcornType::functional(vec![arb_inductive_type.clone()], AcornType::Bool);
        // x0 represents the inductive hypothesis.
        // Think of the inductive principle as (conjunction) -> (conclusion).
        // The conjunction is a case for each constructor.
        // The conclusion is that x0 holds for all items of the type.
        let mut conjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types, _) = &constructors[i];
            let mut args = vec![];
            let mut conditions = vec![];
            for (j, arg_type) in arg_types.iter().enumerate() {
                // x0 is the inductive hypothesis so we start at 1 for the
                // constructor arguments.
                let id = (j + 1) as AtomId;
                args.push(AcornValue::Variable(id, arg_type.clone()));
                if arg_type == &arb_inductive_type {
                    // The inductive case for this constructor includes a condition
                    // that the inductive hypothesis holds for this argument.
                    conditions.push(AcornValue::apply(
                        AcornValue::Variable(0, hyp_type.clone()),
                        vec![AcornValue::Variable(id, arg_type.clone())],
                    ));
                }
            }

            let new_instance = AcornValue::apply(constructor_fn.clone(), args);
            let instance_claim = AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![new_instance],
            );
            let unbound = if conditions.is_empty() {
                // This is a base case. We just need to show that the inductive hypothesis
                // holds for this constructor.
                instance_claim
            } else {
                // This is an inductive case. Given the conditions, we show that
                // the inductive hypothesis holds for this constructor.
                AcornValue::implies(
                    AcornValue::reduce(BinaryOp::And, conditions),
                    instance_claim,
                )
            };
            let conjunction_part = AcornValue::forall(arg_types.clone(), unbound);
            conjuncts.push(conjunction_part);
        }
        let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
        let conclusion = AcornValue::forall(
            vec![arb_inductive_type.clone()],
            AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![AcornValue::Variable(1, arb_inductive_type.clone())],
            ),
        );
        let unbound_claim = AcornValue::implies(conjunction, conclusion);

        // The lambda form is the functional form, which we bind in the environment.
        let name = ConstantName::datatype_attr(datatype.clone(), "induction");
        let arb_lambda_claim = AcornValue::lambda(vec![hyp_type.clone()], unbound_claim.clone());
        let gen_lambda_claim = arb_lambda_claim.genericize(&type_params);
        let def_str = format!(
            "{}.induction: {}",
            is.name_token.text(),
            gen_lambda_claim.get_type()
        );
        self.bindings.add_datatype_attribute(
            &datatype,
            "induction",
            type_params.clone(),
            gen_lambda_claim.get_type(),
            Some(gen_lambda_claim),
            None,
            vec![],
            def_str,
        );
        self.bindings.mark_as_theorem(&name);

        // The forall form is the anonymous truth of induction.
        // We add that as a proposition.
        let arb_forall_claim = AcornValue::forall(vec![hyp_type], unbound_claim);
        let source = Source::theorem(
            true,
            self.module_id,
            range,
            true,
            self.depth,
            Some(name.to_string()),
        );
        let gen_forall_claim = arb_forall_claim.genericize(&type_params);
        let prop = Proposition::new(gen_forall_claim, type_params, source);
        self.add_node(Node::structural(project, self, prop));

        // Clean up the type parameters
        for type_param in &is.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    fn add_attributes_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ats: &AttributesStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);

        // Try type first
        if let Some(potential) = self.bindings.get_type_for_typename(ats.name_token.text()) {
            self.add_type_attributes(project, ats, potential.clone())
        } else if let Some(typeclass) = self.bindings.get_typeclass_for_name(ats.name_token.text())
        {
            self.add_typeclass_attributes(project, ats, typeclass.clone())
        } else {
            Err(ats.name_token.error(&format!(
                "undefined type or typeclass name '{}'",
                ats.name_token.text()
            )))
        }
    }

    fn add_type_attributes(
        &mut self,
        project: &mut Project,
        ats: &AttributesStatement,
        potential: crate::acorn_type::PotentialType,
    ) -> compilation::Result<()> {
        let type_params = self
            .evaluator(project)
            .evaluate_type_params(&ats.type_params)?;
        let mut params = vec![];
        for param in &type_params {
            params.push(self.bindings.add_arbitrary_type(param.clone()));
        }
        let instance_type = potential.invertible_resolve(params, &ats.name_token)?;
        let datatype = self.check_can_add_attributes(&ats.name_token, &instance_type)?;

        for substatement in &ats.body.statements {
            match &substatement.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        substatement,
                        DefinedName::datatype_attr(datatype, ls.name_token.text()),
                        ls,
                        ls.name_token.range(),
                        Some(&type_params),
                    )?;
                }
                StatementInfo::Define(ds) => {
                    self.add_define_statement(
                        project,
                        substatement,
                        DefinedName::datatype_attr(datatype, ds.name_token.text()),
                        Some(&instance_type),
                        Some(&type_params),
                        ds,
                        ds.name_token.range(),
                    )?;
                }
                StatementInfo::DocComment(s) => {
                    // Add to self.doc_comments so it will be picked up by the next statement
                    self.doc_comments.push(s.clone());
                }
                _ => {
                    return Err(substatement
                        .error("only let, define, and doc comment statements are allowed in attributes bodies"));
                }
            }
        }
        for type_param in &ats.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    fn add_typeclass_attributes(
        &mut self,
        project: &mut Project,
        ats: &AttributesStatement,
        typeclass: crate::acorn_type::Typeclass,
    ) -> compilation::Result<()> {
        // Typeclasses don't support type parameters yet
        if !ats.type_params.is_empty() {
            return Err(ats.type_params[0]
                .name
                .error("typeclass attributes do not support type parameters"));
        }

        // For typeclass attributes, we need an instance name
        let instance_name_token = ats.instance_name.as_ref().ok_or_else(|| {
            ats.name_token.error(
                "typeclass attributes require an instance name (e.g., 'attributes M: Magma')",
            )
        })?;

        // Bind the instance type as a type parameter with the typeclass constraint
        let instance_name = instance_name_token.text();
        let type_param = crate::acorn_type::TypeParam {
            name: instance_name.to_string(),
            typeclass: Some(typeclass.clone()),
        };
        let instance_type = self.bindings.add_arbitrary_type(type_param.clone());
        let type_params = vec![type_param];

        for substatement in &ats.body.statements {
            match &substatement.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        substatement,
                        DefinedName::typeclass_attr(&typeclass, ls.name_token.text()),
                        ls,
                        ls.name_token.range(),
                        Some(&type_params),
                    )?;
                }
                StatementInfo::Define(ds) => {
                    self.add_define_statement(
                        project,
                        substatement,
                        DefinedName::typeclass_attr(&typeclass, ds.name_token.text()),
                        Some(&instance_type),
                        Some(&type_params),
                        ds,
                        ds.name_token.range(),
                    )?;
                }
                StatementInfo::DocComment(s) => {
                    // Add to self.doc_comments so it will be picked up by the next statement
                    self.doc_comments.push(s.clone());
                }
                _ => {
                    return Err(substatement
                        .error("only let, define, and doc comment statements are allowed in attributes bodies"));
                }
            }
        }

        // Clean up the instance type binding
        self.bindings.remove_type(instance_name);
        Ok(())
    }

    fn add_typeclass_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TypeclassStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);

        // Figure out what, if anything, this extends.
        let mut extends = vec![];
        for extend in &ts.extends {
            let typeclass = self.evaluator(project).evaluate_typeclass(extend)?;
            extends.push(typeclass);
        }

        // Check names are available and bind the typeclass.
        let typeclass_name = ts.typeclass_name.text();
        self.bindings
            .check_typename_available(typeclass_name, statement)?;
        let typeclass = Typeclass {
            module_id: self.module_id,
            name: typeclass_name.to_string(),
        };
        let doc_comments = self.take_doc_comments();
        let definition_string = Some(statement.to_string());
        self.bindings.add_typeclass(
            typeclass_name,
            extends,
            doc_comments,
            Some(ts.typeclass_name.range()),
            definition_string,
            &project,
            &ts.typeclass_name,
        )?;

        // For block syntax, we also need to bind the instance name
        let type_params = if let Some(instance_name_token) = &ts.instance_name {
            let instance_name = instance_name_token.text();
            self.bindings
                .check_typename_available(instance_name, statement)?;
            let type_param = TypeParam {
                name: instance_name.to_string(),
                typeclass: Some(typeclass.clone()),
            };
            self.bindings.add_arbitrary_type(type_param.clone());
            vec![type_param.clone()]
        } else {
            // No-block syntax doesn't have an instance name
            vec![]
        };

        if let Some(extends_set) = self.bindings.get_extends_set(&typeclass) {
            // Create a node for the extends relationship.
            let source = Source {
                module_id: self.module_id,
                range: statement.range(),
                source_type: SourceType::Extends(typeclass_name.to_string()),
                importable: true,
                depth: self.depth,
            };
            let extends_fact = Fact::Extends(typeclass.clone(), extends_set.clone(), source);
            self.add_node(Node::Structural(extends_fact));
        }

        // Define all the constants that are in the typeclass.
        // Only applicable for block syntax, not no-block syntax
        if !type_params.is_empty() {
            let type_param = &type_params[0]; // For block syntax, there's exactly one type param
            for (attr_name, type_expr, doc_comments) in &ts.constants {
                if let Some(existing_tc) = self
                    .bindings
                    .typeclass_attr_lookup(&typeclass, attr_name.text())
                {
                    return Err(attr_name.error(&format!(
                        "attribute '{}' is already defined via base typeclass '{}'",
                        attr_name.text(),
                        existing_tc.name
                    )));
                }
                let arb_type = self.evaluator(project).evaluate_type(type_expr)?;
                let var_type = arb_type.genericize(&type_params);
                let defined_name = DefinedName::typeclass_attr(&typeclass, attr_name.text());
                self.bindings
                    .check_defined_name_available(&defined_name, attr_name)?;
                let def_str = format!("{}: {}", attr_name.text(), type_expr);
                self.bindings.add_typeclass_attribute(
                    &typeclass,
                    &attr_name.text(),
                    vec![type_param.clone()],
                    var_type,
                    None,
                    None,
                    doc_comments.clone(),
                    def_str,
                );
                // Mark as required since it's from the initial typeclass definition
                self.bindings
                    .mark_typeclass_attr_required(&typeclass, &attr_name.text());
            }
        }

        // Add a node for each typeclass condition.
        // The node says, "this condition is true for all instances of the typeclass".
        // Conditions are similar to theorems, but they don't get proven at the typeclass level.
        // So they don't have blocks.
        // They do get proven, but in the instance statement, not in the typeclass statement.
        // Only applicable for block syntax, not no-block syntax
        if !type_params.is_empty() {
            let type_param = &type_params[0]; // For block syntax, there's exactly one type param
            for condition in &ts.conditions {
                let range = Range {
                    start: condition.name_token.start_pos(),
                    end: condition.claim.last_token().end_pos(),
                };
                let defined_name =
                    DefinedName::typeclass_attr(&typeclass, &condition.name_token.text());
                self.bindings
                    .check_defined_name_available(&defined_name, &condition.name_token)?;

                let (bad_params, _, arg_types, unbound_claim, _) =
                    self.bindings.evaluate_scoped_value(
                        &[],
                        &condition.args,
                        None,
                        &condition.claim,
                        None,
                        None,
                        project,
                        Some(&mut self.token_map),
                    )?;
                if !bad_params.is_empty() {
                    return Err(condition
                        .name_token
                        .error("type parameters are not allowed here"));
                }
                let unbound_claim = unbound_claim
                    .ok_or_else(|| condition.claim.error("conditions must have values"))?;
                let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone())
                    .genericize(&type_params);
                if let Err(message) = external_claim.validate() {
                    return Err(condition.claim.error(&message));
                }
                let lambda_claim = AcornValue::lambda(arg_types.clone(), unbound_claim.clone())
                    .genericize(&type_params);
                let theorem_type = lambda_claim.get_type();
                self.bindings.add_typeclass_attribute(
                    &typeclass,
                    &condition.name_token.text(),
                    type_params.clone(),
                    theorem_type.clone(),
                    Some(lambda_claim),
                    None,
                    condition.doc_comments.clone(),
                    condition.to_string(),
                );

                let source = Source::theorem(
                    true,
                    self.module_id,
                    range,
                    true,
                    self.depth,
                    Some(defined_name.to_string()),
                );
                let prop = Proposition::new(external_claim, vec![type_param.clone()], source);
                self.add_node(Node::structural(project, self, prop));
                let constant_name =
                    ConstantName::typeclass_attr(typeclass.clone(), &condition.name_token.text());
                self.bindings.mark_as_theorem(&constant_name);
            }
        }

        // For block syntax, remove the instance type
        if let Some(instance_name_token) = &ts.instance_name {
            self.bindings.remove_type(instance_name_token.text());
        }
        Ok(())
    }

    fn add_instance_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &InstanceStatement,
    ) -> compilation::Result<()> {
        // Create an expression from the type name token and evaluate it to track the token
        let type_expr = Expression::Singleton(is.type_name.clone());
        let instance_type = self.evaluator(project).evaluate_type(&type_expr)?;
        let instance_datatype = self.check_can_add_attributes(&is.type_name, &instance_type)?;
        let typeclass = self.evaluator(project).evaluate_typeclass(&is.typeclass)?;

        // Every base typeclass that this typeclass extends, the instance class must
        // already be an instance of.
        for base_typeclass in self.bindings.get_extends(&typeclass) {
            if !self
                .bindings
                .is_instance_of(&instance_datatype, &base_typeclass)
            {
                return Err(statement.error(&format!(
                    "'{}' must be an instance of '{}' in order to be an instance of '{}'",
                    is.type_name, base_typeclass.name, typeclass.name
                )));
            }
        }

        // Pairs contains (resolved constant, defined constant) for each attribute.
        let mut pairs = vec![];

        // Process definitions if they exist (block syntax), otherwise skip (no-block syntax)
        if let Some(definitions) = &is.definitions {
            for substatement in &definitions.statements {
                match &substatement.statement {
                    StatementInfo::Let(ls) => {
                        self.add_let_statement(
                            project,
                            substatement,
                            DefinedName::instance(
                                typeclass.clone(),
                                ls.name_token.text(),
                                instance_datatype.clone(),
                            ),
                            ls,
                            ls.name_token.range(),
                            None,
                        )?;

                        pairs.push(self.bindings.check_instance_attribute(
                            &instance_type,
                            &typeclass,
                            ls.name_token.text(),
                            &project,
                            substatement,
                        )?);
                    }
                    StatementInfo::Define(ds) => {
                        if !ds.type_params.is_empty() {
                            return Err(substatement.error("type parameters are not allowed here"));
                        }
                        self.add_define_statement(
                            project,
                            substatement,
                            DefinedName::instance(
                                typeclass.clone(),
                                ds.name_token.text(),
                                instance_datatype.clone(),
                            ),
                            Some(&instance_type),
                            None,
                            ds,
                            ds.name_token.range(),
                        )?;

                        pairs.push(self.bindings.check_instance_attribute(
                            &instance_type,
                            &typeclass,
                            ds.name_token.text(),
                            &project,
                            substatement,
                        )?);
                    }
                    _ => {
                        return Err(substatement.error(
                            "only let and define statements are allowed in instance bodies",
                        ));
                    }
                }
            }
        }

        // Check that we have all implementations.
        let attributes = self.bindings.get_typeclass_attributes(&typeclass, &project);
        let mut conditions = vec![];
        let mut defaults_to_add = vec![]; // Collect defaults to add after the loop

        for (attr_name, (_module_id, root_tc)) in attributes.iter() {
            if root_tc != &typeclass {
                // This attribute is inherited, so we don't need to check it.
                continue;
            }

            let tc_attr_name = ConstantName::typeclass_attr(typeclass.clone(), attr_name);
            let tc_bindings = self.bindings.get_bindings(typeclass.module_id, project);
            if tc_bindings.is_theorem(&tc_attr_name) {
                // Conditions don't have an implementation.
                // We do gather them for verification.
                // First, we create a condition that is "unsafe" in the sense that it contains
                // typeclass attribute functions applied to the instance type, which is not
                // yet proven to be an instance of the typeclass.
                let unsafe_condition = self.bindings.unsafe_instantiate_condition(
                    &typeclass,
                    &attr_name,
                    &instance_type,
                    project,
                    statement,
                )?;
                // Now we make the condition safe by replacing the unsafe constants with their
                // definitions.
                let condition = unsafe_condition.replace_constants(0, &|ci| {
                    let name = match ci.to_defined_instance_name(&typeclass, &instance_datatype) {
                        Some(name) => name,
                        None => return None,
                    };
                    self.bindings.get_definition(&name).cloned()
                });
                conditions.push(condition);
                continue;
            }

            // Only check required attributes for implementation
            if !self
                .bindings
                .is_typeclass_attr_required(&typeclass, attr_name)
            {
                // This is an optional attribute added via "attributes" statement, skip validation
                continue;
            }

            let name =
                DefinedName::instance(typeclass.clone(), attr_name, instance_datatype.clone());
            if !self.bindings.constant_name_in_use(&name) {
                // Check if a datatype attribute with the same name exists
                let datatype_attr_name = DefinedName::datatype_attr(&instance_datatype, attr_name);
                if self.bindings.constant_name_in_use(&datatype_attr_name) {
                    // Check that the types match
                    let tc_attr_name = DefinedName::typeclass_attr(&typeclass, attr_name);
                    let tc_attr = self.bindings.get_constant_value(&tc_attr_name, statement)?;
                    let tc_unresolved = tc_attr.to_unresolved(statement)?;
                    let tc_resolved =
                        tc_unresolved.resolve(statement, vec![instance_type.clone()])?;
                    let tc_type = tc_resolved.get_type();

                    let dt_attr = self
                        .bindings
                        .get_constant_value(&datatype_attr_name, statement)?;
                    let dt_value = dt_attr.as_value(statement)?;
                    let dt_type = dt_value.get_type();

                    if tc_type != dt_type {
                        return Err(statement.error(&format!(
                            "type mismatch for attribute '{}': typeclass expects {}, but datatype has {}",
                            attr_name, tc_type, dt_type
                        )));
                    }

                    // Store the information to add the default after the loop
                    defaults_to_add.push((name, tc_type, dt_value.clone(), tc_resolved, dt_value));
                } else {
                    return Err(statement
                        .error(&format!("missing implementation for attribute '{}'", name)));
                }
            }
        }

        // Now add any defaults we found
        for (name, tc_type, dt_value, tc_resolved, dt_value_for_pair) in defaults_to_add {
            self.define_constant(
                name,
                vec![],
                tc_type,
                Some(dt_value),
                statement.range(),
                None,
            );
            pairs.push((tc_resolved, dt_value_for_pair));
        }

        // Create a node for the instance relationship.
        let source = Source {
            module_id: self.module_id,
            range: statement.range(),
            source_type: SourceType::Instance(
                is.type_name.text().to_string(),
                typeclass.name.to_string(),
            ),
            importable: true,
            depth: self.depth,
        };
        let instance_fact = Fact::Instance(instance_datatype.clone(), typeclass.clone(), source);

        let node = if conditions.is_empty() {
            Node::Structural(instance_fact)
        } else {
            // We must prove in a block that all the conditions hold for this instance.
            let conditions_claim = AcornValue::reduce(BinaryOp::And, conditions);
            let range = Range {
                start: statement.first_token.start_pos(),
                end: if let Some(definitions) = &is.definitions {
                    definitions.right_brace.end_pos()
                } else {
                    statement.last_token.end_pos()
                },
            };
            let block_params = BlockParams::TypeRequirement(conditions_claim, range);
            let block = Block::new(
                project,
                &self,
                vec![], // no type params
                vec![], // no args
                block_params,
                statement.first_line(),
                statement.last_line(),
                is.body.as_ref(),
            )?;
            Node::Block(block, Some(instance_fact))
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        self.bindings
            .add_instance_of(instance_datatype.clone(), typeclass);
        Ok(())
    }

    /// Adds a type statement to the environment.
    fn add_type_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TypeStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        self.bindings
            .check_typename_available(ts.name_token.text(), statement)?;
        if ts.type_expr.is_axiom() {
            let doc_comments = self.take_doc_comments();
            let definition_string = Some(statement.to_string());
            self.bindings.add_potential_type(
                ts.name_token.text(),
                vec![],
                doc_comments,
                Some(ts.name_token.range()),
                definition_string,
            );
        } else {
            let potential = self
                .evaluator(project)
                .evaluate_potential_type(&ts.type_expr)?;
            self.bindings
                .add_type_alias(ts.name_token.text(), potential);
        };
        Ok(())
    }

    /// Adds a claim statement to the environment.
    fn add_claim_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        cs: &ClaimStatement,
    ) -> compilation::Result<()> {
        let claim = self
            .evaluator(project)
            .evaluate_value(&cs.claim, Some(&AcornType::Bool))?;
        if claim == AcornValue::Bool(false) {
            self.includes_explicit_false = true;
        }

        if self.bindings.is_citation(&claim, project) {
            // We already know this is true, so we don't need to prove it
            let source = Source::anonymous(self.module_id, statement.range(), self.depth);
            let prop = Proposition::monomorphic(claim, source);
            self.add_node(Node::structural(project, self, prop));
            self.add_other_lines(statement);
        } else {
            let source = Source::anonymous(self.module_id, statement.range(), self.depth);
            let prop = Proposition::monomorphic(claim, source);
            let index = self.add_node(Node::claim(project, self, prop));
            self.add_node_lines(index, &statement.range());
        }
        Ok(())
    }

    /// Adds a forall statement to the environment.
    fn add_forall_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fas: &ForAllStatement,
    ) -> compilation::Result<()> {
        if fas.body.statements.is_empty() {
            // ForAll statements with an empty body can just be ignored
            return Ok(());
        }
        let mut args = vec![];
        for quantifier in &fas.quantifiers {
            let (arg_name, arg_type) = self.evaluator(project).evaluate_declaration(quantifier)?;
            args.push((arg_name, arg_type));
        }

        let block = Block::new(
            project,
            &self,
            vec![],
            args,
            BlockParams::ForAll,
            statement.first_line(),
            statement.last_line(),
            Some(&fas.body),
        )?;

        let (outer_claim, range) = block.externalize_last_claim(self, &fas.body.right_brace)?;
        let source = Source::anonymous(self.module_id, range, self.depth);
        let prop = Proposition::monomorphic(outer_claim, source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds an if statement to the environment.
    fn add_if_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &IfStatement,
    ) -> compilation::Result<()> {
        let condition = self
            .evaluator(project)
            .evaluate_value(&is.condition, Some(&AcornType::Bool))?;
        let range = is.condition.range();
        let if_claim = self.add_conditional(
            project,
            condition.clone(),
            range,
            statement.first_line(),
            statement.last_line(),
            &is.body,
            None,
        )?;
        if let Some(else_body) = &is.else_body {
            self.add_conditional(
                project,
                condition.negate(),
                range,
                else_body.left_brace.line_number as u32,
                else_body.right_brace.line_number as u32,
                else_body,
                if_claim,
            )?;
        }
        Ok(())
    }

    /// Adds an import statement to the environment.
    fn add_import_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &ImportStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);

        // Give a local name to the imported module
        let local_name = is.components.last().unwrap().text();
        self.bindings
            .check_unqualified_name_available(local_name, statement)?;
        let full_name_vec: Vec<_> = is.components.iter().map(|t| t.text().to_string()).collect();
        let full_name = full_name_vec.join(".");
        let module_id = match project.load_module_by_name(&full_name) {
            Ok(module_id) => module_id,
            Err(ImportError::NotFound(message)) => {
                // The error is with the import statement itself, like a typo.
                return Err(statement.error(&message));
            }
            Err(ImportError::Circular(module_id)) => {
                // Circular imports kind of count everywhere.
                return Err(Error::circular(
                    module_id,
                    &statement.first_token,
                    &statement.last_token,
                    &format!("circular import of '{}' module", full_name),
                ));
            }
        };
        match project.get_bindings(module_id) {
            None => {
                // The fundamental error is in the other module, not this one.
                return Err(Error::indirect(
                    &statement.first_token,
                    &statement.last_token,
                    &format!("error in '{}' module", full_name),
                ));
            }
            Some(bindings) => {
                self.bindings.import_module(
                    local_name,
                    full_name_vec,
                    &bindings,
                    &statement.first_token,
                )?;
            }
        }

        // Track token for the module (only the last component represents the module)
        if let Some(last_component) = is.components.last() {
            self.token_map
                .track_token(last_component, &NamedEntity::Module(module_id));
        }

        // Bring the imported names into this environment
        for name in &is.names {
            let entity = self.bindings.import_name(project, module_id, name)?;
            self.token_map.track_token(name, &entity);
        }

        Ok(())
    }

    /// Adds a numerals statement to the environment.
    fn add_numerals_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ds: &NumeralsStatement,
    ) -> compilation::Result<()> {
        self.add_other_lines(statement);
        let acorn_type = self.evaluator(project).evaluate_type(&ds.type_expr)?;
        if let AcornType::Data(datatype, params) = acorn_type {
            if !params.is_empty() {
                return Err(ds
                    .type_expr
                    .error("numerals type cannot have type parameters"));
            }
            self.bindings.set_numerals(datatype);
            Ok(())
        } else {
            Err(ds.type_expr.error("numerals type must be a data type"))
        }
    }

    /// Adds a solve statement to the environment.
    fn add_solve_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ss: &SolveStatement,
    ) -> compilation::Result<()> {
        let target = self.evaluator(project).evaluate_value(&ss.target, None)?;
        let solve_range = Range {
            start: statement.first_token.start_pos(),
            end: ss.target.last_token().end_pos(),
        };

        let mut block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Solve(target.clone(), solve_range),
            statement.first_line(),
            statement.last_line(),
            Some(&ss.body),
        )?;

        let prop = match block.solves(self, &target) {
            Some((outer_claim, claim_range)) => {
                block.goal = None;
                let source = Source::anonymous(self.module_id, claim_range, self.depth);
                Some(Proposition::monomorphic(outer_claim, source))
            }
            None => None,
        };

        let index = self.add_node(Node::block(project, self, block, prop));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds a problem statement to the environment.
    fn add_problem_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        body: &Body,
    ) -> compilation::Result<()> {
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Problem,
            statement.first_line(),
            statement.last_line(),
            Some(body),
        )?;

        let index = self.add_node(Node::block(project, self, block, None));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds a todo statement to the environment.
    fn add_todo_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TodoStatement,
    ) -> compilation::Result<()> {
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Todo,
            statement.first_line(),
            statement.last_line(),
            Some(&ts.body),
        )?;

        let index = self.add_node(Node::block(project, self, block, None));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds a match statement to the environment.
    fn add_match_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ms: &MatchStatement,
    ) -> compilation::Result<()> {
        let scrutinee = self
            .evaluator(project)
            .evaluate_value(&ms.scrutinee, None)?;
        let scrutinee_type = scrutinee.get_type();
        let mut indices = vec![];
        let mut disjuncts = vec![];
        for (pattern, body) in &ms.cases {
            let (constructor, args, i, total) = self
                .evaluator(project)
                .evaluate_pattern(&scrutinee_type, pattern)?;
            if indices.contains(&i) {
                return Err(pattern.error("duplicate pattern in match statement"));
            }
            indices.push(i);

            let params =
                BlockParams::MatchCase(scrutinee.clone(), constructor, args, pattern.range());

            let block = Block::new(
                project,
                &self,
                vec![],
                vec![],
                params,
                body.left_brace.line_number,
                body.right_brace.line_number,
                Some(body),
            )?;

            let (disjunct, _) = block.externalize_last_claim(self, &body.right_brace)?;
            disjuncts.push(disjunct);

            if total == indices.len() {
                if ms.cases.len() > total {
                    // The next iteration will report an error
                    continue;
                }

                let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
                let source = Source::anonymous(self.module_id, statement.range(), self.depth);
                let prop = Proposition::monomorphic(disjunction, source);
                let index = self.add_node(Node::block(project, self, block, Some(prop)));
                self.add_node_lines(index, &body.range());
                return Ok(());
            }

            // No proposition here. We only put an externalized proposition on the last block.
            let index = self.add_node(Node::block(project, self, block, None));
            self.add_node_lines(index, &body.range());
        }
        Err(ms
            .scrutinee
            .error("not all cases are covered in match statement"))
    }
}
