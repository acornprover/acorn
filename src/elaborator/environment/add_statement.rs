use std::sync::Arc;

use tower_lsp::lsp_types::Range;

use crate::elaborator::acorn_type::{
    AcornType, Datatype, DependentTypeArg, FamilyParam, TypeParam, Typeclass, TypeclassInstance,
    ValueParam, Variance,
};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp};
use crate::elaborator::binding_map::ConstructorInfo;
use crate::elaborator::block::{Block, BlockParams};
use crate::elaborator::error::{self, Error, ErrorContext};
use crate::elaborator::evaluator::{AttributesTypeArgs, Evaluator};
use crate::elaborator::fact::Fact;
use crate::elaborator::inference::InferenceEngine;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::elaborator::node::Node;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::{Source, SourceType};
use crate::elaborator::stack::Stack;
use crate::kernel::atom::AtomId;
use crate::project::{ImportError, Project};
use crate::syntax::expression::{Declaration, Expression};
use crate::syntax::statement::{
    AttributesStatement, ClaimStatement, DefineStatement, DestructuringStatement, ForAllStatement,
    FunctionSatisfyStatement, IfStatement, ImportStatement, InductiveStatement, InstanceStatement,
    LetStatement, MatchStatement, NumeralsStatement, Statement, StatementInfo, StructureStatement,
    TheoremStatement, TypeStatement, TypeclassStatement, VariableSatisfyStatement,
};
use crate::syntax::token::{Token, TokenIter, TokenType};

use super::{Environment, LineType};

/// The hidden family binders that come from the surrounding datatype/typeclass header while we
/// elaborate an attribute or member body.
///
/// Example: inside `attributes Zmod[k: Nat] { ... }`, the body is not itself parameterized, but
/// every defined constant implicitly depends on the outer `k`. This helper keeps those ambient
/// binders together so downstream code can:
/// - genericize over the type parameters
/// - keep the value parameters as hidden leading constant binders
/// - reintroduce the value params into local stacks/proof blocks when elaborating bodies
#[derive(Clone, Debug, Default)]
struct DatatypeFamilyScope {
    type_params: Vec<TypeParam>,
    value_params: Vec<ValueParam>,
}

impl DatatypeFamilyScope {
    fn type_params_slice(&self) -> &[TypeParam] {
        &self.type_params
    }

    fn value_params_slice(&self) -> &[ValueParam] {
        &self.value_params
    }

    fn value_param_types(&self) -> Vec<AcornType> {
        self.value_params
            .iter()
            .map(|param| param.value_type.clone())
            .collect()
    }

    fn value_block_args(&self) -> Vec<(String, AcornType)> {
        self.value_params
            .iter()
            .map(|param| (param.name.clone(), param.value_type.clone()))
            .collect()
    }

    fn bind_value_stack(&self, stack: &mut Stack) {
        for param in &self.value_params {
            stack.insert(param.name.clone(), param.value_type.clone());
        }
    }
}

mod attributes;
mod blocks;
mod datatypes;
mod definitions;
mod imports;
mod simple_types;
mod typeclasses;

// This file generally contains the logic for creating an environment.
// It would be nice for the separation to be cleaner.

impl Environment {
    /// Parse these tokens and add them to the environment.
    /// If project is not provided, we won't be able to handle import statements.
    pub fn add_tokens(
        &mut self,
        project: &mut Project,
        tokens: Vec<Token>,
        strict: bool,
    ) -> error::Result<()> {
        let mut tokens = TokenIter::new(tokens);
        loop {
            match Statement::parse(&mut tokens, false, strict) {
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
    ) -> error::Result<()> {
        if self.includes_explicit_false {
            return Err(
                statement.error("an explicit 'false' may not be followed by other statements")
            );
        }

        if !matches!(&statement.statement, StatementInfo::DocComment(_)) {
            let current_line = statement.first_line();

            if self.at_module_beginning {
                if let Some(last_line) = self.last_statement_line {
                    if current_line > last_line + 1 {
                        self.module_doc_comments.extend(self.doc_comments.drain(..));
                    }
                }
                self.at_module_beginning = false;
            }
        }

        let result = match &statement.statement {
            StatementInfo::Type(ts) => self.add_type_statement(project, statement, ts),

            StatementInfo::Let(ls) => self.add_let_statement(
                project,
                statement,
                DefinedName::unqualified(self.module_id, ls.name_token.text()),
                ls,
                ls.name_token.range(),
                None,
            ),

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

            StatementInfo::Match(ms) => self.add_match_statement(project, statement, ms),

            StatementInfo::Typeclass(ts) => self.add_typeclass_statement(project, statement, ts),

            StatementInfo::Instance(is) => self.add_instance_statement(project, statement, is),

            StatementInfo::Destructuring(ds) => {
                self.add_destructuring_statement(project, statement, ds)
            }

            StatementInfo::DocComment(s) => {
                let current_line = statement.first_line();

                if self.at_module_beginning {
                    if let Some(last_line) = self.last_statement_line {
                        if current_line > last_line + 1 {
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

        if !matches!(&statement.statement, StatementInfo::DocComment(_)) {
            self.doc_comments.clear();
            self.last_statement_line = Some(statement.first_line());
            if result.is_ok() {
                self.sync_current_binding_state();
            }
        }

        result
    }
}
