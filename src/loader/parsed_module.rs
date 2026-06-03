use std::collections::HashSet;

use crate::elaborator::error::{self, ErrorContext};
use crate::module::ModuleDescriptor;
use crate::syntax::expression::{Declaration, Expression, LocalBlockItem, TypeParamExpr};
use crate::syntax::statement::{Body, ImportStatement, Statement, StatementInfo};
use crate::syntax::token::{Token, TokenIter, TokenType};

pub const MAX_EXPORTED_DECLARATIONS_PER_MODULE: usize = 500;

/// The source-level output of the first loading stage.
///
/// This is deliberately before elaboration: dependencies are module names discovered by walking
/// the parsed syntax tree, while import visibility is still applied later by the elaborator in
/// source order.
pub struct ParsedModule {
    pub descriptor: ModuleDescriptor,
    pub statements: Vec<Statement>,
    pub dependency_names: Vec<String>,
    pub implicit_lib_dependency_names: Vec<String>,
    pub content_hash: blake3::Hash,
}

#[derive(Default)]
struct DependencyCollector {
    all: Vec<String>,
    seen_all: HashSet<String>,
    implicit_lib: Vec<String>,
    seen_implicit_lib: HashSet<String>,
}

impl DependencyCollector {
    fn add_explicit_import(&mut self, module_name: String) {
        self.add_dependency(module_name);
    }

    fn add_implicit_lib(&mut self, module_name: String) {
        if self.seen_implicit_lib.insert(module_name.clone()) {
            self.implicit_lib.push(module_name.clone());
        }
        self.add_dependency(module_name);
    }

    fn add_dependency(&mut self, module_name: String) {
        if self.seen_all.insert(module_name.clone()) {
            self.all.push(module_name);
        }
    }
}

impl ParsedModule {
    pub fn parse(descriptor: ModuleDescriptor, text: String, strict: bool) -> error::Result<Self> {
        let statements = parse_module_statements(&text, strict)?;
        check_exported_declaration_limit(&statements)?;

        let mut dependencies = DependencyCollector::default();
        for statement in &statements {
            collect_dependencies_from_statement(statement, &mut dependencies);
        }

        let mut content_hasher = blake3::Hasher::new();
        content_hasher.update(text.as_bytes());
        let content_hash = content_hasher.finalize();

        Ok(Self {
            descriptor,
            statements,
            dependency_names: dependencies.all,
            implicit_lib_dependency_names: dependencies.implicit_lib,
            content_hash,
        })
    }

    pub fn module_name(&self) -> Option<String> {
        match &self.descriptor {
            ModuleDescriptor::Name(parts) => Some(parts.join(".")),
            ModuleDescriptor::Anonymous | ModuleDescriptor::File(_) => None,
        }
    }

    pub fn apply_interface_mode(&mut self) -> error::Result<()> {
        for statement in &mut self.statements {
            apply_interface_statement_mode(statement, false)?;
        }
        Ok(())
    }
}

fn apply_interface_statement_mode(
    statement: &mut Statement,
    in_attributes: bool,
) -> error::Result<()> {
    if in_attributes
        && !matches!(
            &statement.statement,
            StatementInfo::Let(_)
                | StatementInfo::Define(_)
                | StatementInfo::VariableSatisfy(_)
                | StatementInfo::FunctionSatisfy(_)
                | StatementInfo::DocComment(_)
        )
    {
        return Err(statement.error(
            "only let, let ... satisfy, define, and doc comment statements are allowed in attributes bodies",
        ));
    }

    match &mut statement.statement {
        StatementInfo::Let(ls) => {
            check_interface_type_params(&ls.type_params)?;
            if let Some(type_expr) = &ls.type_expr {
                check_interface_expression(type_expr)?;
            }
            check_interface_expression(&ls.value)?;
        }
        StatementInfo::Define(ds) => {
            check_interface_type_params(&ds.type_params)?;
            check_interface_declarations(&ds.args)?;
            check_interface_expression(&ds.return_type)?;
            check_interface_expression(&ds.return_value)?;
        }
        StatementInfo::Theorem(theorem) => {
            if theorem.lemma {
                return Err(statement.error("interface.ac cannot contain lemmas"));
            }
            if theorem.axiomatic {
                return Err(statement.error("interface axioms are not allowed"));
            }
            if theorem.body.is_some() {
                return Err(statement.error("interface theorems cannot have proof bodies"));
            }
            theorem.trusted = true;
            check_interface_type_params(&theorem.type_params)?;
            check_interface_declarations(&theorem.args)?;
            check_interface_expression(&theorem.claim)?;
        }
        StatementInfo::Claim(cs) => {
            check_interface_expression(&cs.claim)?;
        }
        StatementInfo::Type(ts) => {
            check_interface_type_params(&ts.type_params)?;
            check_interface_expression(&ts.type_expr)?;
        }
        StatementInfo::ForAll(fas) => {
            check_interface_declarations(&fas.quantifiers)?;
            check_interface_body(&mut fas.body)?;
        }
        StatementInfo::If(is) => {
            check_interface_expression(&is.condition)?;
            check_interface_body(&mut is.body)?;
            if let Some(else_body) = &mut is.else_body {
                check_interface_body(else_body)?;
            }
        }
        StatementInfo::VariableSatisfy(vss) => {
            check_interface_type_params(&vss.type_params)?;
            check_interface_declarations(&vss.declarations)?;
            check_interface_expression(&vss.condition)?;
        }
        StatementInfo::FunctionSatisfy(fss) => {
            if fss.body.is_some() {
                return Err(
                    statement.error("interface let-satisfy declarations cannot have proof bodies")
                );
            }
            check_interface_type_params(&fss.type_params)?;
            check_interface_declarations(&fss.declarations)?;
            check_interface_expression(&fss.condition)?;
        }
        StatementInfo::Structure(ss) => {
            if ss.body.is_some() {
                return Err(statement.error("interface structures cannot have proof bodies"));
            }
            check_interface_type_params(&ss.type_params)?;
            for (_, field_type, _) in &ss.fields {
                check_interface_expression(field_type)?;
            }
            if let Some(constraint) = &ss.constraint {
                check_interface_expression(constraint)?;
            }
        }
        StatementInfo::Inductive(is) => {
            check_interface_type_params(&is.type_params)?;
            for (_, constructor, _) in &is.constructors {
                if let Some(constructor) = constructor {
                    check_interface_expression(constructor)?;
                }
            }
        }
        StatementInfo::Import(_) => {}
        StatementInfo::Attributes(attributes) => {
            check_interface_type_params(&attributes.type_params)?;
            for member in &mut attributes.body.statements {
                apply_interface_statement_mode(member, true)?;
            }
        }
        StatementInfo::Numerals(ns) => {
            check_interface_expression(&ns.type_expr)?;
        }
        StatementInfo::Match(ms) => {
            check_interface_expression(&ms.scrutinee)?;
            for (pattern, body) in &mut ms.cases {
                check_interface_expression(pattern)?;
                check_interface_body(body)?;
            }
        }
        StatementInfo::Typeclass(ts) => {
            for extend in &ts.extends {
                check_interface_expression(extend)?;
            }
            for (_, constant_type, _) in &ts.constants {
                check_interface_expression(constant_type)?;
            }
            for condition in &ts.conditions {
                check_interface_declarations(&condition.args)?;
                check_interface_expression(&condition.claim)?;
            }
        }
        StatementInfo::Instance(is) => {
            if is.body.is_some() {
                return Err(statement.error("interface instances cannot have proof bodies"));
            }
            check_interface_type_params(&is.type_params)?;
            check_interface_expression(&is.typeclass)?;
            if let Some(definitions) = &mut is.definitions {
                check_interface_instance_definitions(definitions)?;
            }
        }
        StatementInfo::Destructuring(ds) => {
            if ds.body.is_some() {
                return Err(statement.error("interfaces cannot contain by blocks"));
            }
            check_interface_expression(&ds.function)?;
            check_interface_expression(&ds.value)?;
        }
        StatementInfo::DocComment(_) => {}
    }
    Ok(())
}

fn check_interface_body(body: &mut Body) -> error::Result<()> {
    for statement in &mut body.statements {
        apply_interface_statement_mode(statement, false)?;
    }
    Ok(())
}

fn check_interface_instance_definitions(body: &mut Body) -> error::Result<()> {
    for statement in &mut body.statements {
        if !matches!(
            &statement.statement,
            StatementInfo::Let(_) | StatementInfo::Define(_)
        ) {
            return Err(
                statement.error("only let and define statements are allowed in instance bodies")
            );
        }
        apply_interface_statement_mode(statement, false)?;
    }
    Ok(())
}

fn check_interface_type_params(type_params: &[TypeParamExpr]) -> error::Result<()> {
    for type_param in type_params {
        if let Some(type_expr) = &type_param.type_expr {
            check_interface_expression(type_expr)?;
        }
        if let Some(typeclass) = &type_param.typeclass {
            check_interface_expression(typeclass)?;
        }
    }
    Ok(())
}

fn check_interface_declarations(declarations: &[Declaration]) -> error::Result<()> {
    for declaration in declarations {
        if let Declaration::Typed(_, type_expr) = declaration {
            check_interface_expression(type_expr)?;
        }
    }
    Ok(())
}

fn check_interface_expression(expression: &Expression) -> error::Result<()> {
    match expression {
        Expression::Singleton(_) => {}
        Expression::Unary(_, inner) => check_interface_expression(inner)?,
        Expression::Binary(left, _, right) => {
            check_interface_expression(left)?;
            check_interface_expression(right)?;
        }
        Expression::Concatenation(left, right) => {
            check_interface_expression(left)?;
            check_interface_expression(right)?;
        }
        Expression::Grouping(_, inner, _) => check_interface_expression(inner)?,
        Expression::Binder(_, declarations, body, _) => {
            check_interface_declarations(declarations)?;
            check_interface_expression(body)?;
        }
        Expression::GenericBinder(_, type_params, declarations, body, _) => {
            check_interface_type_params(type_params)?;
            check_interface_declarations(declarations)?;
            check_interface_expression(body)?;
        }
        Expression::IfThenElse(_, condition, then_branch, else_branch, _) => {
            check_interface_expression(condition)?;
            check_interface_expression(then_branch)?;
            if let Some(else_branch) = else_branch {
                check_interface_expression(else_branch)?;
            }
        }
        Expression::Match(_, scrutinee, cases, _) => {
            check_interface_expression(scrutinee)?;
            for (pattern, body) in cases {
                check_interface_expression(pattern)?;
                check_interface_expression(body)?;
            }
        }
        Expression::Block(items, result, _) => {
            for item in items {
                check_interface_local_item(item)?;
            }
            check_interface_expression(result)?;
        }
    }
    Ok(())
}

fn check_interface_local_item(item: &LocalBlockItem) -> error::Result<()> {
    match item {
        LocalBlockItem::Let(local_let) => {
            if local_let.body.is_some() {
                return Err(local_let
                    .let_token
                    .error("interfaces cannot contain by blocks"));
            }
            if let Some(type_expr) = &local_let.type_expr {
                check_interface_expression(type_expr)?;
            }
            check_interface_expression(&local_let.value)?;
        }
        LocalBlockItem::Satisfy(local_satisfy) => {
            if local_satisfy.body.is_some() {
                return Err(local_satisfy
                    .let_token
                    .error("interfaces cannot contain by blocks"));
            }
            check_interface_expression(&local_satisfy.type_expr)?;
            check_interface_expression(&local_satisfy.condition)?;
        }
        LocalBlockItem::Destructuring(local_destructuring) => {
            if local_destructuring.body.is_some() {
                return Err(local_destructuring
                    .let_token
                    .error("interfaces cannot contain by blocks"));
            }
            check_interface_expression(&local_destructuring.function)?;
            check_interface_expression(&local_destructuring.value)?;
        }
    }
    Ok(())
}

fn import_module_name(import: &ImportStatement) -> String {
    import
        .components
        .iter()
        .map(|token| token.text().to_string())
        .collect::<Vec<_>>()
        .join(".")
}

fn module_name_from_expression(expression: &Expression) -> Option<String> {
    match expression {
        Expression::Singleton(token) if token.token_type == TokenType::Identifier => {
            Some(token.text().to_string())
        }
        Expression::Binary(left, token, right) if token.token_type == TokenType::Dot => {
            let left_name = module_name_from_expression(left)?;
            let Expression::Singleton(token) = right.as_ref() else {
                return None;
            };
            if token.token_type != TokenType::Identifier {
                return None;
            }
            Some(format!("{}.{}", left_name, token.text()))
        }
        _ => None,
    }
}

fn collect_dependencies_from_type_param(
    type_param: &TypeParamExpr,
    output: &mut DependencyCollector,
) {
    if let Some(type_expr) = &type_param.type_expr {
        collect_dependencies_from_expression(type_expr, output);
    }
    if let Some(typeclass) = &type_param.typeclass {
        collect_dependencies_from_expression(typeclass, output);
    }
}

fn collect_dependencies_from_declaration(
    declaration: &Declaration,
    output: &mut DependencyCollector,
) {
    if let Declaration::Typed(_, type_expr) = declaration {
        collect_dependencies_from_expression(type_expr, output);
    }
}

fn collect_dependencies_from_expression(expression: &Expression, output: &mut DependencyCollector) {
    match expression {
        Expression::Singleton(_) => {}
        Expression::Unary(_, subexpression) => {
            collect_dependencies_from_expression(subexpression, output);
        }
        Expression::Binary(left, _, right) => {
            collect_dependencies_from_expression(left, output);
            collect_dependencies_from_expression(right, output);
        }
        Expression::Concatenation(left, right) => {
            if let Expression::Singleton(token) = left.as_ref() {
                if token.token_type == TokenType::Lib {
                    if let Expression::Grouping(_, module_expr, _) = right.as_ref() {
                        if let Some(module_name) = module_name_from_expression(module_expr) {
                            output.add_implicit_lib(module_name);
                        }
                    }
                }
            }
            collect_dependencies_from_expression(left, output);
            collect_dependencies_from_expression(right, output);
        }
        Expression::Grouping(_, inner, _) => {
            collect_dependencies_from_expression(inner, output);
        }
        Expression::Binder(_, declarations, body, _) => {
            for declaration in declarations {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_expression(body, output);
        }
        Expression::GenericBinder(_, type_params, declarations, body, _) => {
            for type_param in type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for declaration in declarations {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_expression(body, output);
        }
        Expression::IfThenElse(_, cond, if_block, else_block, _) => {
            collect_dependencies_from_expression(cond, output);
            collect_dependencies_from_expression(if_block, output);
            if let Some(else_block) = else_block {
                collect_dependencies_from_expression(else_block, output);
            }
        }
        Expression::Match(_, scrutinee, cases, _) => {
            collect_dependencies_from_expression(scrutinee, output);
            for (pattern, result) in cases {
                collect_dependencies_from_expression(pattern, output);
                collect_dependencies_from_expression(result, output);
            }
        }
        Expression::Block(local_lets, body, _) => {
            for local_item in local_lets {
                match local_item {
                    LocalBlockItem::Let(local_let) => {
                        if let Some(type_expr) = &local_let.type_expr {
                            collect_dependencies_from_expression(type_expr, output);
                        }
                        collect_dependencies_from_expression(&local_let.value, output);
                        if let Some(body) = &local_let.body {
                            collect_dependencies_from_body(body, output);
                        }
                    }
                    LocalBlockItem::Satisfy(local_satisfy) => {
                        collect_dependencies_from_expression(&local_satisfy.type_expr, output);
                        collect_dependencies_from_expression(&local_satisfy.condition, output);
                        if let Some(body) = &local_satisfy.body {
                            collect_dependencies_from_body(body, output);
                        }
                    }
                    LocalBlockItem::Destructuring(local_destructuring) => {
                        collect_dependencies_from_expression(&local_destructuring.function, output);
                        collect_dependencies_from_expression(&local_destructuring.value, output);
                        if let Some(body) = &local_destructuring.body {
                            collect_dependencies_from_body(body, output);
                        }
                    }
                }
            }
            collect_dependencies_from_expression(body, output);
        }
    }
}

fn collect_dependencies_from_body(body: &Body, output: &mut DependencyCollector) {
    for statement in &body.statements {
        collect_dependencies_from_statement(statement, output);
    }
}

fn collect_dependencies_from_statement(statement: &Statement, output: &mut DependencyCollector) {
    match &statement.statement {
        StatementInfo::Let(ls) => {
            for type_param in &ls.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            if let Some(type_expr) = &ls.type_expr {
                collect_dependencies_from_expression(type_expr, output);
            }
            collect_dependencies_from_expression(&ls.value, output);
        }
        StatementInfo::Define(ds) => {
            for type_param in &ds.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for declaration in &ds.args {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_expression(&ds.return_type, output);
            collect_dependencies_from_expression(&ds.return_value, output);
        }
        StatementInfo::Theorem(ts) => {
            for type_param in &ts.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for declaration in &ts.args {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_expression(&ts.claim, output);
            if let Some(body) = &ts.body {
                collect_dependencies_from_body(body, output);
            }
        }
        StatementInfo::Claim(cs) => {
            collect_dependencies_from_expression(&cs.claim, output);
        }
        StatementInfo::Type(ts) => {
            for type_param in &ts.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            collect_dependencies_from_expression(&ts.type_expr, output);
        }
        StatementInfo::ForAll(fas) => {
            for declaration in &fas.quantifiers {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_body(&fas.body, output);
        }
        StatementInfo::If(is) => {
            collect_dependencies_from_expression(&is.condition, output);
            collect_dependencies_from_body(&is.body, output);
            if let Some(else_body) = &is.else_body {
                collect_dependencies_from_body(else_body, output);
            }
        }
        StatementInfo::VariableSatisfy(vss) => {
            for type_param in &vss.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for declaration in &vss.declarations {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_expression(&vss.condition, output);
        }
        StatementInfo::FunctionSatisfy(fss) => {
            for type_param in &fss.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for declaration in &fss.declarations {
                collect_dependencies_from_declaration(declaration, output);
            }
            collect_dependencies_from_expression(&fss.condition, output);
            if let Some(body) = &fss.body {
                collect_dependencies_from_body(body, output);
            }
        }
        StatementInfo::Structure(ss) => {
            for type_param in &ss.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for (_, field_type, _) in &ss.fields {
                collect_dependencies_from_expression(field_type, output);
            }
            if let Some(constraint) = &ss.constraint {
                collect_dependencies_from_expression(constraint, output);
            }
            if let Some(body) = &ss.body {
                collect_dependencies_from_body(body, output);
            }
        }
        StatementInfo::Inductive(is) => {
            for type_param in &is.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            for (_, constructor, _) in &is.constructors {
                if let Some(constructor) = constructor {
                    collect_dependencies_from_expression(constructor, output);
                }
            }
        }
        StatementInfo::Import(import) => {
            output.add_explicit_import(import_module_name(import));
        }
        StatementInfo::Attributes(as_) => {
            for type_param in &as_.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            collect_dependencies_from_body(&as_.body, output);
        }
        StatementInfo::Numerals(ns) => {
            collect_dependencies_from_expression(&ns.type_expr, output);
        }
        StatementInfo::Match(ms) => {
            collect_dependencies_from_expression(&ms.scrutinee, output);
            for (pattern, body) in &ms.cases {
                collect_dependencies_from_expression(pattern, output);
                collect_dependencies_from_body(body, output);
            }
        }
        StatementInfo::Typeclass(ts) => {
            for extend in &ts.extends {
                collect_dependencies_from_expression(extend, output);
            }
            for (_, constant_type, _) in &ts.constants {
                collect_dependencies_from_expression(constant_type, output);
            }
            for condition in &ts.conditions {
                for declaration in &condition.args {
                    collect_dependencies_from_declaration(declaration, output);
                }
                collect_dependencies_from_expression(&condition.claim, output);
            }
        }
        StatementInfo::Instance(is) => {
            for type_param in &is.type_params {
                collect_dependencies_from_type_param(type_param, output);
            }
            collect_dependencies_from_expression(&is.typeclass, output);
            if let Some(definitions) = &is.definitions {
                collect_dependencies_from_body(definitions, output);
            }
            if let Some(body) = &is.body {
                collect_dependencies_from_body(body, output);
            }
        }
        StatementInfo::Destructuring(ds) => {
            collect_dependencies_from_expression(&ds.function, output);
            collect_dependencies_from_expression(&ds.value, output);
        }
        StatementInfo::DocComment(_) => {}
    }
}

fn parse_module_statements(text: &str, strict: bool) -> error::Result<Vec<Statement>> {
    let mut tokens = TokenIter::new(Token::scan(text));
    let mut statements = vec![];
    loop {
        match Statement::parse(&mut tokens, false, strict) {
            Ok((Some(statement), _)) => statements.push(statement),
            Ok((None, _)) => return Ok(statements),
            Err(error) => return Err(error),
        }
    }
}

fn is_exported_declaration_statement(statement: &Statement) -> bool {
    match &statement.statement {
        StatementInfo::Theorem(theorem) => !theorem.lemma,
        StatementInfo::Let(_)
        | StatementInfo::Define(_)
        | StatementInfo::Type(_)
        | StatementInfo::Structure(_)
        | StatementInfo::Inductive(_)
        | StatementInfo::Typeclass(_)
        | StatementInfo::Instance(_) => true,
        _ => false,
    }
}

fn check_exported_declaration_limit(statements: &[Statement]) -> error::Result<()> {
    let mut exported_declarations = 0;
    for statement in statements {
        if !is_exported_declaration_statement(statement) {
            continue;
        }
        exported_declarations += 1;
        if exported_declarations > MAX_EXPORTED_DECLARATIONS_PER_MODULE {
            return Err(statement.error(&format!(
                "module has more than {} exported declarations",
                MAX_EXPORTED_DECLARATIONS_PER_MODULE
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn theorem_module(count: usize) -> String {
        let mut text = String::new();
        for i in 0..count {
            text.push_str(&format!("theorem t{} {{ true }}\n", i));
        }
        text
    }

    fn parse(text: &str) -> ParsedModule {
        ParsedModule::parse(ModuleDescriptor::name("main"), text.to_string(), false).unwrap()
    }

    #[test]
    fn exported_declaration_limit_allows_500() {
        let text = theorem_module(MAX_EXPORTED_DECLARATIONS_PER_MODULE);
        ParsedModule::parse(ModuleDescriptor::name("main"), text, false).unwrap();
    }

    #[test]
    fn exported_declaration_limit_rejects_501() {
        let text = theorem_module(MAX_EXPORTED_DECLARATIONS_PER_MODULE + 1);
        let error = match ParsedModule::parse(ModuleDescriptor::name("main"), text, false) {
            Ok(_) => panic!("expected exported declaration limit error"),
            Err(error) => error,
        };
        assert!(error
            .to_string()
            .contains("module has more than 500 exported declarations"));
    }

    #[test]
    fn explicit_imports_are_dependencies_but_not_implicit_lib_dependencies() {
        let parsed = parse("from dep.mod import value\ntheorem goal { true }\n");
        assert_eq!(parsed.dependency_names, vec!["dep.mod"]);
        assert!(parsed.implicit_lib_dependency_names.is_empty());
    }

    #[test]
    fn nested_explicit_imports_are_dependencies() {
        let parsed = parse(indoc::indoc! {"
            if true {
                from helper import fact
            }
        "});
        assert_eq!(parsed.dependency_names, vec!["helper"]);
    }

    #[test]
    fn implicit_lib_references_are_tracked_separately() {
        let parsed = parse("theorem goal { lib(helper.mod).fact }\n");
        assert_eq!(parsed.dependency_names, vec!["helper.mod"]);
        assert_eq!(parsed.implicit_lib_dependency_names, vec!["helper.mod"]);
    }

    #[test]
    fn dependencies_keep_first_seen_order() {
        let parsed = parse(indoc::indoc! {"
            from zed import z
            theorem goal { lib(alpha).fact }
            from alpha import a
            from mid import m
        "});
        assert_eq!(parsed.dependency_names, vec!["zed", "alpha", "mid"]);
        assert_eq!(parsed.implicit_lib_dependency_names, vec!["alpha"]);
    }
}
