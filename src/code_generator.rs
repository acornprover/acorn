use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::{LanguageString, MarkedString};

use crate::acorn_type::{AcornType, Datatype, PotentialType, Typeclass};
use crate::acorn_value::{AcornValue, BinaryOp, ConstantInstance};
use crate::atom::AtomId;
use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::expression::{Declaration, Expression};
use crate::module::ModuleId;
use crate::names::{ConstantName, DefinedName};
use crate::normalizer::Normalizer;
use crate::proof::ConcreteStep;
use crate::term::{Term, TypeId};
use crate::token::TokenType;
use crate::type_unifier::TypeclassRegistry;
use crate::variable_map::VariableMap;

pub type Result<T> = std::result::Result<T, Error>;

pub struct CodeGenerator<'a> {
    /// Bindings for the module we are generating code in.
    bindings: &'a BindingMap,

    /// We use variables named x0, x1, x2, etc for universal variables.
    next_x: u32,

    /// We use variables named k0, k1, k2, etc for existential variables.
    next_k: u32,

    /// We use variables named s0, s1, s2, etc for synthetic atoms.
    next_s: u32,

    /// The names we have assigned to stack variables so far.
    var_names: Vec<String>,

    /// The names we have assigned to synthetic atoms so far.
    synthetic_names: HashMap<AtomId, String>,

    /// The names for whenever we need an arbitrary member of a type.
    arbitrary_names: HashMap<TypeId, ConstantName>,
}

impl CodeGenerator<'_> {
    /// Creates a new code generator.
    pub fn new(bindings: &BindingMap) -> CodeGenerator {
        CodeGenerator {
            bindings,
            next_x: 0,
            next_k: 0,
            next_s: 0,
            var_names: vec![],
            synthetic_names: HashMap::new(),
            arbitrary_names: HashMap::new(),
        }
    }

    pub fn marked(code: String) -> MarkedString {
        MarkedString::LanguageString(LanguageString {
            language: "acorn".to_string(),
            value: code.to_string(),
        })
    }

    /// Converts a ModuleId to an Expression representing that module.
    fn module_to_expr(&self, module_id: ModuleId) -> Result<Expression> {
        let Some(info) = self.bindings.get_module_info(module_id) else {
            return Err(Error::internal("reference to unreferenceable module"));
        };
        if let Some(local_name) = &info.local_name {
            return Ok(Expression::generate_identifier(local_name));
        };

        // Generate lib(module) syntax
        // Build the dot-separated module path expression
        let parts: Vec<&str> = info.full_name.iter().map(|s| s.as_str()).collect();
        let path_expr = Expression::generate_identifier_chain(&parts);
        let lib_expr = Expression::generate_lib();
        let args_expr = Expression::Grouping(
            TokenType::LeftParen.new_token("("),
            Box::new(path_expr),
            TokenType::RightParen.new_token(")"),
        );
        Ok(Expression::Concatenation(
            Box::new(lib_expr),
            Box::new(args_expr),
        ))
    }

    fn datatype_to_expr(&self, datatype: &Datatype) -> Result<Expression> {
        if datatype.module_id == self.bindings.module_id() {
            return Ok(Expression::generate_identifier(&datatype.name));
        }

        // Check if we have an alias
        if let Some(alias) = self.bindings.datatype_alias(&datatype) {
            return Ok(Expression::generate_identifier(alias));
        }

        // Reference this type via referencing the imported module
        let module = self.module_to_expr(datatype.module_id)?;
        Ok(module.add_dot_str(&datatype.name))
    }

    /// Returns an error if this type can't be encoded as an expression.
    /// This will happen when it's defined in a module that isn't directly imported.
    /// In theory we could fix this, but we would have to have a way to suggest imports.
    /// There are probably other error cases.
    pub fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression> {
        // Check if there's a local name for this exact type
        if let Some(name) = self
            .bindings
            .get_typename_for_type(&PotentialType::Resolved(acorn_type.clone()))
        {
            return Ok(Expression::generate_identifier(name));
        }

        match acorn_type {
            AcornType::Data(datatype, params) => {
                let base_expr = self.datatype_to_expr(datatype)?;

                self.parametrize_expr(base_expr, params)
            }
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                Ok(Expression::generate_identifier(&param.name))
            }
            AcornType::Function(ft) => {
                let mut args = vec![];
                for arg_type in &ft.arg_types {
                    args.push(self.type_to_expr(arg_type)?);
                }
                let lhs = if args.len() == 1 {
                    args.pop().unwrap()
                } else {
                    Expression::generate_paren_grouping(args)
                };
                let rhs = self.type_to_expr(&ft.return_type)?;
                Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::RightArrow.generate(),
                    Box::new(rhs),
                ))
            }
            AcornType::Empty => Err(Error::internal("empty type generated")),
            AcornType::Bool => Err(Error::internal("Bool unbound")),
        }
    }

    /// Adds parameters, if there are any, to an expression representing a type.
    fn parametrize_expr(&self, base_expr: Expression, params: &[AcornType]) -> Result<Expression> {
        if params.is_empty() {
            return Ok(base_expr);
        }
        let mut param_exprs = vec![];
        for param in params {
            param_exprs.push(self.type_to_expr(&param)?);
        }
        let params_expr = Expression::generate_params(param_exprs);
        let applied = Expression::Concatenation(Box::new(base_expr), Box::new(params_expr));
        Ok(applied)
    }

    /// If this value cannot be expressed in a single chunk of code, returns an error.
    /// For example, it might refer to a constant that is not in scope.
    pub fn value_to_code(&mut self, value: &AcornValue) -> Result<String> {
        let expr = self.value_to_expr(value, false)?;
        Ok(expr.to_string())
    }

    /// Generates definitions for the given synthetic atom IDs and appends them to codes.
    /// Updates self.synthetic_names with names for all provided synthetic atom IDs.
    fn define_synthetics(
        &mut self,
        skolem_ids: Vec<AtomId>,
        normalizer: &Normalizer,
        codes: &mut Vec<String>,
    ) -> Result<()> {
        // TODO: currently all synthetics are skolems, so we can assume this catches all of them,
        // but we need to change that.
        let infos = normalizer.find_covering_synthetic_info(&skolem_ids);
        for info in &infos {
            let mut decl = vec![];
            for id in &info.atoms {
                if self.synthetic_names.contains_key(id) {
                    // We already have a name for this synthetic atom
                    continue;
                }
                let name = self.bindings.next_indexed_var('s', &mut self.next_s);
                self.synthetic_names.insert(*id, name.clone());
                decl.push((name, normalizer.get_synthetic_type(*id).clone()));
            }
            if decl.is_empty() {
                continue;
            }

            // Create code for the declaration
            let mut decl_parts = vec![];
            for (name, ty) in decl {
                let ty_code = self.type_to_code(&ty)?;
                decl_parts.push(format!("{}: {}", name, ty_code));
            }
            let decl = if decl_parts.len() > 1 {
                format!("({})", decl_parts.join(", "))
            } else {
                decl_parts.join("")
            };

            // Create code for the condition
            let mut cond_parts = vec![];
            for clause in &info.clauses {
                let part = normalizer.denormalize(&clause, None);
                cond_parts.push(part);
            }
            let cond_val = AcornValue::reduce(BinaryOp::And, cond_parts);
            let cond = self.value_to_code(&cond_val)?;

            let let_statement = format!("let {} satisfy {{ {} }}", decl, cond);
            codes.push(let_statement);
        }
        Ok(())
    }

    /// Convert to a clause to code strings.
    /// This will generate synthetic atom definitions if necessary.
    /// Appends let statements that define arbitrary variables and synthetic atoms to definitions,
    /// and appends the actual clause content to codes.
    fn specialization_to_code(
        &mut self,
        generic: &Clause,
        var_map: &VariableMap,
        normalizer: &Normalizer,
        definitions: &mut Vec<String>,
        codes: &mut Vec<String>,
    ) -> Result<()> {
        let clause = var_map.specialize_clause(&generic);
        self.add_arbitrary_for_clause(&clause);
        let mut value = normalizer.denormalize(&clause, Some(&self.arbitrary_names));

        // Define the arbitrary variables.
        for (ty, name) in self.arbitrary_names.clone() {
            let ty_code = self.type_to_code(&normalizer.denormalize_type(ty))?;
            let decl = format!("let {}: {} satisfy {{ true }}", name, ty_code);
            definitions.push(decl);
        }

        // Create a name and definition for each synthetic atom.
        let synthetic_ids = value.find_synthetics();
        self.define_synthetics(synthetic_ids, normalizer, definitions)?;

        value = value.replace_synthetics(self.bindings.module_id(), &self.synthetic_names);
        let subvalues = value.remove_and();
        for subvalue in subvalues {
            codes.push(self.value_to_code(&subvalue)?);
        }
        Ok(())
    }

    /// Converts a ConcreteStep to code.
    /// Returns (definitions, code) where definitions are let statements that define
    /// arbitrary variables and synthetic atoms, and code is the actual clause content.
    pub fn concrete_step_to_code(
        &mut self,
        step: &ConcreteStep,
        normalizer: &Normalizer,
    ) -> Result<(Vec<String>, Vec<String>)> {
        let mut defs = vec![];
        let mut codes = vec![];
        for var_map in &step.var_maps {
            self.specialization_to_code(&step.generic, var_map, normalizer, &mut defs, &mut codes)?;
        }
        defs.sort();
        codes.sort();
        Ok((defs, codes))
    }

    fn type_to_code(&mut self, acorn_type: &AcornType) -> Result<String> {
        let expr = self.type_to_expr(acorn_type)?;
        Ok(expr.to_string())
    }

    fn add_arbitrary_for_term(&mut self, term: &Term) {
        if term.is_variable() {
            let type_id = term.head_type;
            if !self.arbitrary_names.contains_key(&type_id) {
                // Generate a name for this arbitrary value
                let name = self.bindings.next_indexed_var('s', &mut self.next_s);
                let cname = ConstantName::Unqualified(self.bindings.module_id(), name);
                self.arbitrary_names.insert(type_id, cname);
            }
        }
        for arg in &term.args {
            self.add_arbitrary_for_term(arg);
        }
    }

    /// For any variables in this clause, add an arbitrary variable.
    fn add_arbitrary_for_clause(&mut self, clause: &Clause) {
        for literal in &clause.literals {
            for term in [&literal.left, &literal.right] {
                self.add_arbitrary_for_term(term);
            }
        }
    }

    /// Check if we can infer a function's type parameters from its argument types.
    ///
    /// The key insight: if a function foo[P, Q] takes argument of type P,
    /// we can't infer Q from just the argument. So we need explicit parameters.
    fn can_infer_type_params_from_args(&self, function: &AcornValue, args: &[AcornValue]) -> bool {
        // Get the constant and its parameters
        let constant = match function {
            AcornValue::Constant(c) => c,
            _ => return true, // Not a generic constant, inference doesn't apply
        };

        if constant.params.is_empty() {
            return true; // No parameters to infer
        }

        // Get the function type
        let function_type = function.get_type();
        let fn_type = match &function_type {
            AcornType::Function(ft) => ft,
            _ => return false, // Not a function type, can't infer
        };

        // For each type parameter, check if it appears in the argument types
        // in a way that would allow inference
        for param_type in &constant.params {
            let mut found_in_args = false;

            // Check each argument type to see if this parameter appears
            for (i, _arg) in args.iter().enumerate() {
                if let Some(expected_arg_type) = fn_type.arg_types.get(i) {
                    // Check if the parameter appears in this argument position
                    // For simplicity, we just check direct equality
                    if param_type == expected_arg_type {
                        found_in_args = true;
                        break;
                    }
                }
            }

            if !found_in_args {
                // This parameter doesn't appear in arguments, can't infer
                return false;
            }
        }

        true
    }

    /// Create a marked-up string to display information for this value.
    pub fn value_to_marked(&mut self, value: &AcornValue) -> Result<MarkedString> {
        let value_code = self.value_to_code(value)?;
        let type_code = self.type_to_code(&value.get_type())?;
        let code = format!("{}: {}", value_code, type_code);
        Ok(Self::marked(code))
    }

    /// Create a marked-up string to display information for this type.
    pub fn type_to_marked(&mut self, acorn_type: &AcornType) -> Result<MarkedString> {
        let code = self.type_to_code(acorn_type)?;
        Ok(Self::marked(format!("type {}", code)))
    }

    /// Given a constant instance, create an expression that refers to it.
    /// This does *not* include the parameters.
    fn const_to_expr(&self, ci: &ConstantInstance) -> Result<Expression> {
        if ci.name.is_synthetic() {
            if let Some(id) = ci.name.synthetic_id() {
                if let Some(synthetic_name) = self.synthetic_names.get(&id) {
                    return Ok(Expression::generate_identifier(synthetic_name));
                }
            }
            return Err(Error::synthetic(&ci.name.to_string()));
        }

        // Handle numeric literals
        if let Some((_, datatype_name, attr)) = ci.name.as_attribute() {
            if attr.chars().all(|ch| ch.is_ascii_digit()) {
                let datatype = Datatype {
                    module_id: ci.name.module_id(),
                    name: datatype_name.to_string(),
                };

                let numeral = TokenType::Numeral.new_token(&attr);

                // If it's the default type, we don't need to scope it
                if self.bindings.numerals() == Some(&datatype) {
                    return Ok(Expression::Singleton(numeral));
                }

                // Otherwise, we need to scope it by the type
                let numeric_type = self.datatype_to_expr(&datatype)?;
                return Ok(Expression::generate_dot(
                    numeric_type,
                    Expression::Singleton(numeral),
                ));
            }
        }

        // Handle local constants
        if ci.name.module_id() == self.bindings.module_id() {
            return Ok(match &ci.name {
                ConstantName::Unqualified(_, word) => Expression::generate_identifier(word),
                ConstantName::DatatypeAttribute(datatype, attr) => {
                    Expression::generate_identifier(&datatype.name).add_dot_str(attr)
                }
                ConstantName::TypeclassAttribute(tc, attr) => {
                    Expression::generate_identifier(&tc.name).add_dot_str(attr)
                }
                ConstantName::Synthetic(_) => panic!("control should not get here"),
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.bindings.constant_alias(&ci.name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let Some((_, rname, attr)) = ci.name.as_attribute() {
            // Check if this is a datatype attribute
            let datatype = Datatype {
                module_id: ci.name.module_id(),
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.datatype_alias(&datatype) {
                let lhs = Expression::generate_identifier(alias);
                return Ok(lhs.add_dot_str(attr));
            }

            // Check if this is a typeclass attribute
            let typeclass = Typeclass {
                module_id: ci.name.module_id(),
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.typeclass_alias(&typeclass) {
                let lhs = Expression::generate_identifier(alias);
                return Ok(lhs.add_dot_str(attr));
            }
        }

        // Refer to this constant using its module
        let module = self.module_to_expr(ci.name.module_id())?;
        match &ci.name {
            ConstantName::Unqualified(_, name) => Ok(module.add_dot_str(name)),
            ConstantName::DatatypeAttribute(datatype, attr) => {
                Ok(module.add_dot_str(&datatype.name).add_dot_str(attr))
            }
            ConstantName::TypeclassAttribute(tc, attr) => {
                Ok(module.add_dot_str(&tc.name).add_dot_str(attr))
            }
            ConstantName::Synthetic(_) => panic!("control should not get here"),
        }
    }

    /// If use_x is true we use x-variables; otherwise we use k-variables.
    fn generate_quantifier_expr(
        &mut self,
        token_type: TokenType,
        quants: &Vec<AcornType>,
        value: &AcornValue,
        use_x: bool,
    ) -> Result<Expression> {
        let initial_var_names_len = self.var_names.len();
        let mut decls = vec![];
        for arg_type in quants {
            let var_name = if use_x {
                self.bindings.next_indexed_var('x', &mut self.next_x)
            } else {
                self.bindings.next_indexed_var('k', &mut self.next_k)
            };
            let name_token = TokenType::Identifier.new_token(&var_name);
            self.var_names.push(var_name);
            let type_expr = self.type_to_expr(arg_type)?;
            let var_name = Declaration::Typed(name_token, type_expr);
            let decl = var_name;
            decls.push(decl);
        }
        let subresult = self.value_to_expr(value, false)?;
        self.var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    /// Convert an AcornValue to an Expression.
    /// var_names is the names we have assigned to indexed variables so far.
    /// We automatically generate variable names sometimes, using next_x and next_k.
    /// "inferrable" is true if the type of this value can be inferred, which means
    /// we don't need top level parameters.
    fn value_to_expr(&mut self, value: &AcornValue, inferrable: bool) -> Result<Expression> {
        match value {
            AcornValue::Variable(i, _) => {
                if *i >= self.var_names.len() as u16 {
                    // This is definitely wrong.
                    // We use this for the hover, but it would be better to fix it.
                    Ok(Expression::generate_identifier(&format!("v{}", i)))
                } else {
                    Ok(Expression::generate_identifier(
                        &self.var_names[*i as usize],
                    ))
                }
            }
            AcornValue::Application(fa) => {
                let mut arg_exprs = vec![];
                for arg in &fa.args {
                    // We currently never infer the type of arguments from the type of the function.
                    // Inference only goes the other way.
                    // We could improve this at some point.
                    arg_exprs.push(self.value_to_expr(arg, false)?);
                }

                // Check if we could replace this with receiver+attribute syntax
                let receiver_type = fa.args[0].get_type();
                if let Some((module_id, entity, attr)) = fa.function.as_attribute() {
                    let is_typeclass_instance =
                        if let AcornValue::Constant(c) = fa.function.as_ref() {
                            if let ConstantName::TypeclassAttribute(typeclass, _) = &c.name {
                                if let AcornType::Data(datatype, _) = &receiver_type {
                                    if self.bindings.is_instance_of(datatype, typeclass) {
                                        // Check if the datatype has its own attribute with the same name
                                        let datatype_attr_name =
                                            DefinedName::datatype_attr(datatype, &attr);
                                        !self.bindings.constant_name_in_use(&datatype_attr_name)
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        } else {
                            false
                        };

                    let use_receiver_syntax =
                        self.bindings
                            .inherits_attributes(&receiver_type, module_id, entity)
                            || is_typeclass_instance;

                    if use_receiver_syntax {
                        // We can use receiver+attribute syntax
                        if arg_exprs.len() == 1 {
                            // Prefix operators
                            if let Some(op) = TokenType::from_prefix_magic_method_name(&attr) {
                                return Ok(Expression::generate_unary(
                                    op,
                                    arg_exprs.pop().unwrap(),
                                ));
                            }
                        }

                        if arg_exprs.len() == 2 {
                            // Infix operators
                            if let Some(op) = TokenType::from_infix_magic_method_name(&attr) {
                                let right = arg_exprs.pop().unwrap();
                                let left = arg_exprs.pop().unwrap();
                                return Ok(Expression::generate_binary(left, op, right));
                            }

                            // Long numeric literals
                            if attr == "read" && arg_exprs[0].is_number() {
                                if let Some(digit) = arg_exprs[1].to_digit() {
                                    let left = arg_exprs.remove(0);
                                    return Ok(Expression::generate_number(left, digit));
                                }
                            }
                        }

                        // General member functions
                        let instance = arg_exprs.remove(0);
                        let bound = Expression::generate_binary(
                            instance,
                            TokenType::Dot,
                            Expression::generate_identifier(&attr),
                        );
                        if arg_exprs.len() == 0 {
                            // Like foo.bar
                            return Ok(bound);
                        } else {
                            // Like foo.bar(baz, qux)
                            let applied = Expression::Concatenation(
                                Box::new(bound),
                                Box::new(Expression::generate_paren_grouping(arg_exprs)),
                            );
                            return Ok(applied);
                        }
                    }
                }

                // For overridden typeclass attributes, we need explicit parameters
                // to distinguish from the datatype's own attributes
                let inferrable = if let AcornValue::Constant(c) = fa.function.as_ref() {
                    if let ConstantName::TypeclassAttribute(typeclass, attr_name) = &c.name {
                        if let AcornType::Data(datatype, _) = &receiver_type {
                            if self.bindings.is_instance_of(datatype, typeclass) {
                                let datatype_attr_name =
                                    DefinedName::datatype_attr(datatype, attr_name);
                                // If the datatype has its own attribute, don't infer parameters
                                !self.bindings.constant_name_in_use(&datatype_attr_name)
                            } else {
                                true
                            }
                        } else {
                            true
                        }
                    } else {
                        // For regular functions, check if we can infer type parameters from arguments
                        self.can_infer_type_params_from_args(&fa.function, &fa.args)
                    }
                } else {
                    true
                };
                let f = self.value_to_expr(&fa.function, inferrable)?;
                let grouped_args = Expression::generate_paren_grouping(arg_exprs);
                Ok(Expression::Concatenation(
                    Box::new(f),
                    Box::new(grouped_args),
                ))
            }
            AcornValue::Binary(op, left, right) => {
                let mut left_expr = self.value_to_expr(left, false)?;
                let mut right_expr = self.value_to_expr(right, false)?;
                let token = op.token_type().generate();

                if let AcornValue::Binary(left_op, _, _) = left.as_ref() {
                    if left_op.token_type().binary_precedence()
                        < op.token_type().binary_precedence()
                    {
                        // We want the left op to happen first, but its precedence is lower.
                        // So we wrap the left expression in parentheses.
                        let open = TokenType::LeftParen.generate();
                        let close = TokenType::RightParen.generate();
                        left_expr = Expression::Grouping(open, Box::new(left_expr), close);
                    }
                }

                if let AcornValue::Binary(right_op, _, _) = right.as_ref() {
                    if right_op.token_type().binary_precedence()
                        <= op.token_type().binary_precedence()
                    {
                        // We want the right op to happen first, but its precedence is not higher.
                        // So we wrap the right expression in parentheses.
                        let open = TokenType::LeftParen.generate();
                        let close = TokenType::RightParen.generate();
                        right_expr = Expression::Grouping(open, Box::new(right_expr), close);
                    }
                }

                Ok(Expression::Binary(
                    Box::new(left_expr),
                    token,
                    Box::new(right_expr),
                ))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, false)?;
                Ok(Expression::generate_unary(TokenType::Not, x))
            }
            AcornValue::ForAll(quants, value) => {
                self.generate_quantifier_expr(TokenType::ForAll, quants, value, true)
            }
            AcornValue::Exists(quants, value) => {
                self.generate_quantifier_expr(TokenType::Exists, quants, value, false)
            }
            AcornValue::Lambda(quants, value) => {
                self.generate_quantifier_expr(TokenType::Function, quants, value, true)
            }
            AcornValue::Bool(b) => {
                let token = if *b {
                    TokenType::True.generate()
                } else {
                    TokenType::False.generate()
                };
                Ok(Expression::Singleton(token))
            }
            AcornValue::Constant(c) => {
                if c.params.len() == 1 {
                    if let Some((module_id, entity, attr)) = c.name.as_attribute() {
                        if self
                            .bindings
                            .inherits_attributes(&c.params[0], module_id, entity)
                        {
                            // We can use receiver+attribute syntax
                            let lhs = self.type_to_expr(&c.params[0])?;
                            let rhs = Expression::generate_identifier(&attr);
                            return Ok(Expression::generate_dot(lhs, rhs));
                        }

                        // Check if this is a typeclass attribute being accessed on an instance type
                        if let ConstantName::TypeclassAttribute(typeclass, _) = &c.name {
                            if let AcornType::Data(datatype, _) = &c.params[0] {
                                if self.bindings.is_instance_of(datatype, typeclass) {
                                    // Check if the datatype has its own attribute with the same name
                                    let datatype_attr_name =
                                        DefinedName::datatype_attr(datatype, &attr);
                                    if !self.bindings.constant_name_in_use(&datatype_attr_name) {
                                        // Generate DataType.attribute instead of Typeclass.attribute[DataType]
                                        // only if the datatype doesn't override this attribute
                                        let lhs = self.type_to_expr(&c.params[0])?;
                                        let rhs = Expression::generate_identifier(&attr);
                                        return Ok(Expression::generate_dot(lhs, rhs));
                                    }
                                }
                            }
                        }
                    }
                }

                let const_expr = self.const_to_expr(&c)?;

                if !inferrable && !c.params.is_empty() {
                    self.parametrize_expr(const_expr, &c.params)
                } else {
                    // We don't need to parametrize because it can be inferred
                    Ok(const_expr)
                }
            }
            AcornValue::IfThenElse(condition, if_value, else_value) => {
                let condition = self.value_to_expr(condition, false)?;
                let if_value = self.value_to_expr(if_value, false)?;
                let else_value = self.value_to_expr(else_value, false)?;
                Ok(Expression::IfThenElse(
                    TokenType::If.generate(),
                    Box::new(condition),
                    Box::new(if_value),
                    Some(Box::new(else_value)),
                    TokenType::RightBrace.generate(),
                ))
            }
            AcornValue::Match(_scrutinee, _cases) => {
                todo!("codegen match expressions");
            }
        }
    }

    /// For testing. Panics if generating code for this value does not give expected.
    pub fn expect(bindings: &BindingMap, input: &str, value: &AcornValue, expected: &str) {
        let output = match CodeGenerator::new(bindings).value_to_code(&value) {
            Ok(output) => output,
            Err(e) => panic!("code generation error: {}", e),
        };

        if output != expected {
            panic!(
                "\nconverted:\n  {}\nto value:\n  {}\nand back to:\n  {}\nbut expected:\n  {}\n",
                input, value, output, expected
            );
        }
    }
}

#[derive(Debug)]
pub enum Error {
    // Trouble expressing a synthetic atom created during normalization.
    Synthetic(String),

    // Trouble referencing a module that has not been directly imported.
    UnimportedModule(ModuleId, String),

    // Trouble using a type that we can't find the name for.
    UnnamedType(String),

    // Some sort of value we could handle, but we don't yet, because it's rare.
    UnhandledValue(String),

    // The code contains the explicit goal, which we can't generate code for.
    ExplicitGoal,

    // When you try to generate code but there is no proof
    NoProof,

    // Generated code that failed checking
    GeneratedBadCode(String),

    // Something went wrong, it's our fault, and we can't figure out what it is
    InternalError(String),
}

impl Error {
    pub fn synthetic(s: &str) -> Error {
        Error::Synthetic(s.to_string())
    }

    pub fn unnamed_type(datatype: &Datatype) -> Error {
        Error::UnnamedType(datatype.name.to_string())
    }

    pub fn unhandled_value(s: &str) -> Error {
        Error::UnhandledValue(s.to_string())
    }

    pub fn internal<T: Into<String>>(s: T) -> Error {
        Error::InternalError(s.into())
    }

    pub fn error_type(&self) -> &'static str {
        match self {
            Error::Synthetic(_) => "Synthetic",
            Error::UnimportedModule(..) => "UnimportedModule",
            Error::UnnamedType(_) => "UnnamedType",
            Error::UnhandledValue(_) => "UnhandledValue",
            Error::ExplicitGoal => "ExplicitGoal",
            Error::NoProof => "NoProof",
            Error::GeneratedBadCode(_) => "GeneratedInvalidCode",
            Error::InternalError(_) => "InternalError",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Synthetic(s) => {
                write!(f, "could not find a name for the synthetic constant: {}", s)
            }
            Error::UnimportedModule(_, name) => {
                write!(
                    f,
                    "could not generate code using '{}' because it is not imported",
                    name
                )
            }
            Error::UnnamedType(s) => {
                write!(f, "could not figure out a name for the type: {}", s)
            }
            Error::UnhandledValue(s) => {
                write!(f, "codegen for '{}' values is not yet implemented", s)
            }
            Error::ExplicitGoal => {
                write!(f, "could not isolate the goal at the end of the proof")
            }
            Error::NoProof => write!(f, "no proof"),
            Error::GeneratedBadCode(s) => {
                write!(f, "generated invalid code: {}", s)
            }
            Error::InternalError(s) => {
                write!(f, "internal error: {}", s)
            }
        }
    }
}

impl From<crate::compilation::CompilationError> for Error {
    fn from(err: crate::compilation::CompilationError) -> Self {
        Error::GeneratedBadCode(err.to_string())
    }
}

impl From<String> for Error {
    fn from(err: String) -> Self {
        Error::GeneratedBadCode(err)
    }
}

#[cfg(test)]
mod tests {
    use crate::project::Project;

    #[test]
    fn test_code_generation() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            type MyType: axiom
            let t: MyType = axiom
        "#,
        );
        p.check_code("main", "t");
        p.check_code("main", "forall(x0: MyType) { x0 = t }");
    }

    #[test]
    fn test_code_for_imported_things() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            let thing1: Bool = axiom
            let thing2: Bool = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import stuff
            let st1: Bool = stuff.thing1
        "#,
        );
        p.check_code_into("main", "stuff.thing1", "st1");
        p.check_code("main", "st1");
        p.check_code("main", "stuff.thing2");
    }

    #[test]
    fn test_imported_member_functions() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolpair.ac",
            r#"
            structure BoolPair {
                first: Bool
                second: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import boolpair
            type BoolPair: boolpair.BoolPair
            let first: BoolPair -> Bool = BoolPair.first
        "#,
        );
        p.expect_ok("main");
        p.check_code("main", "first");
        p.check_code_into("main", "BoolPair.first", "first");
        p.check_code_into("main", "boolpair.BoolPair.first", "first");

        p.check_code("main", "BoolPair.second");
        p.check_code_into("main", "boolpair.BoolPair.second", "BoolPair.second");
    }

    #[test]
    fn test_structure_aliasing() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            structure Foo {
                member: Bool
            }
            type Bar: Foo
        "#,
        );
        p.expect_ok("stuff");
        p.check_code_into("stuff", "Bar.member", "Foo.member");
    }

    #[test]
    fn test_names_imported_via_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            type Foo: axiom
            attributes Foo {
                let foo: Bool = true
                let foo2: Bool = false
            }
            type Bar: Foo
            let bar: Bar = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from stuff import Foo, Bar, bar
            let x: Bool = Bar.foo
            let y: Bar = bar
        "#,
        );
        p.expect_ok("stuff");
        p.expect_ok("main");
        p.check_code("main", "x");
        p.check_code_into("main", "y", "bar");
        p.check_code_into("main", "stuff.Foo.foo2", "Foo.foo2");
    }

    #[test]
    fn test_imported_numbers_codegen_basic() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            "#,
        );
        p.check_code_into("main", "nat.Nat.0", "Nat.0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "Nat.0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "Nat.0 + Nat.0");
    }

    #[test]
    fn test_imported_numbers_codegen_with_numerals() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            numerals Nat
            "#,
        );
        p.check_code_into("main", "nat.Nat.0", "0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "0 + 0");
    }

    #[test]
    fn test_import_without_from_codegen() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolbox.ac",
            r#"
            structure BoolBox {
                item: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import boolbox
        "#,
        );
        p.check_code("main", "forall(x0: boolbox.BoolBox) { true }");
    }

    #[test]
    fn test_importing_a_generic_type() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import Pair
            "#,
        );
        p.check_code("main", "forall(x0: Pair[Bool, Bool]) { true }");
        p.check_code(
            "main",
            "forall(x0: Bool, x1: Bool) { Pair.new(x0, x1).second = x1 }",
        );
    }

    #[test]
    fn test_generic_type_in_imported_module() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import pair
            "#,
        );
        p.check_code("main", "forall(x0: pair.Pair[Bool, Bool]) { true }");
    }

    #[test]
    fn test_aliasing_local_generic_constant() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            let pbbn: (Bool, Bool) -> Pair[Bool, Bool] = Pair[Bool, Bool].new
            "#,
        );
        p.expect_ok("pair");
        p.check_code("pair", "pbbn(false, true)");
    }

    #[test]
    fn test_importing_generic_function() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            define double[T](x: T) -> Pair[T, T] {
                Pair.new(x, x)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import double
            "#,
        );
        p.check_code("main", "double(true)");
    }

    #[test]
    fn test_generic_function_in_imported_module() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            define double[T](x: T) -> Pair[T, T] {
                Pair.new(x, x)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import pair
            "#,
        );
        p.check_code("main", "pair.double(true)");
    }

    #[test]
    fn test_importing_typeclasses_with_import() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/magma.ac",
            r#"
            typeclass M: Magma {
                op: (M, M) -> M
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import magma

            inductive Z1 {
                zero
            }

            instance Z1: magma.Magma {
                define op(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
        );
        p.check_code("main", "Z1.zero.op(Z1.zero) = Z1.zero");
    }

    #[test]
    fn test_importing_typeclasses_with_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/magma.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from magma import Magma

            inductive Z1 {
                zero
            }

            instance Z1: Magma {
                define mul(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
        );
        p.check_code("main", "Z1.zero * Z1.zero = Z1.zero");
    }

    #[test]
    fn test_codegen_typeclass_infix() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            theorem goal[M: Magma](x: M) {
                x * x = x
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x * x = x");
    }

    #[test]
    fn test_codegen_extended_infix() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            typeclass T: Thing extends Magma {
                thing_property: Bool
            }

            theorem goal[T: Thing](x: T) {
                x * x = x
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x * x = x");
    }

    #[test]
    fn test_codegen_for_imported_typeclasses() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo.ac",
            r#"
            typeclass F: Foo {
                zero: F
                add: (F, F) -> F
                neg: F -> F
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Foo

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            theorem goal[B: Bar](x: B) {
                x + -x = B.zero + B.zero
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x + -x = B.zero + B.zero");
    }

    #[test]
    fn test_codegen_for_quantified_types() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                item: F
            }

            inductive List[T] {
                nil
                cons(T, List[T])
            }

            structure Bar {
                item: Bool
            }

            theorem goal1 {
                exists(a: Bar) {
                    true
                }
            }

            theorem goal2 {
                exists(a: List[Bool]) {
                    true
                }
            }

            theorem goal3[F: Foo] {
                exists(a: List[F]) {
                    true
                }
            }

            theorem goal4 {
                exists(a: Bool) {
                    a
                }
            }
            "#,
        );
        p.check_goal_code("main", "goal1", "exists(k0: Bar) { true }");
        p.check_goal_code("main", "goal2", "exists(k0: List[Bool]) { true }");
        p.check_goal_code("main", "goal3", "exists(k0: List[F]) { true }");
        p.check_goal_code("main", "goal4", "exists(k0: Bool) { k0 }");
    }

    #[test]
    fn test_codegen_indirect_attribute() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo_base.ac",
            r#"
            inductive Foo {
                foo
            }

            attributes Foo {
                define add(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
        "#,
        );
        p.mock(
            "/mock/foo_middle.ac",
            r#"
            from foo_base import Foo
            attributes Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
        );
        p.mock(
            "/mock/foo.ac",
            r#"
            from foo_middle import Foo
            attributes Foo {
                define sub(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Foo
            "#,
        );
        p.check_code("main", "Foo.add");
        p.check_code("main", "Foo.foo.add");
        p.check_code("main", "Foo.foo + Foo.foo");
        p.check_code("main", "Foo.mul");
        p.check_code("main", "Foo.foo.mul");
        p.check_code("main", "Foo.foo * Foo.foo");
        p.check_code("main", "Foo.sub");
        p.check_code("main", "Foo.foo.sub");
        p.check_code("main", "Foo.foo - Foo.foo");
    }

    #[test]
    fn test_codegen_instance_attribute_access() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                vacuous {
                    true
                }
            }

            attributes F: Foo {
                let flag: Bool = true
                define foo(self) -> Bool {
                    true
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            theorem const_attr(b: Bar) {
                Bar.flag
            }

            theorem fn_attr(b: Bar) {
                b.foo
            }
            "#,
        );
        p.check_goal_code("main", "const_attr", "Bar.flag");
        p.check_goal_code("main", "fn_attr", "b.foo");
    }

    #[test]
    fn test_codegen_overridden_attribute() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                vacuous {
                    true
                }
            }

            attributes F: Foo {
                let flag: Bool = true
                define foo(self) -> Bool {
                    true
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            // These override, changing the desired codegen.
            attributes Bar {
                let flag: Bool = false
                define foo(self) -> Bool {
                    false
                }
            }

            theorem const_attr(b: Bar) {
                Foo.flag[Bar]
            }

            theorem fn_attr(b: Bar) {
                Foo.foo[Bar](b)
            }
            "#,
        );
        p.check_goal_code("main", "const_attr", "Foo.flag[Bar]");
        p.check_goal_code("main", "fn_attr", "Foo.foo[Bar](b)");
    }
}
