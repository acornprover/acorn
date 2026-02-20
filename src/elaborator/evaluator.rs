use crate::elaborator::acorn_type::{AcornType, Datatype, PotentialType, TypeParam, Typeclass};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp};
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::inference::InferenceEngine;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::DefinedName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::stack::Stack;
use crate::module::ModuleId;
use crate::project::Project;
use crate::syntax::expression::{Declaration, Expression, TypeParamExpr};
use crate::syntax::token::{Token, TokenType};
use crate::syntax::token_map::TokenMap;

/// Represents the type arguments in an attributes statement.
/// Either generic type parameters (e.g., K, T) or concrete types (e.g., Color, Nat).
#[derive(Debug, Clone)]
pub enum AttributesTypeArgs {
    /// Generic type parameters like `attributes Set[K]`
    Generic(Vec<TypeParam>),
    /// Concrete types like `attributes Set[Color]`
    Concrete(Vec<AcornType>),
}

/// The Evaluator turns expressions into types and values, and other things of that nature.
pub struct Evaluator<'a> {
    /// The bindings to use for evaluation.
    bindings: &'a BindingMap,

    /// The overall project.
    project: &'a Project,

    /// If the token map is provided, we update it whenever we first determine the
    /// semantics of a token.
    /// This may not be from the same module as the bindings, so we need to be careful.
    token_map: Option<&'a mut TokenMap>,
}

impl<'a> Evaluator<'a> {
    /// Creates a new evaluator.
    pub fn new(
        project: &'a Project,
        bindings: &'a BindingMap,
        token_map: Option<&'a mut TokenMap>,
    ) -> Self {
        Self {
            project,
            bindings,
            token_map,
        }
    }

    // Gets the bindings from the project, except uses the one we already have if it's correct.
    // This is useful while we're still analyzing the module, because in that case, the project
    // won't have access to it yet.
    fn get_bindings(&self, module_id: ModuleId) -> &'a BindingMap {
        if module_id == self.bindings.module_id() {
            self.bindings
        } else {
            self.project.get_bindings(module_id).unwrap()
        }
    }

    fn inference(&self) -> InferenceEngine<'_> {
        InferenceEngine::new(self.bindings)
    }

    /// Tracks token information for the given entity.
    fn track_token(&mut self, token: &Token, entity: &NamedEntity) {
        if let Some(token_map) = self.token_map.as_mut() {
            token_map.track_token(token, entity);
        }
    }

    /// Evaluates an expression that represents a type.
    pub fn evaluate_type(&mut self, expression: &Expression) -> error::Result<AcornType> {
        let potential = self.evaluate_potential_type(expression)?;
        match potential {
            PotentialType::Resolved(t) => Ok(t),
            PotentialType::Unresolved(ut) => {
                Err(expression.error(&format!("type {} is unresolved", ut.datatype.name)))
            }
        }
    }

    /// Evaluates an expression that either represents a type, or represents a type that still needs params.
    pub fn evaluate_potential_type(
        &mut self,
        expression: &Expression,
    ) -> error::Result<PotentialType> {
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(token.error("axiomatic types can only be created at the top level"));
                }
                if let Some(t) = self.bindings.get_type_for_typename(token.text()) {
                    let entity = NamedEntity::from(t.clone());
                    self.track_token(token, &entity);
                    Ok(t.clone())
                } else {
                    Err(token.error("expected type name"))
                }
            }
            Expression::Unary(token, _) => {
                Err(token.error("unexpected unary operator in type expression"))
            }
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    let arg_exprs = left.flatten_list(true)?;
                    let mut arg_types = vec![];
                    for arg_expr in arg_exprs {
                        arg_types.push(self.evaluate_type(arg_expr)?);
                    }
                    let return_type = self.evaluate_type(right)?;
                    Ok(PotentialType::Resolved(AcornType::functional(
                        arg_types,
                        return_type,
                    )))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(&mut Stack::new(), expression)?;
                    Ok(entity.expect_potential_type(token)?)
                }
                _ => Err(token.error("unexpected binary operator in type expression")),
            },
            Expression::Concatenation(left, params) => {
                let Expression::Grouping(opening, expr, _) = params.as_ref() else {
                    return Err(params.error("expected type parameters in type application"));
                };
                if opening.token_type != TokenType::LeftBracket
                    && opening.token_type != TokenType::LessThan
                {
                    return Err(opening.error("expected '[' or 'or' for type params"));
                }
                let param_exprs = expr.flatten_comma_separated_list();
                let mut instance_params = vec![];
                for param_expr in param_exprs {
                    instance_params.push(self.evaluate_type(param_expr)?);
                }
                let p = self.evaluate_potential_type(left)?;
                let t = p.resolve(instance_params, expression)?;
                Ok(PotentialType::Resolved(t))
            }
            Expression::Grouping(_, e, _) => self.evaluate_potential_type(e),
            Expression::Binder(token, _, _, _)
            | Expression::GenericBinder(token, _, _, _, _)
            | Expression::IfThenElse(token, _, _, _, _) => {
                Err(token.error("unexpected token in type expression"))
            }
            Expression::Match(token, _, _, _) => {
                Err(token.error("unexpected match token in type expression"))
            }
        }
    }

    /// Evaluates a list of types.
    pub fn evaluate_type_list(
        &mut self,
        expression: &Expression,
        output: &mut Vec<AcornType>,
    ) -> error::Result<()> {
        match expression {
            Expression::Grouping(_, e, _) => self.evaluate_type_list(e, output),
            Expression::Binary(left, token, right) if token.token_type == TokenType::Comma => {
                self.evaluate_type_list(left, output)?;
                self.evaluate_type_list(right, output)
            }
            e => {
                output.push(self.evaluate_type(e)?);
                Ok(())
            }
        }
    }

    /// Evaluates a variable declaration in this context.
    /// "self" declarations should be handled externally.
    pub fn evaluate_declaration(
        &mut self,
        declaration: &Declaration,
    ) -> error::Result<(String, AcornType)> {
        match declaration {
            Declaration::Typed(name_token, type_expr) => {
                let acorn_type = self.evaluate_type(&type_expr)?;
                return Ok((name_token.to_string(), acorn_type));
            }
            Declaration::SelfToken(name_token) => {
                return Err(name_token.error("cannot use 'self' as an argument here"));
            }
        };
    }

    /// Parses a list of named argument declarations and adds them to the stack.
    /// datatype_type should be provided if these are the arguments of a new member function.
    pub fn bind_args<'b, I>(
        &mut self,
        stack: &mut Stack,
        declarations: I,
        datatype_type: Option<&AcornType>,
    ) -> error::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'b Declaration>,
    {
        self.bind_args_internal(stack, declarations, datatype_type, false)
    }

    /// Like bind_args, but allows argument names to shadow existing unqualified constants.
    pub fn bind_args_may_shadow<'b, I>(
        &mut self,
        stack: &mut Stack,
        declarations: I,
        datatype_type: Option<&AcornType>,
    ) -> error::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'b Declaration>,
    {
        self.bind_args_internal(stack, declarations, datatype_type, true)
    }

    fn bind_args_internal<'b, I>(
        &mut self,
        stack: &mut Stack,
        declarations: I,
        datatype_type: Option<&AcornType>,
        allow_shadowing: bool,
    ) -> error::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'b Declaration>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for (i, declaration) in declarations.into_iter().enumerate() {
            if datatype_type.is_some() && i == 0 {
                match declaration {
                    Declaration::SelfToken(_) => {
                        names.push("self".to_string());
                        types.push(datatype_type.unwrap().clone());
                        continue;
                    }
                    _ => {
                        return Err(declaration
                            .token()
                            .error("first argument of a member function must be 'self'"));
                    }
                }
            }
            let (name, acorn_type) = self.evaluate_declaration(declaration)?;
            if !allow_shadowing {
                self.bindings
                    .check_unqualified_name_available(&name, declaration.token())?;
            }
            if stack.get(&name).is_some() {
                return Err(declaration
                    .token()
                    .error(&format!("name '{}' is already bound", name)));
            }
            if names.contains(&name) {
                return Err(declaration
                    .token()
                    .error("cannot declare a name twice in one argument list"));
            }
            names.push(name);
            types.push(acorn_type);
        }
        for (name, acorn_type) in names.iter().zip(types.iter()) {
            stack.insert(name.to_string(), acorn_type.clone());
        }
        Ok((names, types))
    }

    /// Errors if the value is not a constructor of the expected type.
    /// Returns the index of which constructor this is, and the total number of constructors.
    fn expect_constructor(
        &mut self,
        expected_type: &AcornType,
        value: &AcornValue,
        source: &dyn ErrorContext,
    ) -> error::Result<(usize, usize)> {
        let AcornValue::Constant(ci) = value else {
            return Err(source.error("invalid pattern"));
        };
        let bindings = self.get_bindings(ci.name.module_id());
        let Some(info) = bindings.get_constructor_info(&ci.name) else {
            return Err(source.error("expected a constructor"));
        };
        expected_type.check_instance(&info.datatype, source)?;
        Ok((info.index, info.total))
    }

    /// Evaluates a pattern match. Infers their types from the pattern.
    /// Returns an error if the pattern is not a constructor of the expected type.
    /// Returns:
    ///   a value for the constructor function
    ///   a list of (name, type) pairs
    ///   the index of which constructor this is
    ///   the total number of constructors
    pub fn evaluate_pattern(
        &mut self,
        expected_type: &AcornType,
        pattern: &Expression,
    ) -> error::Result<(AcornValue, Vec<(String, AcornType)>, usize, usize)> {
        let (fn_exp, args) = match pattern {
            Expression::Concatenation(function, args) if !args.is_type() => (function, args),
            _ => {
                // This can only be a no-argument constructor.
                let mut no_token_evaluator = Evaluator::new(self.project, self.bindings, None);
                let constructor =
                    no_token_evaluator.evaluate_value(pattern, Some(expected_type))?;
                let (i, total) = self.expect_constructor(expected_type, &constructor, pattern)?;
                return Ok((constructor, vec![], i, total));
            }
        };
        let mut no_token_evaluator = Evaluator::new(self.project, self.bindings, None);
        let potential_constructor =
            no_token_evaluator.evaluate_potential_value(&mut Stack::new(), fn_exp, None)?;
        let constructor = match potential_constructor {
            PotentialValue::Resolved(v) => v,
            PotentialValue::Unresolved(uc) => {
                let AcornType::Data(datatype, params) = expected_type else {
                    return Err(pattern.error("unmatchable datatype?"));
                };
                if !uc.name.is_attribute_of(&datatype) {
                    return Err(pattern.error(&format!(
                        "pattern {} is not an attribute of {}",
                        &uc.name, datatype.name
                    )));
                }
                self.inference()
                    .resolve_unresolved_with_type_params(uc, params.clone(), pattern)?
            }
        };
        let (i, total) = self.expect_constructor(expected_type, &constructor, pattern)?;
        let AcornType::Function(f) = constructor.get_type() else {
            return Err(fn_exp.error("expected a function"));
        };
        if &*f.return_type != expected_type {
            return Err(pattern.error(&format!(
                "the pattern has type {} but we are matching type {}",
                &*f.return_type, expected_type
            )));
        }
        let name_exps = args.flatten_list(false)?;
        if name_exps.len() != f.arg_types.len() {
            return Err(args.error(&format!(
                "expected {} arguments but got {}",
                f.arg_types.len(),
                name_exps.len()
            )));
        }
        let mut args = vec![];
        for (name_exp, arg_type) in name_exps.into_iter().zip(f.arg_types.into_iter()) {
            let name = match name_exp {
                Expression::Singleton(token) => token.text().to_string(),
                _ => return Err(name_exp.error("expected a simple name in pattern")),
            };
            self.bindings
                .check_unqualified_name_available(&name, name_exp)?;
            // Check if we already saw this name
            if args.iter().any(|(n, _)| n == &name) {
                return Err(name_exp.error(&format!(
                    "cannot use the name '{}' twice in one pattern",
                    name
                )));
            }
            args.push((name, arg_type))
        }
        Ok((constructor, args, i, total))
    }

    /// This function evaluates numbers when we already know what type they are.
    /// token is the token to report errors with.
    /// s is the string to parse.
    fn evaluate_number_with_datatype(
        &mut self,
        token: &Token,
        datatype: &Datatype,
        s: &str,
    ) -> error::Result<AcornValue> {
        // Check if this digit/number is defined as an attribute (either directly or via typeclass)
        if self.bindings.resolve_datatype_attr(datatype, s).is_ok() {
            return self
                .evaluate_datatype_attr(&datatype, s, token)?
                .as_value(token);
        }

        if s.len() == 1 {
            return Err(token.error(&format!("digit {}.{} is not defined", &datatype.name, s)));
        }

        let last_str = &s[s.len() - 1..];
        let last_num = self.evaluate_number_with_datatype(token, datatype, last_str)?;
        let initial_str = &s[..s.len() - 1];
        let initial_num = self.evaluate_number_with_datatype(token, datatype, initial_str)?;
        let read_fn = match self.evaluate_datatype_attr(&datatype, "read", token)? {
            PotentialValue::Resolved(f) => f,
            PotentialValue::Unresolved(_) => {
                return Err(token.error(&format!(
                    "read function {}.read has unresolved type",
                    &datatype.name
                )))
            }
        };
        let value = AcornValue::apply(read_fn, vec![initial_num, last_num]);
        Ok(value)
    }

    /// Evaluates a name scoped by a datatype, like Nat.range
    fn evaluate_datatype_attr(
        &self,
        datatype: &Datatype,
        attr_name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let (module_id, const_name) = match self.bindings.resolve_datatype_attr(datatype, attr_name)
        {
            Ok((module_id, const_name)) => (module_id, const_name),
            Err(err) => return Err(source.error(&err)),
        };

        // Get the bindings from the module where this attribute was actually defined
        let bindings = self.get_bindings(module_id);
        let defined_name = DefinedName::Constant(const_name);
        let value = bindings
            .get_constant_value(&defined_name)
            .map_err(|e| source.error(&e))?;
        if !defined_name.is_typeclass_attr() {
            return Ok(value);
        };

        // If this is a typeclass attribute, instantiate it with the datatype.
        match value {
            PotentialValue::Unresolved(unresolved) => {
                let instance_type = AcornType::Data(datatype.clone(), vec![]);
                let resolved = self.inference().resolve_unresolved_with_type_params(
                    unresolved,
                    vec![instance_type],
                    source,
                )?;
                Ok(PotentialValue::Resolved(resolved))
            }
            potential => Ok(potential),
        }
    }

    /// Evalutes a name scoped by a typeclass name, like Group.foo
    fn evaluate_typeclass_attr(
        &self,
        typeclass: &Typeclass,
        attr_name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        if let Some((module_id, name)) = self.bindings.resolve_typeclass_attr(typeclass, attr_name)
        {
            // Get the bindings from the module where this attribute was actually defined
            let bindings = self.get_bindings(module_id);
            let defined_name = DefinedName::Constant(name);
            let attr_value = bindings
                .get_constant_value(&defined_name)
                .map_err(|e| source.error(&e))?;
            return Ok(attr_value);
        }

        // If no attribute found, return error
        Err(source.error(&format!(
            "attribute '{}' not found on typeclass '{}'",
            attr_name, typeclass.name
        )))
    }

    /// Evaluates an expression that is supposed to describe a value, with an empty stack.
    pub fn evaluate_value(
        &mut self,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> error::Result<AcornValue> {
        self.evaluate_value_with_stack(&mut Stack::new(), expression, expected_type)
    }

    /// Evaluates an attribute of a value, like foo.bar.
    /// token is used for reporting errors but may not correspond to anything in particular.
    fn evaluate_value_attr(
        &mut self,
        receiver: AcornValue,
        attr_name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let base_type = receiver.get_type();

        let function = match &base_type {
            AcornType::Data(datatype, type_params) => {
                // Try to resolve with specific type parameters first, then fall back to generic
                let (module_id, const_name) = match self.bindings.resolve_datatype_attr_with_params(
                    datatype,
                    type_params,
                    attr_name,
                ) {
                    Ok((module_id, const_name)) => (module_id, const_name),
                    Err(err) => return Err(source.error(&err)),
                };

                // Get the bindings from the module where this attribute was actually defined
                let bindings = self.get_bindings(module_id);
                let defined_name = DefinedName::Constant(const_name);
                let value = bindings
                    .get_constant_value(&defined_name)
                    .map_err(|e| source.error(&e))?;
                if !defined_name.is_typeclass_attr() {
                    value
                } else {
                    // If this is a typeclass attribute, instantiate it with the datatype.
                    if let PotentialValue::Unresolved(unresolved) = value {
                        let instance_type = AcornType::Data(datatype.clone(), vec![]);
                        let resolved = self.inference().resolve_unresolved_with_type_params(
                            unresolved,
                            vec![instance_type],
                            source,
                        )?;
                        PotentialValue::Resolved(resolved)
                    } else {
                        value
                    }
                }
            }
            AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                let Some(typeclass) = &param.typeclass else {
                    return Err(source.error(&format!(
                        "unqualified type {} has no attributes",
                        param.name
                    )));
                };
                let potential = self.evaluate_typeclass_attr(typeclass, attr_name, source)?;

                // Check if this is a non-function typeclass attribute
                let attr_type = potential.get_type();
                if !matches!(attr_type, AcornType::Function(_)) {
                    return Err(source.error(&format!(
                        "'.{}' is a type-level attribute, not a method. Use '{}.{}' to access it",
                        attr_name, param.name, attr_name
                    )));
                }

                potential
            }
            _ => {
                return Err(source.error(&format!(
                    "objects of type {:?} have no attributes",
                    base_type
                )));
            }
        };
        self.inference()
            .try_apply_potential(function, vec![receiver], None, source)
    }

    /// Evaluates a single name, which may be namespaced to another named entity.
    /// In this situation, we don't know what sort of thing we expect the name to represent.
    /// We have the entity described by a chain of names, and we're adding one more name to the chain.
    pub fn evaluate_name(
        &mut self,
        name_token: &Token,
        stack: &Stack,
        namespace: Option<NamedEntity>,
    ) -> error::Result<NamedEntity> {
        let name = name_token.text();
        let entity = match namespace {
            Some(NamedEntity::Value(instance)) => {
                let potential = self.evaluate_value_attr(instance, name, name_token)?;
                NamedEntity::new(potential)
            }
            Some(NamedEntity::Type(t)) => {
                match &t {
                    AcornType::Data(datatype, params) => {
                        if name_token.token_type == TokenType::Numeral {
                            let value = self.evaluate_number_with_datatype(
                                name_token,
                                &datatype,
                                name_token.text(),
                            )?;
                            NamedEntity::Value(value)
                        } else {
                            match self.evaluate_datatype_attr(datatype, name, name_token)? {
                                PotentialValue::Resolved(value) => {
                                    if !params.is_empty() {
                                        return Err(
                                            name_token.error("unexpected double type resolution")
                                        );
                                    }
                                    NamedEntity::Value(value)
                                }
                                PotentialValue::Unresolved(u) => {
                                    if params.is_empty() {
                                        // Leave it unresolved
                                        NamedEntity::UnresolvedValue(u)
                                    } else {
                                        // Resolve it with the params from the type name
                                        let value =
                                            self.inference().resolve_unresolved_with_type_params(
                                                u,
                                                params.clone(),
                                                name_token,
                                            )?;
                                        NamedEntity::Value(value)
                                    }
                                }
                            }
                        }
                    }
                    AcornType::Arbitrary(param) if param.typeclass.is_some() => {
                        let typeclass = param.typeclass.as_ref().unwrap();
                        match self.evaluate_typeclass_attr(&typeclass, name, name_token)? {
                            PotentialValue::Resolved(value) => NamedEntity::Value(value),
                            PotentialValue::Unresolved(u) => {
                                // Resolve it with the arbitrary type itself
                                let value = self.inference().resolve_unresolved_with_type_params(
                                    u,
                                    vec![t.clone()],
                                    name_token,
                                )?;
                                NamedEntity::Value(value)
                            }
                        }
                    }
                    _ => return Err(name_token.error("this type cannot have attributes")),
                }
            }
            Some(NamedEntity::Module(module)) => {
                if let Some(bindings) = self.project.get_bindings(module) {
                    // Funny case where the bindings aren't in the same module as the token.
                    // Be careful not to track the token map here.
                    Evaluator::new(self.project, bindings, None)
                        .evaluate_name(name_token, stack, None)?
                } else {
                    return Err(name_token.error("could not load bindings for module"));
                }
            }
            Some(NamedEntity::Typeclass(tc)) => {
                match self.evaluate_typeclass_attr(&tc, name, name_token)? {
                    PotentialValue::Resolved(value) => NamedEntity::Value(value),
                    PotentialValue::Unresolved(u) => NamedEntity::UnresolvedValue(u),
                }
            }
            Some(NamedEntity::UnresolvedValue(_)) => {
                return Err(name_token.error("cannot access members of unresolved types"));
            }
            Some(NamedEntity::UnresolvedType(ut)) => {
                match self.evaluate_datatype_attr(&ut.datatype, name, name_token)? {
                    PotentialValue::Resolved(value) => NamedEntity::Value(value),
                    PotentialValue::Unresolved(u) => NamedEntity::UnresolvedValue(u),
                }
            }
            None => {
                match name_token.token_type {
                    TokenType::Identifier => {
                        if self.bindings.is_module(name) {
                            match self.bindings.get_module_id_for_name(name) {
                                Some(module) => NamedEntity::Module(module),
                                None => return Err(name_token.error("unknown module")),
                            }
                        } else if self.bindings.has_typename(name) {
                            match self.bindings.get_type_for_typename(name) {
                                Some(PotentialType::Resolved(t)) => NamedEntity::Type(t.clone()),
                                Some(PotentialType::Unresolved(ut)) => {
                                    NamedEntity::UnresolvedType(ut.clone())
                                }
                                _ => return Err(name_token.error("unknown type")),
                            }
                        } else if self.bindings.has_typeclass_name(name) {
                            let tc = self.bindings.get_typeclass_for_name(name).unwrap();
                            NamedEntity::Typeclass(tc.clone())
                        } else if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            NamedEntity::Value(AcornValue::Variable(*i, t.clone()))
                        } else {
                            let constant_name =
                                DefinedName::unqualified(self.bindings.module_id(), name);
                            NamedEntity::new(
                                self.bindings
                                    .get_constant_value(&constant_name)
                                    .map_err(|e| name_token.error(&e))?,
                            )
                        }
                    }
                    TokenType::Numeral => {
                        let datatype = match self.bindings.numerals() {
                            Some(c) => c,
                            None => {
                                return Err(name_token
                                    .error("you must set a default type for numeric literals"));
                            }
                        };
                        let value = self.evaluate_number_with_datatype(
                            name_token,
                            &datatype,
                            name_token.text(),
                        )?;
                        NamedEntity::Value(value)
                    }
                    TokenType::SelfToken => {
                        if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            NamedEntity::Value(AcornValue::Variable(*i, t.clone()))
                        } else {
                            return Err(name_token.error("unexpected location for 'self'"));
                        }
                    }
                    TokenType::Lib => {
                        // lib must be used with parentheses as lib(module)
                        return Err(name_token
                            .error("'lib' must be followed by parentheses, e.g. lib(module)"));
                    }
                    t => return Err(name_token.error(&format!("unexpected {:?} token", t))),
                }
            }
        };

        self.track_token(name_token, &entity);

        Ok(entity)
    }

    /// Evaluates a single dot operator.
    fn evaluate_dot_expression(
        &mut self,
        stack: &mut Stack,
        left: &Expression,
        right: &Expression,
    ) -> error::Result<NamedEntity> {
        let right_token = match right {
            Expression::Singleton(token) => token,
            _ => return Err(right.error("expected an identifier after a dot")),
        };
        let left_entity = self.evaluate_entity(stack, left)?;
        self.evaluate_name(right_token, stack, Some(left_entity))
    }

    /// Evaluate a string of names separated by dots.
    /// Creates fake tokens to be used for error reporting.
    /// Chain must not be empty.
    pub fn evaluate_name_chain(&mut self, chain: &[&str]) -> Option<NamedEntity> {
        let mut answer: Option<NamedEntity> = None;
        for name in chain {
            let token = TokenType::Identifier.new_token(name);
            answer = Some(self.evaluate_name(&token, &Stack::new(), answer).ok()?);
        }
        answer
    }

    /// Extract a module name from an expression like foo.bar.baz
    /// Returns the module name as a string like "foo.bar.baz"
    fn extract_module_name(&self, expression: &Expression) -> error::Result<String> {
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Identifier {
                    Ok(token.text().to_string())
                } else {
                    Err(token.error("expected a module name"))
                }
            }
            Expression::Binary(left, op, right) => {
                if op.token_type != TokenType::Dot {
                    return Err(op.error("expected a dot-separated module path"));
                }
                let left_name = self.extract_module_name(left)?;
                let right_name = match right.as_ref() {
                    Expression::Singleton(token) if token.token_type == TokenType::Identifier => {
                        token.text()
                    }
                    _ => return Err(right.error("expected an identifier after dot")),
                };
                Ok(format!("{}.{}", left_name, right_name))
            }
            _ => Err(expression.error("expected a module path")),
        }
    }

    /// Evaluates an expression that could represent any sort of named entity.
    /// It could be a type, a value, or a module.
    fn evaluate_entity(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
    ) -> error::Result<NamedEntity> {
        // Handle a plain old name
        if let Expression::Singleton(token) = expression {
            return self.evaluate_name(token, stack, None);
        }

        // Special case: lib(module) syntax - always returns a module
        if let Expression::Concatenation(function_expr, args_expr) = expression {
            if let Expression::Singleton(token) = function_expr.as_ref() {
                if token.token_type == TokenType::Lib {
                    // lib() is special syntax for accessing modules
                    if let Expression::Grouping(_, module_expr, _) = args_expr.as_ref() {
                        // Extract the module name and return the module
                        let module_name = self.extract_module_name(module_expr)?;

                        match self.project.get_module_id_by_name(&module_name) {
                            Some(module_id) => {
                                return Ok(NamedEntity::Module(module_id));
                            }
                            None => {
                                return Err(module_expr
                                    .error(&format!("module '{}' not found", module_name)));
                            }
                        }
                    } else {
                        return Err(args_expr.error("lib() expects a module path in parentheses"));
                    }
                }
            }
        }

        // Dot expressions could be any sort of named entity
        if let Expression::Binary(left, token, right) = expression {
            if token.token_type == TokenType::Dot {
                return self.evaluate_dot_expression(stack, left, right);
            }
        }

        if expression.is_type() {
            let acorn_type = self.evaluate_type(expression)?;
            return Ok(NamedEntity::Type(acorn_type));
        }

        // If it isn't a name or a type, it must be a value.
        let value = self.evaluate_value_with_stack(stack, expression, None)?;
        Ok(NamedEntity::Value(value))
    }

    /// Evaluates an infix operator.
    /// name is the special alphanumeric name that corresponds to the operator, like "+" expands to "add".
    fn evaluate_infix(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
        left: &Expression,
        token: &Token,
        right: &Expression,
        name: &str,
        expected_type: Option<&AcornType>,
    ) -> error::Result<AcornValue> {
        let mut left_value = self.evaluate_value_with_stack(stack, left, None)?;
        let mut right_value = self.evaluate_value_with_stack(stack, right, None)?;

        // swap left and right for infix op `∈` and `∉`, e.g. `x ∈ a` will be mapped to `a.contains(x)`
        if token.token_type == TokenType::ElemOf || token.token_type == TokenType::NotElemOf {
            std::mem::swap(&mut left_value, &mut right_value);
        }

        // Get the partial application to the left
        let potential = self.evaluate_value_attr(left_value, name, expression)?;

        // Handle Resolved and Unresolved cases differently
        let value = match potential {
            PotentialValue::Resolved(partial) => {
                // Resolved case: use the old logic to preserve value structure for code generation
                let mut fa = match partial {
                    AcornValue::Application(fa) => fa,
                    _ => {
                        return Err(expression.error(&format!(
                            "the '{}' operator requires a method named '{}'",
                            token, name
                        )))
                    }
                };
                match fa.function.get_type() {
                    AcornType::Function(f) => {
                        if f.arg_types.len() != 2 {
                            return Err(expression.error(&format!(
                                "expected a binary function for '{}' method",
                                name
                            )));
                        }
                        right_value.check_type(Some(&f.arg_types[1]), expression)?;
                    }
                    _ => {
                        return Err(
                            expression.error(&format!("unexpected type for '{}' method", name))
                        )
                    }
                };

                fa.args.push(right_value);
                AcornValue::apply(*fa.function, fa.args)
            }
            unresolved_potential => self.inference().apply_potential_or_error(
                unresolved_potential,
                vec![right_value],
                expected_type,
                &format!("cannot infer type parameters for '{}' operator", token),
                expression,
            )?,
        };

        value.check_type(expected_type, expression)?;
        Ok(value)
    }

    /// Evaluates an expression that describes a value, with a stack given as context.
    /// This must resolve to a completed value, with all types inferred.
    /// If the result is an unresolved constant and we have an expected type, we'll try to
    /// use type inference to resolve it.
    pub fn evaluate_value_with_stack(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> error::Result<AcornValue> {
        let potential = self.evaluate_potential_value(stack, expression, expected_type)?;
        let resolved =
            self.inference()
                .maybe_resolve_value(potential, expected_type, expression)?;
        resolved.as_value(expression)
    }

    /// Evaluates an expression as a generic value, converting unresolved constants
    /// to their generic form. This is useful for type inference when we need to
    /// pass arguments that may have in-scope type variables.
    pub fn evaluate_as_generic_value(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
    ) -> error::Result<AcornValue> {
        let potential = self.evaluate_potential_value(stack, expression, None)?;
        Ok(potential.to_generic_value())
    }

    /// Evaluates operands for equality or not-equals expressions.
    /// Handles the case where one operand is an unresolved constant - uses the type
    /// of the other operand to resolve it via type inference.
    fn evaluate_equality_operands(
        &mut self,
        stack: &mut Stack,
        left: &Expression,
        right: &Expression,
        left_expected: Option<&AcornType>,
    ) -> error::Result<(AcornValue, AcornValue)> {
        let left_potential = self.evaluate_potential_value(stack, left, left_expected)?;
        let right_potential = self.evaluate_potential_value(stack, right, None)?;
        self.inference()
            .resolve_equality_operands(left_potential, left, right_potential, right)
    }

    /// Evaluates an expression that could describe a value, but could also describe
    /// a constant with an unresolved type.
    fn evaluate_potential_value(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> error::Result<PotentialValue> {
        let value = match expression {
            Expression::Singleton(token) => match token.token_type {
                TokenType::Axiom => panic!("axiomatic values should be handled elsewhere"),
                TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                    return Err(token.error("binder keywords cannot be used as values"));
                }
                TokenType::True | TokenType::False => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    AcornValue::Bool(token.token_type == TokenType::True)
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, stack, None)?;
                    match entity {
                        NamedEntity::Value(value) => {
                            value.check_type(expected_type, expression)?;
                            value
                        }
                        NamedEntity::Type(_)
                        | NamedEntity::Module(_)
                        | NamedEntity::Typeclass(_)
                        | NamedEntity::UnresolvedType(_) => {
                            return Err(token.error("expected a value"));
                        }
                        NamedEntity::UnresolvedValue(u) => {
                            let potential = PotentialValue::Unresolved(u);
                            return self.inference().maybe_resolve_value(
                                potential,
                                expected_type,
                                token,
                            );
                        }
                    }
                }
                token_type => {
                    return Err(token.error(&format!(
                        "identifier expression has token type {:?}",
                        token_type
                    )))
                }
            },
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Not => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let value =
                        self.evaluate_value_with_stack(stack, expr, Some(&AcornType::Bool))?;
                    AcornValue::Not(Box::new(value))
                }
                TokenType::QuestionMark => {
                    // The try operator '?' requires a '.some' constructor on the type.
                    // If foo has type MyType[P1, P2, ...], and MyType.some has type T -> MyType[P1, P2, ...],
                    // then foo? has type T.

                    // First evaluate the inner expression to get its type
                    let inner_value = self.evaluate_value_with_stack(stack, expr, None)?;
                    let inner_type = inner_value.get_type();

                    // Extract the datatype and type parameters from the inner type
                    let (datatype, type_params) = match &inner_type {
                        AcornType::Data(dt, params) => (dt, params),
                        _ => {
                            return Err(token.error(&format!(
                                "try operator requires a data type with a '.some' constructor, but found type {:?}",
                                inner_type
                            )));
                        }
                    };

                    // Look up the .some constructor on the datatype
                    let (module_id, const_name) = self
                        .bindings
                        .resolve_datatype_attr_with_params(datatype, type_params, "some")
                        .map_err(|e| token.error(&e))?;

                    // Get the constructor's value
                    let bindings = self.get_bindings(module_id);
                    let defined_name = DefinedName::Constant(const_name);
                    let some_potential = bindings
                        .get_constant_value(&defined_name)
                        .map_err(|e| token.error(&e))?;

                    // Resolve the constructor with the type parameters
                    let some_value = match some_potential {
                        PotentialValue::Resolved(v) => v,
                        PotentialValue::Unresolved(u) => self
                            .inference()
                            .resolve_unresolved_with_type_params(u, type_params.clone(), token)?,
                    };

                    // Verify that .some is a function of type T -> inner_type
                    let some_type = some_value.get_type();
                    let unwrapped_type = match &some_type {
                        AcornType::Function(ft) => {
                            // Verify it takes exactly one argument
                            if ft.arg_types.len() != 1 {
                                return Err(token.error(&format!(
                                    "'.some' must be a function with exactly one argument, but has {} arguments",
                                    ft.arg_types.len()
                                )));
                            }

                            // Verify the return type matches the inner type
                            if *ft.return_type != inner_type {
                                return Err(token.error(&format!(
                                    "'.some' must return the same type as the value being unwrapped, expected {:?}, but returns {:?}",
                                    inner_type, ft.return_type
                                )));
                            }

                            // The unwrapped type is the argument type
                            ft.arg_types[0].clone()
                        }
                        _ => {
                            return Err(token.error(&format!(
                                "'.some' must be a function, but has type {:?}",
                                some_type
                            )));
                        }
                    };

                    // Check that the unwrapped type matches the expected type
                    unwrapped_type.check_eq(expected_type, token)?;

                    AcornValue::Try(Box::new(inner_value), unwrapped_type)
                }
                token_type => match token_type.to_prefix_magic_method_name() {
                    Some(name) => {
                        let subvalue = self.evaluate_value_with_stack(stack, expr, None)?;
                        let potential = self.evaluate_value_attr(subvalue, name, token)?;
                        let value = match potential {
                            PotentialValue::Resolved(v) => v,
                            PotentialValue::Unresolved(_) => {
                                return Err(token.error(&format!(
                                    "cannot use unresolved generic function for '{}' operator",
                                    token
                                )))
                            }
                        };
                        value.check_type(expected_type, token)?;
                        value
                    }
                    None => {
                        return Err(token.error("unexpected unary operator in value expression"))
                    }
                },
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow | TokenType::Implies => {
                    // We still allow right arrow in values for now, but eventually
                    // we should deprecate it.
                    // if token.token_type == TokenType::RightArrow {
                    //     return Err(token.error("RightArrow in values is deprecated"));
                    // }
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value =
                        self.evaluate_value_with_stack(stack, left, Some(&AcornType::Bool))?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&AcornType::Bool))?;

                    AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::Equals | TokenType::Iff => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_expected = if token.token_type == TokenType::Iff {
                        Some(&AcornType::Bool)
                    } else {
                        None
                    };
                    let (left_value, right_value) =
                        self.evaluate_equality_operands(stack, left, right, left_expected)?;
                    AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::NotEquals => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let (left_value, right_value) =
                        self.evaluate_equality_operands(stack, left, right, None)?;
                    AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    )
                }
                TokenType::And => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value =
                        self.evaluate_value_with_stack(stack, left, Some(&AcornType::Bool))?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&AcornType::Bool))?;
                    AcornValue::Binary(BinaryOp::And, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Or => {
                    AcornType::Bool.check_eq(expected_type, token)?;
                    let left_value =
                        self.evaluate_value_with_stack(stack, left, Some(&AcornType::Bool))?;
                    let right_value =
                        self.evaluate_value_with_stack(stack, right, Some(&AcornType::Bool))?;
                    AcornValue::Binary(BinaryOp::Or, Box::new(left_value), Box::new(right_value))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, left, right)?;
                    let potential = entity.expect_potential_value(expected_type, expression)?;
                    return self
                        .inference()
                        .maybe_resolve_value(potential, expected_type, token);
                }
                token_type => match token_type.to_infix_magic_method_name() {
                    Some(name) => self.evaluate_infix(
                        stack,
                        expression,
                        left,
                        token,
                        right,
                        name,
                        expected_type,
                    )?,
                    None => {
                        let message =
                            &format!("unexpected operator '{}' in value expression", token);
                        return Err(expression.error(message));
                    }
                },
            },
            Expression::Concatenation(function_expr, args_expr) => {
                // Special case: generic lambda instantiation
                // function[T](x: T) { body }[Nat] is parsed as
                // Concatenation(GenericBinder([T], (x: T), body), Grouping([Nat]))
                if let Expression::GenericBinder(token, type_params, decls, body, _) =
                    function_expr.as_ref()
                {
                    // args_expr must be type arguments [Nat, Bool, ...]
                    let type_arg_exprs = match args_expr.as_ref() {
                        Expression::Grouping(left, e, _)
                            if left.token_type == TokenType::LeftBracket
                                || left.token_type == TokenType::LessThan =>
                        {
                            e.flatten_comma_separated_list()
                        }
                        _ => return Err(token.error("generic function requires type arguments")),
                    };

                    // Create a modified BindingMap with type params bound to arbitrary types,
                    // preserving the generic lambda skeleton in AcornValue.
                    let mut new_bindings = self.bindings.clone();
                    let mut type_param_names = vec![];
                    let mut type_param_constraints = vec![];
                    for param in type_params {
                        let type_param = TypeParam {
                            name: param.name.text().to_string(),
                            typeclass: if let Some(typeclass) = &param.typeclass {
                                Some(self.evaluate_typeclass(typeclass)?)
                            } else {
                                None
                            },
                        };
                        type_param_names.push(type_param.name.clone());
                        type_param_constraints.push(type_param.typeclass.clone());
                        let potential =
                            PotentialType::Resolved(AcornType::Arbitrary(type_param.clone()));
                        new_bindings.add_type_alias(param.name.text(), potential, &param.name)?;
                    }

                    // Create a new evaluator with the modified bindings
                    let mut evaluator = Evaluator::new(self.project, &new_bindings, None);

                    // Evaluate type arguments in the generic lambda's type-parameter scope,
                    // so self-instantiation like function[T](...)[T] is representable.
                    let mut type_args = vec![];
                    for expr in &type_arg_exprs {
                        type_args.push(evaluator.evaluate_type(expr)?);
                    }
                    if type_args.len() != type_params.len() {
                        return Err(args_expr.error("wrong number of type arguments"));
                    }

                    // Evaluate as a regular Lambda.
                    // Generic lambdas may omit value args entirely in type-only claim syntax.
                    let (arg_names, arg_types) = evaluator.bind_args(stack, decls, None)?;
                    let body_val = evaluator.evaluate_value_with_stack(stack, body, None)?;
                    let lambda = AcornValue::Lambda(arg_types, Box::new(body_val));
                    stack.remove_all(&arg_names);

                    let typed_lambda = AcornValue::type_apply(
                        lambda,
                        type_param_names,
                        type_param_constraints,
                        type_args,
                    );
                    typed_lambda.check_type(expected_type, expression)?;
                    return Ok(PotentialValue::Resolved(typed_lambda));
                }

                let function = self.evaluate_potential_value(stack, function_expr, None)?;

                // Handle the case where the "args" are actually type parameters.
                let arg_exprs = match args_expr.as_ref() {
                    Expression::Grouping(left_delimiter, e, _) => {
                        let exprs = e.flatten_comma_separated_list();
                        if left_delimiter.token_type == TokenType::LeftBracket
                            || left_delimiter.token_type == TokenType::LessThan
                        {
                            // This is a type parameter list
                            if let PotentialValue::Unresolved(unresolved) = function {
                                let mut type_params = vec![];
                                for expr in exprs {
                                    type_params.push(self.evaluate_type(expr)?);
                                }
                                let resolved =
                                    self.inference().resolve_unresolved_with_type_params(
                                        unresolved,
                                        type_params,
                                        left_delimiter,
                                    )?;
                                resolved.check_type(expected_type, expression)?;
                                return Ok(PotentialValue::Resolved(resolved));
                            }
                            return Err(left_delimiter.error("unexpected type parameter list"));
                        } else {
                            exprs
                        }
                    }
                    _ => {
                        return Err(args_expr.error("expected a comma-separated list"));
                    }
                };

                // Typecheck the function
                let function_type = function.get_type();
                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(function_expr.error("cannot apply a non-function"));
                    }
                };
                if function_type.arg_types.len() < arg_exprs.len() {
                    return Err(args_expr.error(&format!(
                        "expected <= {} arguments, but got {}",
                        function_type.arg_types.len(),
                        arg_exprs.len()
                    )));
                }

                // Check if we have to do type inference.
                match function {
                    PotentialValue::Unresolved(unresolved) => {
                        let inference = InferenceEngine::new(self.bindings);
                        inference.resolve_unresolved_call_from_exprs(
                            unresolved,
                            &arg_exprs,
                            expected_type,
                            expression,
                            |arg_expr| self.evaluate_as_generic_value(stack, arg_expr),
                        )?
                    }
                    PotentialValue::Resolved(function) => {
                        // Simple, no-type-inference-necessary construction
                        let mut args = vec![];
                        for (i, arg_expr) in arg_exprs.iter().enumerate() {
                            let arg_type: &AcornType = &function_type.arg_types[i];
                            let arg =
                                self.evaluate_value_with_stack(stack, arg_expr, Some(arg_type))?;
                            args.push(arg);
                        }
                        let value = AcornValue::apply(function, args);
                        value.check_type(expected_type, expression)?;
                        value
                    }
                }
            }
            Expression::Grouping(_, e, _) => {
                self.evaluate_value_with_stack(stack, e, expected_type)?
            }
            Expression::Binder(token, args, body, _) => {
                if args.len() < 1 {
                    return Err(token.error("binders must have at least one argument"));
                }
                let (arg_names, arg_types) = self.bind_args(stack, args, None)?;
                let body_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value_with_stack(stack, body, body_type) {
                    Ok(value) => match token.token_type {
                        TokenType::ForAll => Ok(AcornValue::ForAll(arg_types, Box::new(value))),
                        TokenType::Exists => Ok(AcornValue::Exists(arg_types, Box::new(value))),
                        TokenType::Function => Ok(AcornValue::Lambda(arg_types, Box::new(value))),
                        _ => Err(token.error("expected a binder identifier token")),
                    },
                    Err(e) => Err(e),
                };
                stack.remove_all(&arg_names);
                if ret_val.is_ok() && token.token_type == TokenType::Function {
                    ret_val.as_ref().unwrap().check_type(expected_type, token)?;
                }
                ret_val?
            }
            Expression::GenericBinder(token, _, _, _, _) => {
                return Err(token.error("generic function requires type arguments"));
            }
            Expression::IfThenElse(_, cond_exp, if_exp, else_exp, _) => {
                let cond =
                    self.evaluate_value_with_stack(stack, cond_exp, Some(&AcornType::Bool))?;
                let if_value = self.evaluate_value_with_stack(stack, if_exp, expected_type)?;

                match else_exp {
                    Some(else_exp) => {
                        // Traditional if-then-else
                        let else_value = self.evaluate_value_with_stack(
                            stack,
                            else_exp,
                            Some(&if_value.get_type()),
                        )?;
                        AcornValue::IfThenElse(
                            Box::new(cond),
                            Box::new(if_value),
                            Box::new(else_value),
                        )
                    }
                    None => {
                        // If without else - convert to implies if if_value is boolean
                        if if_value.is_bool_type() {
                            AcornValue::implies(cond, if_value)
                        } else {
                            return Err(expression.error(
                                "if expressions without else clauses require the if branch to be boolean"
                            ));
                        }
                    }
                }
            }
            Expression::Match(_, scrutinee_exp, case_exps, _) => {
                let mut expected_type: Option<AcornType> = expected_type.cloned();
                let scrutinee = self.evaluate_value_with_stack(stack, scrutinee_exp, None)?;
                let scrutinee_type = scrutinee.get_type();
                let mut cases = vec![];
                let mut indices = vec![];
                let mut all_cases = false;
                for (pattern_exp, result_exp) in case_exps {
                    let (_, args, i, total) =
                        self.evaluate_pattern(&scrutinee_type, pattern_exp)?;
                    for (name, arg_type) in &args {
                        stack.insert(name.clone(), arg_type.clone());
                    }
                    if indices.contains(&i) {
                        return Err(pattern_exp
                            .error("cannot have multiple cases for the same constructor"));
                    }
                    indices.push(i);
                    if total == indices.len() {
                        all_cases = true;
                    }
                    let pattern =
                        self.evaluate_value_with_stack(stack, pattern_exp, Some(&scrutinee_type))?;
                    let result =
                        self.evaluate_value_with_stack(stack, result_exp, expected_type.as_ref())?;
                    if expected_type.is_none() {
                        expected_type = Some(result.get_type());
                    }
                    let mut arg_types = vec![];
                    for (name, arg_type) in args {
                        stack.remove(&name);
                        arg_types.push(arg_type);
                    }
                    cases.push((arg_types, pattern, result));
                }
                if !all_cases {
                    return Err(expression.error("not all constructors are covered in this match"));
                }
                AcornValue::Match(Box::new(scrutinee), cases)
            }
        };
        Ok(PotentialValue::Resolved(value))
    }

    pub fn evaluate_typeclass(&mut self, expression: &Expression) -> error::Result<Typeclass> {
        let entity = self.evaluate_entity(&mut Stack::new(), expression)?;
        match entity {
            NamedEntity::Typeclass(tc) => Ok(tc),
            _ => Err(expression.error("expected a typeclass")),
        }
    }

    /// Evaluates a list of type parameter expressions.
    /// This does not bind them into the environment.
    pub fn evaluate_type_params(
        &mut self,
        exprs: &[TypeParamExpr],
    ) -> error::Result<Vec<TypeParam>> {
        let mut answer: Vec<TypeParam> = vec![];
        for expr in exprs {
            // Reject complex type expressions in type parameter context
            if expr.type_expr.is_some() {
                return Err(expr.name.error(
                    "type parameters must be simple identifiers, not complex type expressions",
                ));
            }

            let name = expr.name.text().to_string();
            self.bindings.check_typename_available(&name, &expr.name)?;
            if answer.iter().any(|tp| tp.name == name) {
                return Err(expr.name.error("duplicate type parameter"));
            }
            let typeclass = match expr.typeclass.as_ref() {
                Some(e) => Some(self.evaluate_typeclass(e)?),
                None => None,
            };
            answer.push(TypeParam {
                name: expr.name.text().to_string(),
                typeclass,
            });
        }
        Ok(answer)
    }

    /// Evaluates type arguments for attributes statements.
    /// Returns either a list of type parameters (for generic attributes) or
    /// a list of concrete types (for specific attributes).
    /// Validates that it's all-or-nothing (no mixing generic and concrete).
    pub fn evaluate_attributes_type_args(
        &mut self,
        exprs: &[TypeParamExpr],
    ) -> error::Result<AttributesTypeArgs> {
        if exprs.is_empty() {
            return Ok(AttributesTypeArgs::Generic(vec![]));
        }

        // Check if each identifier refers to an existing type
        let mut concrete_count = 0;
        let mut generic_count = 0;

        for expr in exprs {
            if expr.typeclass.is_some() {
                // If there's a typeclass constraint (e.g., K: Eq), it must be generic
                generic_count += 1;
            } else if expr.type_expr.is_some() {
                // Complex type expression like List[Color] - definitely concrete
                concrete_count += 1;
            } else {
                let name = expr.name.text();
                // Check if this name is an existing type
                if self.bindings.get_type_for_typename(name).is_some() {
                    concrete_count += 1;
                } else {
                    generic_count += 1;
                }
            }
        }

        // Validate all-or-nothing
        if concrete_count > 0 && generic_count > 0 {
            return Err(exprs[0]
                .name
                .error("cannot mix concrete types and type parameters in attributes statement"));
        }

        if concrete_count > 0 {
            // All are concrete types - evaluate them
            let mut types = vec![];
            for expr in exprs {
                if expr.typeclass.is_some() {
                    return Err(expr
                        .name
                        .error("typeclass constraints not allowed on concrete types"));
                }

                // Handle both simple and complex types
                let acorn_type = if let Some(type_expression) = &expr.type_expr {
                    // Complex type like List[Color]
                    self.evaluate_type(type_expression)?
                } else {
                    // Simple type like Color
                    let type_expr = Expression::Singleton(expr.name.clone());
                    self.evaluate_type(&type_expr)?
                };

                types.push(acorn_type);
            }
            Ok(AttributesTypeArgs::Concrete(types))
        } else {
            // All are generic - use the existing evaluate_type_params
            let type_params = self.evaluate_type_params(exprs)?;
            Ok(AttributesTypeArgs::Generic(type_params))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::code_generator::CodeGenerator;
    use crate::syntax::expression::Terminator;
    use crate::syntax::token::TokenIter;

    use super::*;

    impl Evaluator<'_> {
        fn str_to_type(&mut self, input: &str) -> AcornType {
            let tokens = Token::scan(input);
            let mut tokens = TokenIter::new(tokens);
            let (expression, _) =
                Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
            match self.evaluate_type(&expression) {
                Ok(t) => t,
                Err(error) => panic!("Error evaluating type expression: {}", error),
            }
        }

        fn assert_type_ok(&mut self, input_code: &str) {
            let acorn_type = self.str_to_type(input_code);
            let type_expr = CodeGenerator::new(&self.bindings)
                .type_to_expr(&acorn_type)
                .unwrap();
            let reconstructed_code = type_expr.to_string();
            let reevaluated_type = self.str_to_type(&reconstructed_code);
            assert_eq!(acorn_type, reevaluated_type);
        }

        fn assert_type_bad(&mut self, input: &str) {
            let tokens = Token::scan(input);
            let mut tokens = TokenIter::new(tokens);
            let expression =
                match Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)) {
                    Ok((expression, _)) => expression,
                    Err(_) => {
                        // We expect a bad type so this is fine
                        return;
                    }
                };
            assert!(self.evaluate_potential_type(&expression).is_err());
        }
    }

    #[test]
    fn test_evaluator_types() {
        let p = Project::new_mock();
        let bindings = BindingMap::new(ModuleId(0));
        let mut e = Evaluator::new(&p, &bindings, None);
        e.assert_type_ok("Bool");
        e.assert_type_ok("Bool -> Bool");
        e.assert_type_ok("Bool -> (Bool -> Bool)");
        e.assert_type_ok("(Bool -> Bool) -> (Bool -> Bool)");
        e.assert_type_ok("(Bool, Bool) -> Bool");
        e.assert_type_bad("Bool, Bool -> Bool");
        e.assert_type_bad("(Bool, Bool)");
    }
}
