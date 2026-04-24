use crate::elaborator::acorn_type::{
    AcornType, Datatype, DependentTypeArg, FamilyParam, FamilyParamKind, PotentialType, TypeParam,
    Typeclass, ValueParam,
};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp, MatchCase};
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::inference::InferenceEngine;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::{ConstantName, DefinedName, InstanceName};
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::stack::Stack;
use crate::elaborator::unresolved_constant::UnresolvedConstant;
use crate::kernel::atom::AtomId;
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

#[derive(Clone, Debug)]
struct CurrentInstanceContext {
    defining_module: ModuleId,
    typeclass: Typeclass,
    datatype: Datatype,
    current_attr: String,
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

    /// When we are elaborating the body of an `instance` member, explicit uses of the matching
    /// typeclass attribute such as `Add.add[Nat]` should resolve to the instance implementation
    /// slot, not to the public typeclass constant. This context is only set for that temporary,
    /// in-progress instance-body elaboration path.
    current_instance_context: Option<CurrentInstanceContext>,
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
            current_instance_context: None,
        }
    }

    pub fn new_for_instance_member(
        project: &'a Project,
        bindings: &'a BindingMap,
        token_map: Option<&'a mut TokenMap>,
        instance_name: &InstanceName,
    ) -> Self {
        Self {
            project,
            bindings,
            token_map,
            current_instance_context: Some(CurrentInstanceContext {
                defining_module: bindings.module_id(),
                typeclass: instance_name.typeclass.clone(),
                datatype: instance_name.datatype.clone(),
                current_attr: instance_name.attribute.clone(),
            }),
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

    fn operator_ref_token<'expr>(expression: &'expr Expression) -> Option<&'expr Token> {
        match expression {
            Expression::Grouping(_, inner, _)
                if matches!(inner.as_ref(), Expression::Singleton(_)) =>
            {
                let Expression::Singleton(token) = inner.as_ref() else {
                    unreachable!();
                };
                token.token_type.is_operator_ref().then_some(token)
            }
            _ => None,
        }
    }

    fn equality_operator_arg_type(
        &self,
        token: &Token,
        expected_type: Option<&AcornType>,
        allow_generic: bool,
    ) -> error::Result<AcornType> {
        if let Some(expected_type) = expected_type {
            let AcornType::Function(function_type) = expected_type else {
                return Err(token.error("'(=)' requires a function type"));
            };
            if function_type.arg_types.len() != 2 {
                return Err(token.error("'(=)' requires a binary function type"));
            }
            function_type
                .return_type
                .check_eq(Some(&AcornType::Bool), token)?;
            function_type.arg_types[0].check_eq(Some(&function_type.arg_types[1]), token)?;
            return Ok(function_type.arg_types[0].clone());
        }

        if allow_generic {
            return Ok(AcornType::Arbitrary(TypeParam {
                name: format!("T_op_{}_{}", token.line_number, token.start),
                typeclass: None,
            }));
        }

        Err(token.error("cannot use '(=)' without a function type context"))
    }

    fn operator_ref_value(
        &mut self,
        token: &Token,
        stack_len: usize,
        expected_type: Option<&AcornType>,
        allow_generic_equality: bool,
    ) -> error::Result<AcornValue> {
        let stack_len = stack_len as AtomId;
        let value = match token.token_type {
            TokenType::Not => {
                let arg = AcornValue::Variable(stack_len, AcornType::Bool);
                AcornValue::Lambda(
                    vec![AcornType::Bool],
                    Box::new(AcornValue::Not(Box::new(arg))),
                )
            }
            TokenType::And | TokenType::Or => {
                let left = AcornValue::Variable(stack_len, AcornType::Bool);
                let right = AcornValue::Variable(stack_len + 1, AcornType::Bool);
                let body = if token.token_type == TokenType::And {
                    AcornValue::and(left, right)
                } else {
                    AcornValue::or(left, right)
                };
                AcornValue::Lambda(vec![AcornType::Bool, AcornType::Bool], Box::new(body))
            }
            TokenType::Equals => {
                let arg_type =
                    self.equality_operator_arg_type(token, expected_type, allow_generic_equality)?;
                let left = AcornValue::Variable(stack_len, arg_type.clone());
                let right = AcornValue::Variable(stack_len + 1, arg_type.clone());
                AcornValue::Lambda(
                    vec![arg_type.clone(), arg_type],
                    Box::new(AcornValue::equals(left, right)),
                )
            }
            _ => return Err(token.error("not a supported operator reference")),
        };
        value.check_type(expected_type, token)?;
        self.track_token(token, &NamedEntity::Value(value.clone()));
        Ok(value)
    }

    fn try_operator_ref_application(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
        function_expr: &Expression,
        arg_exprs: &[&Expression],
        expected_type: Option<&AcornType>,
    ) -> Option<error::Result<AcornValue>> {
        let token = Self::operator_ref_token(function_expr)?;
        if token.token_type != TokenType::Equals {
            return None;
        }

        Some(match arg_exprs.len() {
            0 => self.operator_ref_value(token, stack.len(), expected_type, false),
            1 => {
                let left_value = match self.evaluate_value_with_stack(stack, arg_exprs[0], None) {
                    Ok(value) => value,
                    Err(err) => return Some(Err(err)),
                };
                let arg_type = left_value.get_type();
                let right_value = AcornValue::Variable(stack.len() as AtomId, arg_type.clone());
                let value = AcornValue::Lambda(
                    vec![arg_type.clone()],
                    Box::new(AcornValue::equals(left_value, right_value)),
                );
                if let Err(err) = value.check_type(expected_type, expression) {
                    return Some(Err(err));
                }
                Ok(value)
            }
            2 => {
                let (left_value, right_value) = match self.evaluate_equality_operands(
                    stack,
                    arg_exprs[0],
                    arg_exprs[1],
                    None,
                ) {
                    Ok(values) => values,
                    Err(err) => return Some(Err(err)),
                };
                let value = AcornValue::equals(left_value, right_value);
                if let Err(err) = value.check_type(expected_type, expression) {
                    return Some(Err(err));
                }
                Ok(value)
            }
            _ => Err(expression.error("expected <= 2 arguments for '(=)'")),
        })
    }

    /// Creates a sibling evaluator that shares the current evaluation mode.
    ///
    /// We use this when we need a temporary evaluator with different bindings or without token
    /// tracking, but we still need to preserve the temporary instance-member context.
    /// Reconstructing via `Evaluator::new(...)` would silently drop that context and change how
    /// explicit typeclass attributes resolve inside an `instance` body.
    fn fork(&self, bindings: &'a BindingMap, token_map: Option<&'a mut TokenMap>) -> Self {
        Self {
            project: self.project,
            bindings,
            token_map,
            current_instance_context: self.current_instance_context.clone(),
        }
    }

    /// If we are currently elaborating a concrete `instance` member body, redirect an explicit
    /// public-looking typeclass attribute like `Add.add[Nat]` to the private instance-impl
    /// constant for that same `(typeclass, datatype, attribute)`.
    ///
    /// This only applies in the temporary "inside an instance body" context. Outside that path,
    /// or for any other typeclass/datatype/attribute combination, we return `None` and let normal
    /// unresolved-constant resolution handle it.
    fn resolve_instance_impl_constant(
        &self,
        unresolved: &UnresolvedConstant,
        type_params: &[AcornType],
        source: &dyn ErrorContext,
    ) -> error::Result<Option<AcornValue>> {
        let Some(context) = &self.current_instance_context else {
            return Ok(None);
        };
        let ConstantName::TypeclassAttribute(_, typeclass, attr_name) = &unresolved.name else {
            return Ok(None);
        };
        if typeclass != &context.typeclass {
            return Ok(None);
        }
        let [AcornType::Data(datatype, datatype_args)] = type_params else {
            return Ok(None);
        };
        if datatype != &context.datatype || !datatype_args.is_empty() {
            return Ok(None);
        }

        let instance_name = InstanceName {
            typeclass: context.typeclass.clone(),
            attribute: attr_name.clone(),
            datatype: context.datatype.clone(),
        };
        let defined_name = DefinedName::Instance(instance_name.clone());

        // This redirect is only valid while we are elaborating the current instance body:
        // either for the member being defined recursively right now, or for another instance
        // member that has already been defined earlier in the same block.
        if attr_name != &context.current_attr
            && self.bindings.get_definition(&defined_name).is_none()
        {
            return Ok(None);
        }

        let resolved_type = unresolved.resolved_type(source, type_params)?;
        Ok(Some(AcornValue::instance_impl_constant(
            context.defining_module,
            instance_name,
            resolved_type,
        )))
    }

    /// Resolves an unresolved constant after type arguments are known.
    ///
    /// The only special case is the temporary instance-member redirect above. If that does not
    /// apply, resolution falls through to the normal inference path.
    fn resolve_unresolved_with_type_params(
        &self,
        unresolved: UnresolvedConstant,
        type_params: Vec<AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        if let Some(value) =
            self.resolve_instance_impl_constant(&unresolved, &type_params, source)?
        {
            return Ok(value);
        }
        self.inference()
            .resolve_unresolved_with_type_params(unresolved, type_params, source)
    }

    fn split_datatype_args(
        datatype_args: &[DependentTypeArg],
    ) -> (Vec<AcornType>, Vec<AcornValue>) {
        let mut type_args = vec![];
        let mut value_args = vec![];
        for arg in datatype_args {
            match arg {
                DependentTypeArg::Type(acorn_type) => type_args.push(acorn_type.clone()),
                DependentTypeArg::Value(value) => value_args.push(value.clone()),
            }
        }
        (type_args, value_args)
    }

    fn datatype_args_for_type(
        base_type: &AcornType,
    ) -> Option<(Datatype, Vec<AcornType>, Vec<DependentTypeArg>)> {
        match base_type {
            AcornType::Data(datatype, type_args) => Some((
                datatype.clone(),
                type_args.clone(),
                type_args
                    .iter()
                    .cloned()
                    .map(DependentTypeArg::Type)
                    .collect(),
            )),
            AcornType::Family(datatype, args) => Some((
                datatype.clone(),
                args.iter()
                    .filter_map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => Some(acorn_type.clone()),
                        DependentTypeArg::Value(_) => None,
                    })
                    .collect(),
                args.clone(),
            )),
            _ => None,
        }
    }

    fn specialize_potential_with_datatype_args(
        &self,
        potential: PotentialValue,
        datatype_args: &[DependentTypeArg],
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let (type_args, value_args) = Self::split_datatype_args(datatype_args);
        if type_args.is_empty() && value_args.is_empty() {
            return Ok(potential);
        }

        match potential {
            PotentialValue::Unresolved(unresolved) => Ok(PotentialValue::Resolved(
                self.resolve_unresolved_with_type_params(unresolved, type_args, source)?
                    .bind_value_params(&value_args, source)?,
            )),
            PotentialValue::Resolved(value) => Ok(PotentialValue::Resolved(
                value.bind_value_params(&value_args, source)?,
            )),
        }
    }

    fn bind_potential_value_args(
        &self,
        potential: PotentialValue,
        value_args: &[AcornValue],
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        if value_args.is_empty() {
            return Ok(potential);
        }

        match potential {
            PotentialValue::Unresolved(unresolved) => {
                if unresolved.value_param_types.len() != value_args.len() {
                    return Err(source.error(&format!(
                        "expected {} family value arguments, but got {}",
                        unresolved.value_param_types.len(),
                        value_args.len()
                    )));
                }

                if unresolved.params.is_empty() {
                    let bound_value = unresolved
                        .resolve(source, vec![])?
                        .bind_value_params(value_args, source)?;
                    Ok(PotentialValue::Resolved(bound_value))
                } else {
                    Ok(PotentialValue::Unresolved(UnresolvedConstant {
                        name: unresolved.name,
                        params: unresolved.params,
                        generic_type: unresolved.generic_type.bind_value_params(value_args),
                        value_param_types: vec![],
                        args: unresolved.args,
                    }))
                }
            }
            PotentialValue::Resolved(value) => Ok(PotentialValue::Resolved(
                value.bind_value_params(value_args, source)?,
            )),
        }
    }

    fn evaluate_datatype_attr_for_type(
        &self,
        base_type: &AcornType,
        attr_name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let Some((datatype, type_args, datatype_args)) = Self::datatype_args_for_type(base_type)
        else {
            return Err(source.error("not an attributable datatype"));
        };

        let (module_id, const_name) = match self
            .bindings
            .resolve_datatype_attr_with_params(&datatype, &type_args, attr_name)
        {
            Ok((module_id, const_name)) => (module_id, const_name),
            Err(err) => return Err(source.error(&err)),
        };

        let bindings = self.get_bindings(module_id);
        let defined_name = DefinedName::Constant(const_name);
        let value = bindings
            .get_constant_value(&defined_name)
            .map_err(|e| source.error(&e))?;
        if !defined_name.is_typeclass_attr() {
            return self.specialize_potential_with_datatype_args(value, &datatype_args, source);
        }

        match value {
            PotentialValue::Unresolved(unresolved) => {
                let resolved = self.resolve_unresolved_with_type_params(
                    unresolved,
                    vec![base_type.clone()],
                    source,
                )?;
                Ok(PotentialValue::Resolved(resolved))
            }
            potential => Ok(potential),
        }
    }

    /// Tracks token information for the given entity.
    fn track_token(&mut self, token: &Token, entity: &NamedEntity) {
        if let Some(token_map) = self.token_map.as_mut() {
            token_map.track_token(token, entity);
        }
    }

    /// Evaluates an expression that represents a type.
    pub fn evaluate_type(&mut self, expression: &Expression) -> error::Result<AcornType> {
        self.evaluate_type_with_stack(&mut Stack::new(), expression)
    }

    pub fn evaluate_type_with_stack(
        &mut self,
        stack: &mut Stack,
        expression: &Expression,
    ) -> error::Result<AcornType> {
        let potential = self.evaluate_potential_type_with_stack(stack, expression)?;
        match potential {
            PotentialType::Resolved(t) => Ok(t),
            PotentialType::Unresolved(ut) => {
                Err(expression.error(&format!("type {} is unresolved", ut.name)))
            }
        }
    }

    /// Evaluates an expression that either represents a type, or represents a type that still needs params.
    pub fn evaluate_potential_type(
        &mut self,
        expression: &Expression,
    ) -> error::Result<PotentialType> {
        self.evaluate_potential_type_with_stack(&mut Stack::new(), expression)
    }

    fn evaluate_potential_type_with_stack(
        &mut self,
        stack: &mut Stack,
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
                        arg_types.push(self.evaluate_type_with_stack(stack, arg_expr)?);
                    }
                    let return_type = self.evaluate_type_with_stack(stack, right)?;
                    Ok(PotentialType::Resolved(AcornType::functional(
                        arg_types,
                        return_type,
                    )))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(stack, expression)?;
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
                let p = self.evaluate_potential_type_with_stack(stack, left)?;
                if let PotentialType::Unresolved(ut) = &p {
                    if ut.params.len() != param_exprs.len() {
                        return Err(expression.error(&format!(
                            "type {} expects {} parameters, but got {}",
                            ut.name,
                            ut.params.len(),
                            param_exprs.len()
                        )));
                    }
                    let mut instance_params = vec![];
                    for (param_expr, param_kind) in param_exprs.iter().zip(&ut.params) {
                        match param_kind {
                            FamilyParamKind::Type(_) => {
                                if self
                                    .fork(self.bindings, None)
                                    .evaluate_type_with_stack(stack, param_expr)
                                    .is_ok()
                                {
                                    instance_params.push(DependentTypeArg::Type(
                                        self.evaluate_type_with_stack(stack, param_expr)?,
                                    ));
                                    continue;
                                }
                                if let Ok(value) = self
                                    .fork(self.bindings, None)
                                    .evaluate_value_with_stack(stack, param_expr, None)
                                {
                                    return Err(self.unsupported_value_type_arg_error(
                                        param_expr,
                                        &value.get_type(),
                                    ));
                                }
                                instance_params.push(DependentTypeArg::Type(
                                    self.evaluate_type_with_stack(stack, param_expr)?,
                                ));
                            }
                            FamilyParamKind::Value(value_type) => {
                                let value = self.evaluate_value_with_stack(
                                    stack,
                                    param_expr,
                                    Some(value_type),
                                )?;
                                instance_params.push(DependentTypeArg::Value(value));
                            }
                        }
                    }
                    let t = p.resolve_args(instance_params, expression)?;
                    return Ok(PotentialType::Resolved(t));
                }
                let mut instance_params = vec![];
                for param_expr in param_exprs {
                    if self
                        .fork(self.bindings, None)
                        .evaluate_type_with_stack(stack, param_expr)
                        .is_ok()
                    {
                        instance_params.push(DependentTypeArg::Type(
                            self.evaluate_type_with_stack(stack, param_expr)?,
                        ));
                        continue;
                    }
                    if let Ok(value) = self
                        .fork(self.bindings, None)
                        .evaluate_value_with_stack(stack, param_expr, None)
                    {
                        return Err(
                            self.unsupported_value_type_arg_error(param_expr, &value.get_type())
                        );
                    }
                    instance_params.push(DependentTypeArg::Type(
                        self.evaluate_type_with_stack(stack, param_expr)?,
                    ));
                }
                let t = p.resolve_args(instance_params, expression)?;
                Ok(PotentialType::Resolved(t))
            }
            Expression::Grouping(_, e, _) => self.evaluate_potential_type_with_stack(stack, e),
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
                let acorn_type = self.evaluate_type_with_stack(&mut Stack::new(), &type_expr)?;
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
                        let self_type = datatype_type.unwrap().clone();
                        names.push("self".to_string());
                        types.push(self_type.clone());
                        stack.insert("self".to_string(), self_type);
                        continue;
                    }
                    _ => {
                        return Err(declaration
                            .token()
                            .error("first argument of a member function must be 'self'"));
                    }
                }
            }
            let (name, acorn_type) = match declaration {
                Declaration::Typed(name_token, type_expr) => (
                    name_token.to_string(),
                    self.evaluate_type_with_stack(stack, type_expr)?,
                ),
                Declaration::SelfToken(name_token) => {
                    return Err(name_token.error("cannot use 'self' as an argument here"));
                }
            };
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
            names.push(name.clone());
            types.push(acorn_type.clone());
            stack.insert(name, acorn_type);
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
                let mut no_token_evaluator = self.fork(self.bindings, None);
                let constructor =
                    no_token_evaluator.evaluate_value(pattern, Some(expected_type))?;
                let (i, total) = self.expect_constructor(expected_type, &constructor, pattern)?;
                return Ok((constructor, vec![], i, total));
            }
        };
        let mut no_token_evaluator = self.fork(self.bindings, None);
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
                self.resolve_unresolved_with_type_params(uc, params.clone(), pattern)?
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
        self.evaluate_datatype_attr_for_type(
            &AcornType::Data(datatype.clone(), vec![]),
            attr_name,
            source,
        )
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
            AcornType::Data(_, _) | AcornType::Family(_, _) => {
                let Some((datatype, type_args, datatype_args)) =
                    Self::datatype_args_for_type(&base_type)
                else {
                    unreachable!("data and family types should be attributable");
                };
                let (module_id, const_name) = match self
                    .bindings
                    .resolve_datatype_attr_with_params(&datatype, &type_args, attr_name)
                {
                    Ok((module_id, const_name)) => (module_id, const_name),
                    Err(err) => return Err(source.error(&err)),
                };

                let bindings = self.get_bindings(module_id);
                let defined_name = DefinedName::Constant(const_name);
                let value = bindings
                    .get_constant_value(&defined_name)
                    .map_err(|e| source.error(&e))?;
                if !defined_name.is_typeclass_attr() {
                    let (_type_args, value_args) = Self::split_datatype_args(&datatype_args);
                    self.bind_potential_value_args(value, &value_args, source)?
                } else if let PotentialValue::Unresolved(unresolved) = value {
                    let resolved = self.resolve_unresolved_with_type_params(
                        unresolved,
                        vec![base_type.clone()],
                        source,
                    )?;
                    PotentialValue::Resolved(resolved)
                } else {
                    value
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
                    AcornType::Data(_, _) | AcornType::Family(_, _) => {
                        if name_token.token_type == TokenType::Numeral {
                            let datatype = t.get_datatype(name_token)?;
                            let value = self.evaluate_number_with_datatype(
                                name_token,
                                datatype,
                                name_token.text(),
                            )?;
                            NamedEntity::Value(value)
                        } else {
                            match self.evaluate_datatype_attr_for_type(&t, name, name_token)? {
                                PotentialValue::Resolved(value) => NamedEntity::Value(value),
                                PotentialValue::Unresolved(u) => {
                                    let Some((_datatype, _type_args, datatype_args)) =
                                        Self::datatype_args_for_type(&t)
                                    else {
                                        unreachable!("type namespace should be attributable here");
                                    };
                                    if datatype_args.is_empty() {
                                        // Leave it unresolved
                                        NamedEntity::UnresolvedValue(u)
                                    } else {
                                        let value = self
                                            .specialize_potential_with_datatype_args(
                                                PotentialValue::Unresolved(u),
                                                &datatype_args,
                                                name_token,
                                            )?
                                            .force_value();
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
                                let value = self.resolve_unresolved_with_type_params(
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
                    self.fork(bindings, None)
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
                let Some(datatype) = ut.base_datatype() else {
                    return Err(name_token.error("this type cannot have attributes"));
                };
                match self.evaluate_datatype_attr(datatype, name, name_token)? {
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
            let acorn_type = self.evaluate_type_with_stack(stack, expression)?;
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
        if let Some(token) = Self::operator_ref_token(expression) {
            return self.operator_ref_value(token, stack.len(), None, true);
        }
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
        let left_is_operator_ref = Self::operator_ref_token(left).is_some();
        let right_is_operator_ref = Self::operator_ref_token(right).is_some();

        if left_is_operator_ref {
            let right_potential = self.evaluate_potential_value(stack, right, None)?;
            let right_value = self
                .inference()
                .maybe_resolve_value(right_potential, None, right)?
                .as_value(right)?;
            let left_value =
                self.evaluate_value_with_stack(stack, left, Some(&right_value.get_type()))?;
            return Ok((left_value, right_value));
        }

        if right_is_operator_ref {
            let left_potential = self.evaluate_potential_value(stack, left, left_expected)?;
            let left_value = self
                .inference()
                .maybe_resolve_value(left_potential, left_expected, left)?
                .as_value(left)?;
            let right_value =
                self.evaluate_value_with_stack(stack, right, Some(&left_value.get_type()))?;
            return Ok((left_value, right_value));
        }

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
                TokenType::ForAll | TokenType::Exists | TokenType::Function | TokenType::Choose => {
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
                        PotentialValue::Unresolved(u) => {
                            self.resolve_unresolved_with_type_params(u, type_params.clone(), token)?
                        }
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
                if let Expression::Grouping(left_delimiter, e, _) = args_expr.as_ref() {
                    if left_delimiter.token_type == TokenType::LeftParen {
                        let arg_exprs = e.flatten_comma_separated_list();
                        if let Some(result) = self.try_operator_ref_application(
                            stack,
                            expression,
                            function_expr,
                            &arg_exprs,
                            expected_type,
                        ) {
                            return Ok(PotentialValue::Resolved(result?));
                        }
                    }
                }

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
                    for type_param in self.evaluate_type_params(type_params)? {
                        type_param_names.push(type_param.name.clone());
                        type_param_constraints.push(type_param.typeclass.clone());
                        let potential =
                            PotentialType::Resolved(AcornType::Arbitrary(type_param.clone()));
                        new_bindings.add_type_alias(&type_param.name, potential, token)?;
                    }

                    // Create a new evaluator with the modified bindings
                    let mut evaluator = self.fork(&new_bindings, None);

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
                                let resolved = self.resolve_unresolved_with_type_params(
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
                if let Expression::Singleton(token) = e.as_ref() {
                    if token.token_type.is_operator_ref() {
                        self.operator_ref_value(token, stack.len(), expected_type, false)?
                    } else {
                        self.evaluate_value_with_stack(stack, e, expected_type)?
                    }
                } else {
                    self.evaluate_value_with_stack(stack, e, expected_type)?
                }
            }
            Expression::Binder(token, args, body, _) => {
                if token.token_type == TokenType::Choose {
                    return Err(token.error("choose expressions are not supported"));
                }
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
                    let constructor_index = u16::try_from(i).map_err(|_| {
                        expression.error("too many datatype constructors for match metadata")
                    })?;
                    let constructor_total = u16::try_from(total).map_err(|_| {
                        expression.error("too many datatype constructors for match metadata")
                    })?;
                    cases.push(MatchCase {
                        new_vars: arg_types,
                        pattern,
                        result,
                        constructor_index,
                        constructor_total,
                    });
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

    fn unsupported_value_param_error(
        &self,
        name_token: &Token,
        value_type: &AcornType,
    ) -> error::Error {
        name_token.error(&format!(
            "dependent value parameters like '{}: {}' are not supported here yet",
            name_token.text(),
            value_type
        ))
    }

    fn unsupported_value_type_arg_error(
        &self,
        expression: &Expression,
        value_type: &AcornType,
    ) -> error::Error {
        expression.error(&format!(
            "dependent type arguments like '{}: {}' are not supported here yet",
            expression, value_type
        ))
    }

    pub fn evaluate_family_params(
        &mut self,
        exprs: &[TypeParamExpr],
    ) -> error::Result<Vec<FamilyParam>> {
        let mut answer: Vec<FamilyParam> = vec![];
        for expr in exprs {
            if expr.type_expr.is_some() {
                return Err(expr.name.error(
                    "parameter binders must be simple identifiers, not complex type expressions",
                ));
            }

            if let Some(annotation) = expr.typeclass.as_ref() {
                if self
                    .fork(self.bindings, None)
                    .evaluate_typeclass(annotation)
                    .is_ok()
                {
                    let typeclass = self.evaluate_typeclass(annotation)?;
                    let param = FamilyParam::Type(TypeParam {
                        name: expr.name.text().to_string(),
                        typeclass: Some(typeclass),
                    });
                    if answer
                        .iter()
                        .any(|existing| existing.name() == param.name())
                    {
                        return Err(expr.name.error("duplicate parameter"));
                    }
                    answer.push(param);
                    continue;
                }
                if let Ok(value_type) = self.fork(self.bindings, None).evaluate_type(annotation) {
                    let param = FamilyParam::Value(ValueParam {
                        name: expr.name.text().to_string(),
                        value_type,
                    });
                    if answer
                        .iter()
                        .any(|existing| existing.name() == param.name())
                    {
                        return Err(expr.name.error("duplicate parameter"));
                    }
                    answer.push(param);
                    continue;
                }
                return Err(annotation.error("expected a typeclass constraint or a value type"));
            }

            let param = FamilyParam::Type(TypeParam {
                name: expr.name.text().to_string(),
                typeclass: None,
            });
            if answer
                .iter()
                .any(|existing| existing.name() == param.name())
            {
                return Err(expr.name.error("duplicate parameter"));
            }
            answer.push(param);
        }
        Ok(answer)
    }

    /// Evaluates a list of type parameter expressions.
    /// This does not bind them into the environment.
    pub fn evaluate_type_params(
        &mut self,
        exprs: &[TypeParamExpr],
    ) -> error::Result<Vec<TypeParam>> {
        let mut answer: Vec<TypeParam> = vec![];
        let params = self.evaluate_family_params(exprs)?;
        for (expr, param) in exprs.iter().zip(params) {
            match param {
                FamilyParam::Type(type_param) => {
                    self.bindings
                        .check_typename_available(&type_param.name, &expr.name)?;
                    if answer.iter().any(|tp| tp.name == type_param.name) {
                        return Err(expr.name.error("duplicate type parameter"));
                    }
                    answer.push(type_param);
                }
                FamilyParam::Value(value_param) => {
                    return Err(
                        self.unsupported_value_param_error(&expr.name, &value_param.value_type)
                    );
                }
            }
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
                let annotation = expr.typeclass.as_ref().unwrap();
                if self
                    .fork(self.bindings, None)
                    .evaluate_typeclass(annotation)
                    .is_ok()
                {
                    generic_count += 1;
                } else if let Ok(value_type) =
                    self.fork(self.bindings, None).evaluate_type(annotation)
                {
                    return Err(self.unsupported_value_param_error(&expr.name, &value_type));
                } else {
                    return Err(
                        annotation.error("expected a typeclass constraint or a concrete type")
                    );
                }
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
    use crate::elaborator::acorn_type::FamilyParamKind;
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

        fn parse_type_params(input: &str) -> Vec<TypeParamExpr> {
            let tokens = Token::scan(input);
            let mut tokens = TokenIter::new(tokens);
            TypeParamExpr::parse_list(&mut tokens).unwrap()
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

    #[test]
    fn test_evaluate_family_params_classifies_type_and_value_params() {
        let project = Project::new_mock();
        let mut bindings = BindingMap::new(ModuleId(0));
        bindings
            .add_typeclass(
                "Ring",
                vec![],
                vec![],
                None,
                None,
                &project,
                &Token::empty(),
            )
            .unwrap();
        let mut evaluator = Evaluator::new(&project, &bindings, None);
        let family_params = evaluator
            .evaluate_family_params(&Evaluator::parse_type_params("[T, n: Bool, R: Ring]"))
            .unwrap();
        let kinds: Vec<_> = family_params.iter().map(|param| param.kind()).collect();
        assert_eq!(
            kinds,
            vec![
                FamilyParamKind::Type(None),
                FamilyParamKind::Value(AcornType::Bool),
                FamilyParamKind::Type(Some(Typeclass {
                    module_id: ModuleId(0),
                    name: "Ring".to_string(),
                })),
            ]
        );
    }

    #[test]
    fn test_instance_member_context_redirects_explicit_typeclass_attr_to_internal_constant() {
        let project = Project::new_mock();
        let bindings = BindingMap::new(ModuleId(0));
        let typeclass = Typeclass {
            module_id: ModuleId(0),
            name: "Add".to_string(),
        };
        let datatype = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let instance_name = InstanceName {
            typeclass: typeclass.clone(),
            attribute: "add".to_string(),
            datatype: datatype.clone(),
        };
        let evaluator =
            Evaluator::new_for_instance_member(&project, &bindings, None, &instance_name);
        let unresolved = UnresolvedConstant {
            name: ConstantName::typeclass_attr(ModuleId(0), typeclass.clone(), "add"),
            params: vec![TypeParam {
                name: "Self".to_string(),
                typeclass: Some(typeclass.clone()),
            }],
            generic_type: AcornType::functional(
                vec![
                    AcornType::Variable(TypeParam {
                        name: "Self".to_string(),
                        typeclass: Some(typeclass.clone()),
                    }),
                    AcornType::Variable(TypeParam {
                        name: "Self".to_string(),
                        typeclass: Some(typeclass.clone()),
                    }),
                ],
                AcornType::Variable(TypeParam {
                    name: "Self".to_string(),
                    typeclass: Some(typeclass),
                }),
            ),
            value_param_types: vec![],
            args: vec![],
        };

        let resolved = evaluator
            .resolve_instance_impl_constant(
                &unresolved,
                &[AcornType::Data(datatype.clone(), vec![])],
                &Token::empty(),
            )
            .expect("resolution should succeed")
            .expect("instance context should redirect matching typeclass attrs");

        let AcornValue::Constant(constant) = resolved else {
            panic!("expected a constant");
        };
        assert!(constant.params.is_empty());
        assert!(matches!(
            constant.name,
            ConstantName::InstanceAttribute(ModuleId(0), ref inst)
                if *inst == instance_name
        ));
    }
}
