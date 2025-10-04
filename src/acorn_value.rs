use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornType, Datatype, TypeParam, Typeclass};
use crate::atom::AtomId;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::names::{ConstantName, DefinedName, InstanceName};
use crate::token::TokenType;

/// Represents a function application with a function and its arguments.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    /// The function being applied
    pub function: Box<AcornValue>,
    /// The arguments to the function
    pub args: Vec<AcornValue>,
}

impl FunctionApplication {
    /// Gets the type of this function application result
    pub fn get_type(&self) -> AcornType {
        match self.function.get_type() {
            AcornType::Function(ftype) => ftype.applied_type(self.args.len()),
            _ => panic!("FunctionApplication's function is not a function type"),
        }
    }

    /// Helper function for formatting function applications
    fn fmt_helper(&self, f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
        write!(f, "{}(", Subvalue::new(&self.function, stack_size))?;
        fmt_values(&self.args, f, stack_size)?;
        write!(f, ")")
    }

    /// Iterates over the spine of the application: first the function, then the arguments
    pub fn iter_spine(&self) -> impl Iterator<Item = &AcornValue> {
        std::iter::once(self.function.as_ref()).chain(self.args.iter())
    }

    /// Typechecks this function application
    fn typecheck(&self) -> Result<(), String> {
        let function_type = self.function.get_type();
        if let AcornType::Function(ftype) = function_type {
            if ftype.arg_types.len() < self.args.len() {
                return Err(format!(
                    "Function application has {} arguments, but expected {}",
                    self.args.len(),
                    ftype.arg_types.len()
                ));
            }
            for (i, (arg, arg_type)) in self.args.iter().zip(ftype.arg_types.iter()).enumerate() {
                if !arg.is_type(arg_type) {
                    return Err(format!(
                        "Argument {} has type {}, but expected {}",
                        i,
                        arg.get_type(),
                        arg_type
                    ));
                }
            }
            Ok(())
        } else {
            Err(format!(
                "Function application has function of type {}",
                function_type
            ))
        }
    }
}

/// Represents binary operators used in Acorn
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BinaryOp {
    Implies,
    Equals,
    NotEquals,
    And,
    Or,
}

impl BinaryOp {
    /// Converts this binary operator to its corresponding token type
    pub fn token_type(&self) -> TokenType {
        match self {
            BinaryOp::Implies => TokenType::Implies,
            BinaryOp::Equals => TokenType::Equals,
            BinaryOp::NotEquals => TokenType::NotEquals,
            BinaryOp::And => TokenType::And,
            BinaryOp::Or => TokenType::Or,
        }
    }

    pub fn is_comparison(&self) -> bool {
        matches!(self, BinaryOp::Equals | BinaryOp::NotEquals)
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.token_type().to_str())
    }
}
/// An instance of a constant. Could be generic or not.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct ConstantInstance {
    /// The name of this constant
    pub name: ConstantName,

    /// The type parameters that this constant was instantiated with, if any.
    /// Ordered the same way as in the definition.
    pub params: Vec<AcornType>,

    /// The type of the instance, after instantiation.
    pub instance_type: AcornType,
}

impl fmt::Display for ConstantInstance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.params.is_empty() {
            let types: Vec<_> = self.params.iter().map(|t| t.to_string()).collect();
            write!(f, "[{}]", types.join(", "))?;
        }
        Ok(())
    }
}

impl ConstantInstance {
    /// Make another constant with the same name as this one.
    fn same_name(&self, params: Vec<AcornType>, instance_type: AcornType) -> ConstantInstance {
        ConstantInstance {
            name: self.name.clone(),
            params,
            instance_type,
        }
    }

    pub fn instantiate(&self, params: &[(String, AcornType)]) -> ConstantInstance {
        self.same_name(
            self.params.iter().map(|t| t.instantiate(params)).collect(),
            self.instance_type.instantiate(params),
        )
    }

    pub fn has_generic(&self) -> bool {
        self.params.iter().any(|t| t.has_generic()) || self.instance_type.has_generic()
    }

    /// Change the arbitrary types in this list of parameters to generic ones.
    pub fn genericize(&self, params: &[TypeParam]) -> ConstantInstance {
        let instance_type = self.instance_type.genericize(params);
        let params = if instance_type.has_generic() && self.params.is_empty() {
            // This constant is defined in terms of the arbitrary type, but now we are
            // genericizing it.
            // The only situation I can think of where this happens is when we define
            // a generic function recursively. The recursive reference uses arbitrary types,
            // but the function itself should be generic after genericizing.
            // Thus, to handle this case correctly, we add on the parameters.
            // In particular, the parameters need to be in the same order as they were in the
            // function definition, here. If you run into this comment later while trying to make
            // the parameters unordered, you've now run into a tricky bit.
            params
                .iter()
                .map(|param| AcornType::Variable(param.clone()))
                .collect()
        } else {
            // Just genericize what we started with, same as usual
            self.params.iter().map(|t| t.genericize(params)).collect()
        };
        self.same_name(params, instance_type)
    }

    fn has_arbitrary(&self) -> bool {
        self.params.iter().any(|t| t.has_arbitrary())
    }

    pub fn to_arbitrary(&self) -> ConstantInstance {
        self.same_name(
            self.params.iter().map(|t| t.to_arbitrary()).collect(),
            self.instance_type.to_arbitrary(),
        )
    }

    /// If this value is a typeclass attribute with the specific typeclass and class, convert
    /// it to the name used in its definition.
    pub fn to_defined_instance_name(
        &self,
        typeclass: &Typeclass,
        datatype: &Datatype,
    ) -> Option<DefinedName> {
        if self.name.module_id() != typeclass.module_id {
            return None;
        }
        if let Some((_, receiver, attribute)) = self.name.as_attribute() {
            if receiver == &typeclass.name && self.params.len() == 1 {
                if let AcornType::Data(param_datatype, _) = &self.params[0] {
                    if param_datatype == datatype {
                        return Some(DefinedName::Instance(InstanceName {
                            typeclass: typeclass.clone(),
                            attribute: attribute.to_string(),
                            datatype: datatype.clone(),
                        }));
                    }
                }
            }
        }
        None
    }

    /// Returns None if this is not a synthetic atom, or if its id is not in the map.
    fn replace_synthetic(
        &self,
        module_id: ModuleId,
        synthetic_names: &HashMap<AtomId, String>,
    ) -> Option<ConstantInstance> {
        let id = self.name.synthetic_id()?;
        let name = synthetic_names.get(&id)?;
        assert!(self.params.is_empty());
        Some(ConstantInstance {
            name: ConstantName::unqualified(module_id, name),
            params: vec![],
            instance_type: self.instance_type.clone(),
        })
    }
}

/// Two AcornValue compare to equal if they are structurally identical.
/// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum AcornValue {
    /// A variable that is bound to a value on the stack.
    /// Represented by (stack index, type).
    Variable(AtomId, AcornType),

    Constant(ConstantInstance),

    Application(FunctionApplication),

    /// A function definition that introduces variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    /// The boolean binary operators are treated specially during inference
    Binary(BinaryOp, Box<AcornValue>, Box<AcornValue>),

    Not(Box<AcornValue>),

    /// Quantifiers that introduce variables onto the stack.
    ForAll(Vec<AcornType>, Box<AcornValue>),
    Exists(Vec<AcornType>, Box<AcornValue>),

    /// A plain old bool. True or false
    Bool(bool),

    /// If-then-else requires all parts: condition, if-value, else-value.
    IfThenElse(Box<AcornValue>, Box<AcornValue>, Box<AcornValue>),

    /// The first value is the one being matched (the scrutinee).
    /// The scrutinee needs to be evaluated in the outside context.
    /// Each triple represents a case. The types express which variables are getting bound,
    /// the first value is the pattern, and the final value is the result.
    Match(
        Box<AcornValue>,
        Vec<(Vec<AcornType>, AcornValue, AcornValue)>,
    ),
}

/// An AcornValue has an implicit stack size that determines what index new stack variables
/// will have.
/// The Subvalue includes this implicit stack size.
/// The stack size of a "root" AcornValue is always zero.
struct Subvalue<'a> {
    value: &'a AcornValue,
    stack_size: usize,
}

/// This is a formatting helper, doing a "best effort" that should always display *something*
/// but should not be used for generating usable code.
/// It may reuse temporary variable names, or use constants that have not been imported.
impl fmt::Display for Subvalue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            AcornValue::Variable(i, _) => write!(f, "x{}", i),
            AcornValue::Application(a) => a.fmt_helper(f, self.stack_size),
            AcornValue::Lambda(args, body) => {
                fmt_binder(f, "function", args, body, self.stack_size)
            }
            AcornValue::Binary(op, left, right) => {
                write!(
                    f,
                    "({} {} {})",
                    Subvalue::new(left, self.stack_size),
                    op,
                    Subvalue::new(right, self.stack_size)
                )
            }
            AcornValue::Not(a) => {
                write!(f, "not {}", Subvalue::new(a, self.stack_size))
            }
            AcornValue::ForAll(args, body) => fmt_binder(f, "forall", args, body, self.stack_size),
            AcornValue::Exists(args, body) => fmt_binder(f, "exists", args, body, self.stack_size),
            AcornValue::Constant(c) => {
                write!(f, "{}", c)
            }
            AcornValue::Bool(b) => write!(f, "{}", b),
            AcornValue::IfThenElse(cond, if_value, else_value) => write!(
                f,
                "if {} {{ {} }} else {{ {} }}",
                Subvalue::new(cond, self.stack_size),
                Subvalue::new(if_value, self.stack_size),
                Subvalue::new(else_value, self.stack_size)
            ),
            AcornValue::Match(scrutinee, cases) => {
                write!(f, "match {} {{", Subvalue::new(scrutinee, self.stack_size))?;
                for (new_vars, pattern, result) in cases {
                    let new_stack_size = self.stack_size + new_vars.len();
                    write!(
                        f,
                        " {} {{ {} }}",
                        Subvalue::new(pattern, new_stack_size),
                        Subvalue::new(result, new_stack_size)
                    )?;
                }
                write!(f, " }}")
            }
        }
    }
}

impl Subvalue<'_> {
    fn new(value: &AcornValue, stack_size: usize) -> Subvalue {
        Subvalue { value, stack_size }
    }

    fn root(value: &AcornValue) -> Subvalue {
        Subvalue::new(value, 0)
    }
}

fn fmt_values(v: &Vec<AcornValue>, f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
    for (i, item) in v.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", Subvalue::new(item, stack_size))?;
    }
    Ok(())
}

fn fmt_binder(
    f: &mut fmt::Formatter,
    name: &str,
    decs: &Vec<AcornType>,
    body: &AcornValue,
    stack_size: usize,
) -> fmt::Result {
    write!(
        f,
        "{}({}) {{ {} }}",
        name,
        AcornType::decs_to_str(decs, stack_size),
        Subvalue::new(body, stack_size + decs.len())
    )
}

impl fmt::Display for AcornValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Subvalue::root(self).fmt(f)
    }
}

impl AcornValue {
    pub fn get_type(&self) -> AcornType {
        match self {
            AcornValue::Variable(_, t) => t.clone(),
            AcornValue::Application(t) => t.get_type(),
            AcornValue::Lambda(args, return_value) => {
                AcornType::functional(args.clone(), return_value.get_type())
            }
            AcornValue::Binary(_, _, _) => AcornType::Bool,
            AcornValue::Not(_) => AcornType::Bool,
            AcornValue::ForAll(_, _) => AcornType::Bool,
            AcornValue::Exists(_, _) => AcornType::Bool,
            AcornValue::Constant(c) => c.instance_type.clone(),
            AcornValue::Bool(_) => AcornType::Bool,
            AcornValue::IfThenElse(_, if_value, _) => if_value.get_type(),
            AcornValue::Match(_, cases) => {
                if let Some((_, _, result)) = cases.first() {
                    result.get_type()
                } else {
                    panic!("Match with no cases");
                }
            }
        }
    }

    pub fn is_type(&self, t: &AcornType) -> bool {
        match self {
            AcornValue::Variable(_, var_type) => var_type == t,
            AcornValue::Application(app) => app.get_type() == *t,
            AcornValue::Lambda(args, return_value) => {
                if let AcornType::Function(ftype) = t {
                    args == &ftype.arg_types && return_value.is_type(&ftype.return_type)
                } else {
                    false
                }
            }
            AcornValue::Binary(_, _, _) => *t == AcornType::Bool,
            AcornValue::Not(_) => *t == AcornType::Bool,
            AcornValue::ForAll(_, _) => *t == AcornType::Bool,
            AcornValue::Exists(_, _) => *t == AcornType::Bool,
            AcornValue::Constant(c) => c.instance_type == *t,
            AcornValue::Bool(_) => *t == AcornType::Bool,
            AcornValue::IfThenElse(_, if_value, _) => if_value.is_type(t),
            AcornValue::Match(_, cases) => {
                if let Some((_, _, result)) = cases.first() {
                    result.is_type(t)
                } else {
                    false
                }
            }
        }
    }

    pub fn is_bool_type(&self) -> bool {
        self.is_type(&AcornType::Bool)
    }

    /// Construct an application if we have arguments, but omit it otherwise.
    /// Be careful - if we apply to the wrong type, this just creates an internally invalid value.
    pub fn apply(function: AcornValue, args: Vec<AcornValue>) -> AcornValue {
        if args.is_empty() {
            function
        } else {
            AcornValue::Application(FunctionApplication {
                function: Box::new(function),
                args,
            })
        }
    }

    /// Recursively extract the base function from applications.
    /// For example, if we have f(a)(b)(c), this returns f.
    /// This is useful for getting the original function from partial applications.
    pub fn unapply(&self) -> &AcornValue {
        match self {
            AcornValue::Application(app) => app.function.unapply(),
            _ => self,
        }
    }

    /// Construct a lambda if we have arguments, but omit it otherwise.
    pub fn lambda(args: Vec<AcornType>, value: AcornValue) -> AcornValue {
        if args.is_empty() {
            value
        } else {
            AcornValue::Lambda(args, Box::new(value))
        }
    }

    /// Construct a forall if we have arguments, but omit it otherwise.
    pub fn forall(args: Vec<AcornType>, value: AcornValue) -> AcornValue {
        if args.is_empty() {
            value
        } else {
            AcornValue::ForAll(args, Box::new(value))
        }
    }

    /// Construct an exists if we have arguments, but omit it otherwise.
    pub fn exists(args: Vec<AcornType>, value: AcornValue) -> AcornValue {
        if args.is_empty() {
            value
        } else {
            AcornValue::Exists(args, Box::new(value))
        }
    }

    /// Creates an implication binary operation
    pub fn implies(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::Implies, Box::new(left), Box::new(right))
    }

    /// Creates an equality binary operation
    pub fn equals(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::Equals, Box::new(left), Box::new(right))
    }

    /// Creates an inequality binary operation
    pub fn not_equals(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::NotEquals, Box::new(left), Box::new(right))
    }

    /// Creates a logical AND binary operation
    pub fn and(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::And, Box::new(left), Box::new(right))
    }

    /// Creates a logical OR binary operation
    pub fn or(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::Or, Box::new(left), Box::new(right))
    }

    /// Make a constant for an instance attribute.
    pub fn instance_constant(instance_name: InstanceName, instance_type: AcornType) -> AcornValue {
        let name = ConstantName::typeclass_attr(instance_name.typeclass, &instance_name.attribute);
        let param = AcornType::Data(instance_name.datatype, vec![]);
        let ci = ConstantInstance {
            name,
            params: vec![param],
            instance_type,
        };
        AcornValue::Constant(ci)
    }

    /// Creates a constant value
    pub fn constant(
        name: ConstantName,
        params: Vec<AcornType>,
        instance_type: AcornType,
    ) -> AcornValue {
        let ci = ConstantInstance {
            name,
            params,
            instance_type,
        };
        AcornValue::Constant(ci)
    }

    /// Checks if this value is a lambda function
    pub fn is_lambda(&self) -> bool {
        match self {
            AcornValue::Lambda(_, _) => true,
            _ => false,
        }
    }

    /// Whether this value can be converted to a term, rather than requiring a literal or clause.
    /// Terms can have no boolean operators, lambdas, etc.
    pub fn is_term(&self) -> bool {
        match self {
            AcornValue::Variable(_, _) => true,
            AcornValue::Application(app) => {
                app.args.iter().all(|x| x.is_term()) && app.function.is_term()
            }
            AcornValue::Lambda(_, _) => false,
            AcornValue::Binary(_, _, _) => false,
            AcornValue::Not(_) => false,
            AcornValue::ForAll(_, _) => false,
            AcornValue::Exists(_, _) => false,
            AcornValue::Constant(_) => true,

            // Bit of a weird case. "true" is a term but "false" is not.
            AcornValue::Bool(value) => *value,

            AcornValue::IfThenElse(_, _, _) => false,
            AcornValue::Match(..) => false,
        }
    }

    /// Negates this value
    pub fn negate(self) -> AcornValue {
        match self {
            AcornValue::Not(x) => *x,
            AcornValue::Binary(BinaryOp::Equals, x, y) => {
                AcornValue::Binary(BinaryOp::NotEquals, x, y)
            }
            AcornValue::Binary(BinaryOp::NotEquals, x, y) => {
                AcornValue::Binary(BinaryOp::Equals, x, y)
            }
            AcornValue::Bool(b) => AcornValue::Bool(!b),
            _ => AcornValue::Not(Box::new(self)),
        }
    }

    /// Negates, but pushes the negation inwards when possible.
    pub fn pretty_negate(self) -> AcornValue {
        match self {
            AcornValue::Not(x) => *x,
            AcornValue::Binary(BinaryOp::Equals, x, y) => {
                AcornValue::Binary(BinaryOp::NotEquals, x, y)
            }
            AcornValue::Binary(BinaryOp::NotEquals, x, y) => {
                AcornValue::Binary(BinaryOp::Equals, x, y)
            }
            AcornValue::Binary(BinaryOp::Or, x, y) => {
                AcornValue::and(x.pretty_negate(), y.pretty_negate())
            }
            AcornValue::Binary(BinaryOp::And, x, y) => {
                AcornValue::or(x.pretty_negate(), y.pretty_negate())
            }
            AcornValue::Binary(BinaryOp::Implies, x, y) => AcornValue::and(*x, y.pretty_negate()),
            AcornValue::Bool(b) => AcornValue::Bool(!b),
            AcornValue::ForAll(quants, value) => AcornValue::exists(quants, value.pretty_negate()),
            AcornValue::Exists(quants, value) => AcornValue::forall(quants, value.pretty_negate()),
            _ => AcornValue::Not(Box::new(self)),
        }
    }

    /// Binds the provided values to stack variables.
    ///
    /// The first_binding_index is the first index that we should bind to.
    /// For example, if stack_index is 2, and the values
    /// are "foo", "bar", and "baz" we should set x2 = foo, x3 = bar, x4 = baz.
    /// Any subsequent variables, x5 x6 x7 etc, should be renumbered downwards.
    ///
    /// The stack_size is the size of the stack where this value occurs. This is relevant because any
    /// variables in the bound values will be moved into this environment, so we need to renumber
    /// their variables appropriately.
    pub fn bind_values(
        self,
        first_binding_index: AtomId,
        stack_size: AtomId,
        values: &[AcornValue],
    ) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                if i < first_binding_index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, var_type);
                }
                if i < first_binding_index + values.len() as AtomId {
                    // This reference is bound to a new value
                    let new_value = values[(i - first_binding_index) as usize].clone();

                    // We are moving this value between contexts with possibly different stack sizes
                    assert!(stack_size >= first_binding_index);
                    return new_value
                        .insert_stack(first_binding_index, stack_size - first_binding_index);
                }
                // This reference just needs to be shifted
                AcornValue::Variable(i - values.len() as AtomId, var_type)
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.bind_values(
                    first_binding_index,
                    stack_size,
                    values,
                )),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.bind_values(first_binding_index, stack_size, values))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => {
                let return_value_stack_size = stack_size + args.len() as AtomId;
                AcornValue::Lambda(
                    args,
                    Box::new(return_value.bind_values(
                        first_binding_index,
                        return_value_stack_size,
                        values,
                    )),
                )
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
                Box::new(left.bind_values(first_binding_index, stack_size, values)),
                Box::new(right.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.bind_values(
                first_binding_index,
                stack_size,
                values,
            ))),
            AcornValue::ForAll(quants, value) => {
                let value_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::ForAll(
                    quants,
                    Box::new(value.bind_values(first_binding_index, value_stack_size, values)),
                )
            }
            AcornValue::Exists(quants, value) => {
                let value_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(
                    quants,
                    Box::new(value.bind_values(first_binding_index, value_stack_size, values)),
                )
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.bind_values(first_binding_index, stack_size, values)),
                Box::new(if_value.bind_values(first_binding_index, stack_size, values)),
                Box::new(else_value.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.bind_values(first_binding_index, stack_size, values);
                let new_cases = cases
                    .into_iter()
                    .map(|(new_vars, pattern, result)| {
                        let new_stack_size = stack_size + new_vars.len() as AtomId;
                        (
                            new_vars,
                            pattern.bind_values(first_binding_index, new_stack_size, values),
                            result.bind_values(first_binding_index, new_stack_size, values),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Constant(_) | AcornValue::Bool(_) => self,
        }
    }

    /// Inserts 'increment' stack entries, starting with the provided index, that this value
    /// doesn't use.
    /// This moves the value from a context that has 'index' stack entries, to one that
    /// has 'index + increment' entries.
    /// Every reference at index or higher should be incremented by increment.
    pub fn insert_stack(self, index: AtomId, increment: AtomId) -> AcornValue {
        if increment == 0 {
            return self;
        }
        match self {
            AcornValue::Variable(i, var_type) => {
                if i < index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, var_type);
                }
                // This reference just needs to be shifted
                AcornValue::Variable(i + increment, var_type)
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.insert_stack(index, increment)),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.insert_stack(index, increment))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => {
                AcornValue::Lambda(args, Box::new(return_value.insert_stack(index, increment)))
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.insert_stack(index, increment))),
            AcornValue::ForAll(quants, value) => {
                AcornValue::ForAll(quants, Box::new(value.insert_stack(index, increment)))
            }
            AcornValue::Exists(quants, value) => {
                AcornValue::Exists(quants, Box::new(value.insert_stack(index, increment)))
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.insert_stack(index, increment)),
                Box::new(if_value.insert_stack(index, increment)),
                Box::new(else_value.insert_stack(index, increment)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.insert_stack(index, increment);
                let new_cases = cases
                    .into_iter()
                    .map(|(new_vars, pattern, result)| {
                        (
                            new_vars,
                            pattern.insert_stack(index, increment),
                            result.insert_stack(index, increment),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Constant(_) | AcornValue::Bool(_) => self,
        }
    }

    /// Attempts to remove all lambdas from a value.
    ///
    /// Replaces lambda(...) { value } (args) by substituting the args into the value.
    ///
    /// stack_size is the number of variables that are already on the stack.
    pub fn expand_lambdas(&self, stack_size: AtomId) -> AcornValue {
        match self {
            AcornValue::Application(app) => {
                let function = app.function.expand_lambdas(stack_size);
                if let AcornValue::Lambda(_, return_value) = function {
                    // Expand the lambda
                    let expanded = return_value.bind_values(stack_size, stack_size, &app.args);
                    expanded.expand_lambdas(stack_size)
                } else {
                    AcornValue::Application(FunctionApplication {
                        function: Box::new(function),
                        args: app
                            .args
                            .iter()
                            .map(|x| x.expand_lambdas(stack_size))
                            .collect(),
                    })
                }
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.expand_lambdas(stack_size))),
            AcornValue::ForAll(quants, value) => {
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::ForAll(
                    quants.clone(),
                    Box::new(value.expand_lambdas(new_stack_size)),
                )
            }
            AcornValue::Exists(quants, value) => {
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(
                    quants.clone(),
                    Box::new(value.expand_lambdas(new_stack_size)),
                )
            }
            AcornValue::Lambda(args, value) => {
                let new_stack_size = stack_size + args.len() as AtomId;
                AcornValue::Lambda(args.clone(), Box::new(value.expand_lambdas(new_stack_size)))
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.expand_lambdas(stack_size)),
                Box::new(if_value.expand_lambdas(stack_size)),
                Box::new(else_value.expand_lambdas(stack_size)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.expand_lambdas(stack_size);
                let new_cases = cases
                    .iter()
                    .map(|(new_vars, pattern, result)| {
                        let new_stack_size = stack_size + new_vars.len() as AtomId;
                        (
                            new_vars.clone(),
                            pattern.expand_lambdas(new_stack_size),
                            result.expand_lambdas(new_stack_size),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Variable(_, _) | AcornValue::Constant(_) | AcornValue::Bool(_) => {
                self.clone()
            }
        }
    }

    /// Removes all "and" nodes, collecting the conjuncts into a vector.
    pub fn remove_and(&self) -> Vec<AcornValue> {
        let mut output = vec![];
        self.remove_and_helper(&mut output);
        output
    }

    fn remove_and_helper(&self, output: &mut Vec<AcornValue>) {
        match self {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                left.remove_and_helper(output);
                right.remove_and_helper(output);
            }
            _ => output.push(self.clone()),
        }
    }

    /// Replaces some constants in this value with other values.
    /// 'replacer' tells us what value a constant should be replaced with, or None to not replace it.
    /// This function doesn't alter any types. Replacer should always return something of
    /// the same type that it received.
    ///
    /// stack_size is how many variables are already on the stack, that we should not use when
    /// constructing replacements.
    pub fn replace_constants(
        &self,
        stack_size: AtomId,
        replacer: &impl Fn(&ConstantInstance) -> Option<AcornValue>,
    ) -> AcornValue {
        match self {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => self.clone(),
            AcornValue::Application(fa) => {
                let new_function = fa.function.replace_constants(stack_size, replacer);
                let new_args = fa
                    .args
                    .iter()
                    .map(|x| x.replace_constants(stack_size, replacer))
                    .collect();
                AcornValue::Application(FunctionApplication {
                    function: Box::new(new_function),
                    args: new_args,
                })
            }
            AcornValue::Lambda(arg_types, value) => {
                let new_value =
                    value.replace_constants(stack_size + arg_types.len() as AtomId, replacer);
                AcornValue::Lambda(arg_types.clone(), Box::new(new_value))
            }
            AcornValue::Binary(op, left, right) => {
                let new_left = left.replace_constants(stack_size, replacer);
                let new_right = right.replace_constants(stack_size, replacer);
                AcornValue::Binary(*op, Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.replace_constants(stack_size, replacer)))
            }
            AcornValue::ForAll(quants, value) => {
                let new_value =
                    value.replace_constants(stack_size + quants.len() as AtomId, replacer);
                AcornValue::ForAll(quants.clone(), Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_value =
                    value.replace_constants(stack_size + quants.len() as AtomId, replacer);
                AcornValue::Exists(quants.clone(), Box::new(new_value))
            }
            AcornValue::Constant(c) => replacer(&c).unwrap_or_else(|| self.clone()),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.replace_constants(stack_size, replacer)),
                Box::new(if_value.replace_constants(stack_size, replacer)),
                Box::new(else_value.replace_constants(stack_size, replacer)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.replace_constants(stack_size, replacer);
                let new_cases = cases
                    .into_iter()
                    .map(|(new_vars, pattern, result)| {
                        let new_stack_size = stack_size + new_vars.len() as AtomId;
                        (
                            new_vars.clone(),
                            pattern.replace_constants(new_stack_size, replacer),
                            result.replace_constants(new_stack_size, replacer),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
        }
    }

    pub fn replace_synthetics(
        &self,
        module_id: ModuleId,
        map: &HashMap<AtomId, String>,
    ) -> AcornValue {
        self.replace_constants(0, &|old_ci| {
            if let Some(new_ci) = old_ci.replace_synthetic(module_id, &map) {
                Some(AcornValue::Constant(new_ci))
            } else {
                None
            }
        })
    }

    /// Returns an error string if this is not a valid top-level value.
    /// The types of variables should match the type of the quantifier they correspond to.
    /// The types of function arguments should match the functions.
    pub fn validate(&self) -> Result<(), String> {
        let mut stack: Vec<AcornType> = vec![];
        self.validate_against_stack(&mut stack)
    }

    fn validate_against_stack(&self, stack: &mut Vec<AcornType>) -> Result<(), String> {
        match self {
            AcornValue::Variable(i, var_type) => match stack.get(*i as usize) {
                Some(t) => {
                    if var_type == t {
                        Ok(())
                    } else {
                        Err(format!(
                            "variable {} has type {:?} but is used as type {:?}",
                            i, t, var_type
                        ))
                    }
                }
                None => Err(format!("variable {} is not in scope", i)),
            },
            AcornValue::Application(app) => {
                app.typecheck()?;
                app.function.validate_against_stack(stack)?;
                for arg in &app.args {
                    arg.validate_against_stack(stack)?;
                }
                Ok(())
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                let original_len = stack.len();
                stack.extend(args.iter().cloned());
                let answer = value.validate_against_stack(stack);
                stack.truncate(original_len);
                answer
            }
            AcornValue::Binary(_, left, right) => {
                left.validate_against_stack(stack)?;
                right.validate_against_stack(stack)
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.validate_against_stack(stack)?;
                if_value.validate_against_stack(stack)?;
                else_value.validate_against_stack(stack)
            }
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.validate_against_stack(stack)?;
                for (new_vars, pattern, result) in cases {
                    let original_len = stack.len();
                    stack.extend(new_vars.iter().cloned());
                    pattern.validate_against_stack(stack)?;
                    result.validate_against_stack(stack)?;
                    stack.truncate(original_len);
                }
                Ok(())
            }
            AcornValue::Not(x) => x.validate_against_stack(stack),
            AcornValue::Constant(ci) => {
                if ci.params.is_empty() && ci.has_generic() {
                    Err(format!("'{}' has generic type but no params", ci))
                } else {
                    Ok(())
                }
            }
            AcornValue::Bool(_) => Ok(()),
        }
    }

    // Replace some type variables with other types.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.instantiate(params))
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.instantiate(params)),
                args: app.args.iter().map(|x| x.instantiate(params)).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.instantiate(params))
                    .collect::<Vec<_>>(),
                Box::new(value.instantiate(params)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.instantiate(params))
                    .collect::<Vec<_>>(),
                Box::new(value.instantiate(params)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.instantiate(params))
                    .collect::<Vec<_>>(),
                Box::new(value.instantiate(params)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.instantiate(params)),
                Box::new(right.instantiate(params)),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.instantiate(params)),
                Box::new(if_value.instantiate(params)),
                Box::new(else_value.instantiate(params)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.instantiate(params);
                let new_cases = cases
                    .iter()
                    .map(|(vars, pattern, result)| {
                        (
                            vars.iter().map(|t| t.instantiate(params)).collect(),
                            pattern.instantiate(params),
                            result.instantiate(params),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.instantiate(params))),
            AcornValue::Constant(c) => AcornValue::Constant(c.instantiate(&params)),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    /// A value has_generic if anything within it has type variables.
    pub fn has_generic(&self) -> bool {
        match self {
            AcornValue::Variable(_, t) => t.has_generic(),
            AcornValue::Application(app) => {
                app.function.has_generic() || app.args.iter().any(|x| x.has_generic())
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                args.iter().any(|x| x.has_generic()) || value.has_generic()
            }
            AcornValue::Binary(_, left, right) => left.has_generic() || right.has_generic(),
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.has_generic() || if_value.has_generic() || else_value.has_generic()
            }
            AcornValue::Not(x) => x.has_generic(),
            AcornValue::Constant(c) => c.has_generic(),
            AcornValue::Bool(_) => false,
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.has_generic()
                    || cases
                        .iter()
                        .any(|(_, pattern, result)| pattern.has_generic() || result.has_generic())
            }
        }
    }

    /// A value is arbitrary if any value within it has an arbitrary type.
    pub fn has_arbitrary(&self) -> bool {
        match self {
            AcornValue::Variable(_, t) => t.has_arbitrary(),
            AcornValue::Application(app) => {
                app.function.has_arbitrary() || app.args.iter().any(|x| x.has_arbitrary())
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.has_arbitrary(),
            AcornValue::Binary(_, left, right) => left.has_arbitrary() || right.has_arbitrary(),
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.has_arbitrary() || if_value.has_arbitrary() || else_value.has_arbitrary()
            }
            AcornValue::Not(x) => x.has_arbitrary(),
            AcornValue::Constant(c) => c.has_arbitrary(),
            AcornValue::Bool(_) => false,
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.has_arbitrary()
                    || cases.iter().any(|(_, pattern, result)| {
                        pattern.has_arbitrary() || result.has_arbitrary()
                    })
            }
        }
    }

    /// Apply a function to each constant in this value.
    pub fn for_each_constant(&self, f: &mut impl FnMut(&ConstantInstance)) {
        match self {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Application(app) => {
                app.function.for_each_constant(f);
                for arg in &app.args {
                    arg.for_each_constant(f);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.for_each_constant(f),
            AcornValue::Binary(_, left, right) => {
                left.for_each_constant(f);
                right.for_each_constant(f);
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.for_each_constant(f);
                if_value.for_each_constant(f);
                else_value.for_each_constant(f);
            }
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.for_each_constant(f);
                for (_, pattern, result) in cases {
                    pattern.for_each_constant(f);
                    result.for_each_constant(f);
                }
            }
            AcornValue::Not(x) => x.for_each_constant(f),
            AcornValue::Constant(c) => f(c),
        }
    }

    /// Apply a function to each type in this value.
    /// This includes types of variables, constants, and the result types of function applications.
    pub fn for_each_type(&self, f: &mut impl FnMut(&AcornType)) {
        match self {
            AcornValue::Variable(_, var_type) => f(var_type),
            AcornValue::Application(app) => {
                // Process the function's types
                app.function.for_each_type(f);
                // Process argument types
                for arg in &app.args {
                    arg.for_each_type(f);
                }
                // Process the application's result type
                let app_type = app.get_type();
                f(&app_type);
            }
            AcornValue::Lambda(arg_types, value) => {
                // Process lambda argument types
                for arg_type in arg_types {
                    f(arg_type);
                }
                value.for_each_type(f);
            }
            AcornValue::ForAll(quant_types, value) | AcornValue::Exists(quant_types, value) => {
                // Process quantifier types
                for quant_type in quant_types {
                    f(quant_type);
                }
                value.for_each_type(f);
            }
            AcornValue::Binary(_, left, right) => {
                left.for_each_type(f);
                right.for_each_type(f);
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.for_each_type(f);
                if_value.for_each_type(f);
                else_value.for_each_type(f);
            }
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.for_each_type(f);
                for (new_vars, pattern, result) in cases {
                    // Process types introduced by the match
                    for var_type in new_vars {
                        f(var_type);
                    }
                    pattern.for_each_type(f);
                    result.for_each_type(f);
                }
            }
            AcornValue::Not(x) => x.for_each_type(f),
            AcornValue::Constant(c) => f(&c.instance_type),
            AcornValue::Bool(_) => {}
        }
    }

    pub fn find_constants(
        &self,
        filter: &impl Fn(&ConstantInstance) -> bool,
        output: &mut Vec<ConstantInstance>,
    ) {
        self.for_each_constant(&mut |c| {
            if filter(c) {
                output.push(c.clone());
            }
        });
    }

    /// Finds all synthetic atom ids in this value.
    /// May contain duplicates.
    pub fn find_synthetics(&self) -> Vec<AtomId> {
        let mut consts = vec![];
        self.find_constants(&|c| c.name.is_synthetic(), &mut consts);
        let mut answer = vec![];
        for c in consts {
            if let ConstantName::Synthetic(id) = c.name {
                answer.push(id);
            }
        }
        answer
    }

    /// Converts all the type variables to arbitrary types.
    pub fn to_arbitrary(&self) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => AcornValue::Variable(*i, var_type.to_arbitrary()),
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.to_arbitrary()),
                args: app.args.iter().map(|x| x.to_arbitrary()).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter().map(|x| x.to_arbitrary()).collect(),
                Box::new(value.to_arbitrary()),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter().map(|x| x.to_arbitrary()).collect(),
                Box::new(value.to_arbitrary()),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter().map(|x| x.to_arbitrary()).collect(),
                Box::new(value.to_arbitrary()),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.to_arbitrary()),
                Box::new(right.to_arbitrary()),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.to_arbitrary()),
                Box::new(if_value.to_arbitrary()),
                Box::new(else_value.to_arbitrary()),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.to_arbitrary();
                let new_cases = cases
                    .iter()
                    .map(|(new_vars, pattern, result)| {
                        (
                            new_vars.clone(),
                            pattern.to_arbitrary(),
                            result.to_arbitrary(),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.to_arbitrary())),
            AcornValue::Constant(c) => AcornValue::Constant(c.to_arbitrary()),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    /// Change the arbitrary types in this list of parameters to generic ones.
    pub fn genericize(&self, params: &[TypeParam]) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.genericize(params))
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.genericize(params)),
                args: app.args.iter().map(|x| x.genericize(params)).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter().map(|x| x.genericize(params)).collect(),
                Box::new(value.genericize(params)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter().map(|x| x.genericize(params)).collect(),
                Box::new(value.genericize(params)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter().map(|x| x.genericize(params)).collect(),
                Box::new(value.genericize(params)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.genericize(params)),
                Box::new(right.genericize(params)),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.genericize(params)),
                Box::new(if_value.genericize(params)),
                Box::new(else_value.genericize(params)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.genericize(params);
                let mut new_cases = vec![];
                for (vars, pattern, result) in cases {
                    let new_vars = vars
                        .iter()
                        .map(|t| t.genericize(params))
                        .collect::<Vec<_>>();
                    let new_pattern = pattern.genericize(params);
                    let new_result = result.genericize(params);
                    new_cases.push((new_vars, new_pattern, new_result));
                }
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.genericize(params))),
            AcornValue::Constant(c) => AcornValue::Constant(c.genericize(params)),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    /// Set parameters to the given constant wherever it occurs in this value.
    pub fn set_params(self, name: &ConstantName, params: &Vec<AcornType>) -> AcornValue {
        match self {
            // The only interesting case.
            AcornValue::Constant(c) if &c.name == name => {
                AcornValue::Constant(c.same_name(params.clone(), c.instance_type.clone()))
            }

            // Otherwise just recurse.
            AcornValue::Constant(..) | AcornValue::Variable(..) | AcornValue::Bool(_) => self,
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.set_params(name, params)),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.set_params(name, params))
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => {
                AcornValue::Lambda(args, Box::new(value.set_params(name, params)))
            }
            AcornValue::ForAll(args, value) => {
                AcornValue::ForAll(args, Box::new(value.set_params(name, params)))
            }
            AcornValue::Exists(args, value) => {
                AcornValue::Exists(args, Box::new(value.set_params(name, params)))
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
                Box::new(left.set_params(name, params)),
                Box::new(right.set_params(name, params)),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.set_params(name, params)),
                Box::new(if_value.set_params(name, params)),
                Box::new(else_value.set_params(name, params)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.set_params(name, params);
                let new_cases = cases
                    .into_iter()
                    .map(|(new_vars, pattern, result)| {
                        (
                            new_vars,
                            pattern.set_params(name, params),
                            result.set_params(name, params),
                        )
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.set_params(name, params))),
        }
    }

    /// Negates a goal proposition and separates it into the types of its assumptions.
    /// (hypothetical, counterfactual)
    /// Hypotheticals are assumed to be true in a "by" block when proving something, in the
    /// sense that you can write more statements that depend on the hypotheticals.
    /// Counterfactuals are used by the prover to find a contradiction, but cannot be used
    /// in the direct reasoning of the code.
    pub fn negate_goal(self) -> (Option<AcornValue>, AcornValue) {
        match self {
            AcornValue::Binary(BinaryOp::Implies, left, right) => (Some(*left), right.negate()),
            _ => (None, self.negate()),
        }
    }

    /// Combine a bunch of values with the given binary operator.
    pub fn reduce(op: BinaryOp, args: Vec<AcornValue>) -> AcornValue {
        if args.is_empty() {
            panic!("cannot reduce with no arguments");
        }

        let mut answer = None;
        for arg in args {
            if let Some(a) = answer {
                answer = Some(AcornValue::Binary(op, Box::new(a), Box::new(arg)));
            } else {
                answer = Some(arg);
            }
        }
        answer.unwrap()
    }

    /// If this value is a dotted attribute of a class or typeclass, return:
    ///   (module id, receiver name, attribute name)
    pub fn as_attribute(&self) -> Option<(ModuleId, &str, &str)> {
        match &self {
            AcornValue::Constant(c) => c.name.as_attribute(),
            _ => None,
        }
    }

    /// If this is a plain constant, give access to its name.
    /// Otherwise, return None.
    pub fn as_name(&self) -> Option<&ConstantName> {
        match &self {
            AcornValue::Constant(c) => Some(&c.name),
            _ => None,
        }
    }

    /// If this is a function call of a constant function, give access to its name.
    pub fn is_named_function_call(&self) -> Option<&ConstantName> {
        match self {
            AcornValue::Application(fa) => fa.function.as_name(),
            _ => None,
        }
    }

    /// If this is a constant with no parameters, give access to its name.
    /// Otherwise, return None.
    pub fn as_simple_constant(&self) -> Option<&ConstantName> {
        match self {
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    Some(&c.name)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Inflating a function definition is when we replace the equality of functions by
    /// a statement that they are equal for all arguments.
    /// If this is a function definition, return the inflated version.
    pub fn inflate_function_definition(&self, definition: AcornValue) -> AcornValue {
        if let AcornValue::Lambda(acorn_types, return_value) = definition {
            let args: Vec<_> = acorn_types
                .iter()
                .enumerate()
                .map(|(i, acorn_type)| AcornValue::Variable(i as AtomId, acorn_type.clone()))
                .collect();
            let app = AcornValue::apply(self.clone(), args);
            AcornValue::ForAll(
                acorn_types,
                Box::new(AcornValue::Binary(
                    BinaryOp::Equals,
                    Box::new(app),
                    return_value,
                )),
            )
        } else {
            AcornValue::equals(self.clone(), definition)
        }
    }

    /// Returns an error if this value is not of the expected type.
    pub fn check_type(
        &self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        if let Some(t) = expected_type {
            self.get_type().check_eq(Some(t), source)
        } else {
            Ok(())
        }
    }

    /// Applies the value as a function to the arguments if the types all check.
    /// If there are no arguments, returns the value itself.
    /// Returns an error on a type mismatch.
    pub fn check_apply(
        self,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        // Typecheck the arguments
        let function_type = self.get_type();
        let function_type = match function_type {
            AcornType::Function(f) => f,
            _ => {
                return Err(source.error("cannot apply a non-function"));
            }
        };
        if function_type.arg_types.len() < args.len() {
            return Err(source.error(&format!(
                "expected <= {} arguments, but got {}",
                function_type.arg_types.len(),
                args.len()
            )));
        }

        // Simple, no-type-inference-necessary construction
        for (i, arg) in args.iter().enumerate() {
            let arg_type: &AcornType = &function_type.arg_types[i];
            arg.check_type(Some(arg_type), source)?;
        }
        let value = AcornValue::apply(self, args);
        value.check_type(expected_type, source)?;
        Ok(value)
    }

    /// A display version for when this value is a subvalue.
    pub fn display_as_subvalue(&self, stack_size: usize) -> String {
        let subvalue = Subvalue {
            value: &self,
            stack_size,
        };
        subvalue.to_string()
    }

    /// Collects all type variables used in this value into the provided HashMap.
    /// The HashMap keys are the variable names.
    /// Returns an error if a type variable name is used with different typeclasses.
    pub fn find_type_vars(
        &self,
        vars: &mut HashMap<String, TypeParam>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<()> {
        match self {
            AcornValue::Variable(_, var_type) => {
                var_type.find_type_vars(vars, source)?;
            }
            AcornValue::Application(app) => {
                app.function.find_type_vars(vars, source)?;
                for arg in &app.args {
                    arg.find_type_vars(vars, source)?;
                }
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                for arg_type in args {
                    arg_type.find_type_vars(vars, source)?;
                }
                value.find_type_vars(vars, source)?;
            }
            AcornValue::Binary(_, left, right) => {
                left.find_type_vars(vars, source)?;
                right.find_type_vars(vars, source)?;
            }
            AcornValue::Not(x) => {
                x.find_type_vars(vars, source)?;
            }
            AcornValue::Constant(c) => {
                for param in &c.params {
                    param.find_type_vars(vars, source)?;
                }
                c.instance_type.find_type_vars(vars, source)?;
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.find_type_vars(vars, source)?;
                if_value.find_type_vars(vars, source)?;
                else_value.find_type_vars(vars, source)?;
            }
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.find_type_vars(vars, source)?;
                for (new_vars, pattern, result) in cases {
                    for var_type in new_vars {
                        var_type.find_type_vars(vars, source)?;
                    }
                    pattern.find_type_vars(vars, source)?;
                    result.find_type_vars(vars, source)?;
                }
            }
            AcornValue::Bool(_) => {
                // Bool values don't contain type variables
            }
        }
        Ok(())
    }
}
