use std::collections::HashMap;
use std::fmt;

use crate::elaborator::acorn_type::{AcornType, Datatype, TypeParam, Typeclass};
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::names::{ConstantName, DefinedName, InstanceName};
use crate::kernel::atom::AtomId;
use crate::module::ModuleId;
use crate::syntax::token::TokenType;

/// Represents a function application with a function and its arguments.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct FunctionApplication {
    /// The function being applied
    pub function: Box<AcornValue>,
    /// The arguments to the function
    pub args: Vec<AcornValue>,
}

impl FunctionApplication {
    /// Gets the type of this function application result
    pub fn get_type(&self) -> AcornType {
        let (base, all_args) = self.flattened_head_and_args();
        let (function_type, checked_args_start, binding_offset) =
            Self::resolved_function_type_for_flattened_application(base, &all_args);
        let mut current_type = function_type;
        for arg in &all_args[checked_args_start..] {
            let AcornType::Function(ftype) = current_type else {
                panic!("FunctionApplication's function is not a function type");
            };
            current_type = ftype.applied_type(1).bind_values(
                binding_offset,
                binding_offset,
                std::slice::from_ref(arg),
            );
        }
        current_type
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
        let (base, all_args) = self.flattened_head_and_args();
        if let AcornValue::Constant(constant) = base {
            let num_specialization_args =
                constant.pending_value_specialization_arg_count(all_args.len());
            for (i, (arg, arg_type)) in all_args[..num_specialization_args]
                .iter()
                .zip(constant.value_param_types.iter())
                .enumerate()
            {
                if !arg.is_type(arg_type) {
                    return Err(format!(
                        "Argument {} has type {}, but expected {}",
                        i,
                        arg.get_type(),
                        arg_type
                    ));
                }
            }
        }
        let (function_type, checked_args_start, binding_offset) =
            Self::resolved_function_type_for_flattened_application(base, &all_args);
        let remaining_args = &all_args[checked_args_start..];
        let mut current_type = function_type;
        for (i, arg) in remaining_args.iter().enumerate() {
            let AcornType::Function(ftype) = current_type else {
                return Err(format!(
                    "Function application has function of type {}",
                    current_type
                ));
            };
            let Some(arg_type) = ftype.arg_types.first() else {
                return Err("expected 0 arguments".to_string());
            };
            if !arg.is_type(arg_type) {
                return Err(format!(
                    "Argument {} has type {}, but expected {}",
                    checked_args_start + i,
                    arg.get_type(),
                    arg_type
                ));
            }
            current_type = ftype.applied_type(1).bind_values(
                binding_offset,
                binding_offset,
                std::slice::from_ref(arg),
            );
        }
        Ok(())
    }

    fn flattened_head_and_args(&self) -> (&AcornValue, Vec<AcornValue>) {
        fn collect<'a>(
            function: &'a AcornValue,
            args: &[AcornValue],
            output: &mut Vec<AcornValue>,
        ) -> &'a AcornValue {
            match function {
                AcornValue::Application(app) => {
                    let head = collect(&app.function, &app.args, output);
                    output.extend(args.iter().cloned());
                    head
                }
                _ => {
                    output.extend(args.iter().cloned());
                    function
                }
            }
        }

        let mut args = Vec::new();
        let base = collect(&self.function, &self.args, &mut args);
        (base, args)
    }

    fn resolved_function_type_for_flattened_application(
        base: &AcornValue,
        all_args: &[AcornValue],
    ) -> (AcornType, usize, AtomId) {
        match base {
            AcornValue::Constant(constant) if !constant.bound_value_args.is_empty() => (
                constant.instance_type.clone(),
                0,
                constant.bound_value_args.len() as AtomId,
            ),
            AcornValue::Constant(constant) if !constant.value_param_types.is_empty() => {
                let num_specialization_args =
                    constant.pending_value_specialization_arg_count(all_args.len());
                let visible_prefix_count = constant
                    .visible_value_param_prefix_count()
                    .min(num_specialization_args);
                let mut function_type = constant
                    .instance_type
                    .bind_value_params(&all_args[..num_specialization_args]);
                let binding_offset = constant.bound_value_args.len() as AtomId;
                if visible_prefix_count > 0 {
                    for arg in &all_args[..visible_prefix_count] {
                        function_type = match function_type {
                            AcornType::Function(function_type) => function_type
                                .applied_type(1)
                                .bind_values(
                                    binding_offset,
                                    binding_offset,
                                    std::slice::from_ref(arg),
                                ),
                            _ => panic!(
                                "Function application has invalid visible dependent value parameters"
                            ),
                        };
                    }
                }
                (function_type, num_specialization_args, binding_offset)
            }
            _ => (base.get_type(), 0, 0),
        }
    }
}

/// Represents explicit type application syntax on a value.
/// This preserves source-level type arguments for roundtripping.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct TypeApplication {
    /// The value being type-applied.
    pub function: Box<AcornValue>,

    /// Ordered type parameter names from source syntax.
    pub type_param_names: Vec<String>,

    /// Optional typeclass constraints for each type parameter.
    pub type_param_constraints: Vec<Option<Typeclass>>,

    /// The concrete type arguments.
    pub type_args: Vec<AcornType>,
}

impl TypeApplication {
    fn substitutions(&self) -> Vec<(String, AcornType)> {
        self.type_param_names
            .iter()
            .cloned()
            .zip(self.type_args.iter().cloned())
            .collect()
    }

    pub fn instantiated_function(&self) -> AcornValue {
        self.function.instantiate(&self.substitutions())
    }

    pub fn get_type(&self) -> AcornType {
        self.function.get_type().instantiate(&self.substitutions())
    }
}

/// Represents binary operators used in Acorn
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
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
///
/// Identity is determined by `name`, `params`, and any hidden family-value specialization.
/// The remaining fields (`instance_type`, `generic_type`, `type_param_names`,
/// `value_param_types`) are derived from those and are not included in Hash/Eq/Ord comparisons.
#[derive(Clone, Debug)]
pub struct ConstantInstance {
    /// The name of this constant
    pub name: ConstantName,

    /// The type parameters that this constant was instantiated with, if any.
    /// Ordered the same way as in the definition.
    pub params: Vec<AcornType>,

    /// The type of the instance, after instantiation.
    pub instance_type: AcornType,

    /// The original type of this constant before instantiation.
    /// Uses Variable types (not Arbitrary) to represent type parameters.
    /// For non-generic constants, this equals instance_type.
    pub generic_type: AcornType,

    /// The ordered names of type parameters for this constant.
    /// Used to map Variable names to bound variable indices for polymorphic type conversion.
    /// Empty for non-generic constants.
    pub type_param_names: Vec<String>,

    /// Ordered dependent value parameters for this constant, if any.
    /// These behave like hidden leading binders in the constant's type.
    pub value_param_types: Vec<AcornType>,

    /// Bound values for hidden family parameters, if this is a specialized family constant.
    /// These stay implicit at the source level, but kernel lowering must apply them explicitly.
    pub bound_value_args: Vec<AcornValue>,
}

// Identity is based only on name, params, and hidden family-value specialization.
impl PartialEq for ConstantInstance {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.params == other.params
            && self.bound_value_args == other.bound_value_args
    }
}

impl Eq for ConstantInstance {}

impl std::hash::Hash for ConstantInstance {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.params.hash(state);
        self.bound_value_args.hash(state);
    }
}

impl PartialOrd for ConstantInstance {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ConstantInstance {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.name.cmp(&other.name) {
            std::cmp::Ordering::Equal => match self.params.cmp(&other.params) {
                std::cmp::Ordering::Equal => self.bound_value_args.cmp(&other.bound_value_args),
                ord => ord,
            },
            ord => ord,
        }
    }
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
    fn visible_value_param_prefix_count(&self) -> usize {
        if !matches!(self.name, ConstantName::Unqualified(..)) {
            return 0;
        }
        let AcornType::Function(function_type) = &self.instance_type else {
            return 0;
        };
        if function_type.arg_types.len() < self.value_param_types.len() {
            return 0;
        }
        if function_type.arg_types[..self.value_param_types.len()] != *self.value_param_types {
            return 0;
        }
        self.value_param_types.len()
    }

    fn pending_value_specialization_arg_count(&self, supplied_arg_count: usize) -> usize {
        if self.bound_value_args.is_empty() {
            self.value_param_types.len().min(supplied_arg_count)
        } else {
            0
        }
    }

    /// Make another constant with the same name as this one.
    /// Preserves generic_type, type_param_names, value_param_types, and bound_value_args from self.
    fn same_name(&self, params: Vec<AcornType>, instance_type: AcornType) -> ConstantInstance {
        ConstantInstance {
            name: self.name.clone(),
            params,
            instance_type,
            generic_type: self.generic_type.clone(),
            type_param_names: self.type_param_names.clone(),
            value_param_types: self.value_param_types.clone(),
            bound_value_args: self.bound_value_args.clone(),
        }
    }

    pub fn instantiate(&self, params: &[(String, AcornType)]) -> ConstantInstance {
        let mut answer = self.same_name(
            self.params.iter().map(|t| t.instantiate(params)).collect(),
            self.instance_type.instantiate(params),
        );
        answer.value_param_types = self
            .value_param_types
            .iter()
            .map(|t| t.instantiate(params))
            .collect();
        answer.bound_value_args = self
            .bound_value_args
            .iter()
            .map(|value| value.instantiate(params))
            .collect();
        answer
    }

    pub fn bind_value_params(
        &self,
        values: &[AcornValue],
        source: &dyn ErrorContext,
    ) -> error::Result<ConstantInstance> {
        if values.len() != self.value_param_types.len() {
            return Err(source.error(&format!(
                "constant {} expects {} family value arguments, but got {}",
                self.name,
                self.value_param_types.len(),
                values.len()
            )));
        }

        Ok(ConstantInstance {
            name: self.name.clone(),
            params: self.params.clone(),
            instance_type: self.instance_type.bind_value_params(values),
            generic_type: self.generic_type.clone(),
            type_param_names: self.type_param_names.clone(),
            value_param_types: self.value_param_types.clone(),
            bound_value_args: values.to_vec(),
        })
    }

    pub fn has_generic(&self) -> bool {
        self.params.iter().any(|t| t.has_generic())
            || self.instance_type.has_generic()
            || self.value_param_types.iter().any(|t| t.has_generic())
            || self
                .bound_value_args
                .iter()
                .any(|value| value.has_generic())
    }

    /// Change the arbitrary types in this list of parameters to generic ones.
    pub fn genericize(&self, params: &[TypeParam]) -> ConstantInstance {
        let old_instance_type = &self.instance_type;
        let instance_type = old_instance_type.genericize(params);
        let new_params = if instance_type.has_generic() && self.params.is_empty() {
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
        } else if !self.params.is_empty() && old_instance_type.has_arbitrary() {
            // This is a successive genericization. Check if the instance_type before genericization
            // had arbitrary types that match the params we're genericizing with.
            // If so, we need to append the new params.
            let mut result_params: Vec<AcornType> =
                self.params.iter().map(|t| t.genericize(params)).collect();

            // Check which params from the current genericization apply to this constant
            // and aren't already in the result
            for param in params {
                if old_instance_type.has_arbitrary_type_param(param) {
                    let param_as_type = AcornType::Variable(param.clone());

                    // Check if this type param is already used anywhere in result_params
                    // We need to check recursively because it might be nested inside a Data type
                    let param_already_used = result_params
                        .iter()
                        .any(|existing_type| existing_type.contains_type_var(param));

                    if !param_already_used {
                        result_params.push(param_as_type);
                    }
                }
            }
            result_params
        } else {
            // Just genericize what we started with, same as usual
            self.params.iter().map(|t| t.genericize(params)).collect()
        };
        let mut answer = self.same_name(new_params, instance_type);
        answer.value_param_types = self
            .value_param_types
            .iter()
            .map(|t| t.genericize(params))
            .collect();
        answer.bound_value_args = self
            .bound_value_args
            .iter()
            .map(|value| value.genericize(params))
            .collect();
        answer
    }

    pub fn has_arbitrary(&self) -> bool {
        self.params.iter().any(|t| t.has_arbitrary())
            || self.value_param_types.iter().any(|t| t.has_arbitrary())
            || self
                .bound_value_args
                .iter()
                .any(|value| value.has_arbitrary())
    }

    pub fn to_arbitrary(&self) -> ConstantInstance {
        let mut answer = self.same_name(
            self.params.iter().map(|t| t.to_arbitrary()).collect(),
            self.instance_type.to_arbitrary(),
        );
        answer.value_param_types = self
            .value_param_types
            .iter()
            .map(|t| t.to_arbitrary())
            .collect();
        answer.bound_value_args = self
            .bound_value_args
            .iter()
            .map(|value| value.to_arbitrary())
            .collect();
        answer
    }

    /// If this value is a typeclass attribute with the specific typeclass and class, convert
    /// it to the name used in its definition.
    pub fn to_defined_instance_name(
        &self,
        typeclass: &Typeclass,
        datatype: &Datatype,
    ) -> Option<DefinedName> {
        if let ConstantName::InstanceAttribute(_, instance_name) = &self.name {
            if &instance_name.typeclass == typeclass && &instance_name.datatype == datatype {
                return Some(DefinedName::Instance(instance_name.clone()));
            }
        }
        if let Some((receiver_module_id, receiver, attribute)) = self.name.as_attribute() {
            if receiver_module_id == typeclass.module_id
                && receiver == typeclass.name
                && self.params.len() == 1
            {
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
}

/// Two AcornValue compare to equal if they are structurally identical.
/// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct MatchCase {
    /// Types introduced by this match branch (new pattern-bound variables).
    pub new_vars: Vec<AcornType>,
    /// The branch pattern value.
    /// Invariant: this must agree with `constructor_index` / `constructor_total`.
    /// Term lowering uses the constructor metadata as the authoritative branch identity.
    pub pattern: AcornValue,
    /// The branch result value.
    pub result: AcornValue,
    /// Constructor index within the matched datatype (constructor order).
    pub constructor_index: u16,
    /// Total constructor count for the matched datatype.
    pub constructor_total: u16,
}

/// Two AcornValue compare to equal if they are structurally identical.
/// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum AcornValue {
    /// A variable that is bound to a value on the stack.
    /// Represented by (stack level, type).
    ///
    /// This uses "de Bruijn levels" (not indices). Variable(0) refers to the
    /// FIRST/OUTERMOST binder, not the innermost. See stack.rs for details.
    Variable(AtomId, AcornType),

    Constant(ConstantInstance),

    Application(FunctionApplication),

    /// Explicit type application syntax, e.g. `f[T]`.
    TypeApplication(TypeApplication),

    /// A function definition that introduces variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    /// The boolean binary operators are treated specially during inference
    Binary(BinaryOp, Box<AcornValue>, Box<AcornValue>),

    Not(Box<AcornValue>),

    /// The try operator (postfix ?)
    /// Stores the inner value and the unwrapped type T
    /// If foo has type MyType and MyType.some: T -> MyType, then foo? has type T
    Try(Box<AcornValue>, AcornType),

    /// Quantifiers that introduce variables onto the stack.
    ForAll(Vec<AcornType>, Box<AcornValue>),
    Exists(Vec<AcornType>, Box<AcornValue>),

    /// A parenthesized value that must remain distinguishable in exact clause codecs.
    /// This is semantically transparent outside those codecs.
    Grouping(Box<AcornValue>),

    /// A plain old bool. True or false
    Bool(bool),

    /// If-then-else requires all parts: condition, if-value, else-value.
    IfThenElse(Box<AcornValue>, Box<AcornValue>, Box<AcornValue>),

    /// The first value is the one being matched (the scrutinee).
    /// The scrutinee needs to be evaluated in the outside context.
    /// Each case includes pattern/result plus constructor metadata for deterministic lowering.
    Match(Box<AcornValue>, Vec<MatchCase>),
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
            AcornValue::Variable(i, acorn_type) => {
                let prefix = if matches!(
                    acorn_type,
                    AcornType::Type0 | AcornType::TypeclassConstraint(_)
                ) {
                    "T"
                } else {
                    "x"
                };
                write!(f, "{}{}", prefix, i)
            }
            AcornValue::Application(a) => a.fmt_helper(f, self.stack_size),
            AcornValue::TypeApplication(ta) => {
                if let AcornValue::Lambda(args, body) = ta.function.as_ref() {
                    if !ta.type_param_names.is_empty()
                        && ta.type_param_names.len() == ta.type_param_constraints.len()
                    {
                        let mut type_param_codes = Vec::new();
                        for (name, constraint) in ta
                            .type_param_names
                            .iter()
                            .zip(ta.type_param_constraints.iter())
                        {
                            if let Some(typeclass) = constraint {
                                type_param_codes.push(format!("{}: {}", name, typeclass.name));
                            } else {
                                type_param_codes.push(name.clone());
                            }
                        }
                        write!(
                            f,
                            "function[{}]({}) {{ {} }}",
                            type_param_codes.join(", "),
                            AcornType::decs_to_str(args, self.stack_size),
                            Subvalue::new(body, self.stack_size + args.len())
                        )?;
                    } else {
                        write!(f, "{}", Subvalue::new(&ta.function, self.stack_size))?;
                    }
                } else {
                    write!(f, "{}", Subvalue::new(&ta.function, self.stack_size))?;
                }
                let args: Vec<_> = ta.type_args.iter().map(|t| t.to_string()).collect();
                write!(f, "[{}]", args.join(", "))
            }
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
            AcornValue::Try(a, _) => {
                write!(f, "{}?", Subvalue::new(a, self.stack_size))
            }
            AcornValue::ForAll(args, body) => fmt_binder(f, "forall", args, body, self.stack_size),
            AcornValue::Exists(args, body) => fmt_binder(f, "exists", args, body, self.stack_size),
            AcornValue::Grouping(value) => {
                write!(f, "({})", Subvalue::new(value, self.stack_size))
            }
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
                for case in cases {
                    let new_stack_size = self.stack_size + case.new_vars.len();
                    write!(
                        f,
                        " {} {{ {} }}",
                        Subvalue::new(&case.pattern, new_stack_size),
                        Subvalue::new(&case.result, new_stack_size)
                    )?;
                }
                write!(f, " }}")
            }
        }
    }
}

impl Subvalue<'_> {
    fn new(value: &AcornValue, stack_size: usize) -> Subvalue<'_> {
        Subvalue { value, stack_size }
    }

    fn root(value: &AcornValue) -> Subvalue<'_> {
        Subvalue::new(value, 0)
    }
}

fn fmt_values(v: &[AcornValue], f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
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
    decs: &[AcornType],
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
    pub fn grouped(value: AcornValue) -> AcornValue {
        match value {
            AcornValue::Grouping(_) => value,
            _ => AcornValue::Grouping(Box::new(value)),
        }
    }

    pub fn strip_grouping(&self) -> &AcornValue {
        match self {
            AcornValue::Grouping(value) => value.strip_grouping(),
            _ => self,
        }
    }

    pub fn get_type(&self) -> AcornType {
        match self {
            AcornValue::Variable(_, t) => t.clone(),
            AcornValue::Application(t) => t.get_type(),
            AcornValue::TypeApplication(t) => t.get_type(),
            AcornValue::Lambda(args, return_value) => {
                AcornType::functional(args.clone(), return_value.get_type())
            }
            AcornValue::Binary(_, _, _) => AcornType::Bool,
            AcornValue::Not(_) => AcornType::Bool,
            AcornValue::Try(_, unwrapped_type) => unwrapped_type.clone(),
            AcornValue::ForAll(_, _) => AcornType::Bool,
            AcornValue::Exists(_, _) => AcornType::Bool,
            AcornValue::Grouping(value) => value.get_type(),
            AcornValue::Constant(c) => c.instance_type.clone(),
            AcornValue::Bool(_) => AcornType::Bool,
            AcornValue::IfThenElse(_, if_value, _) => if_value.get_type(),
            AcornValue::Match(_, cases) => {
                if let Some(case) = cases.first() {
                    case.result.get_type()
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
            AcornValue::TypeApplication(app) => app.get_type() == *t,
            AcornValue::Lambda(args, return_value) => {
                if let AcornType::Function(ftype) = t {
                    args == &ftype.arg_types && return_value.is_type(&ftype.return_type)
                } else {
                    false
                }
            }
            AcornValue::Binary(_, _, _) => *t == AcornType::Bool,
            AcornValue::Not(_) => *t == AcornType::Bool,
            AcornValue::Try(_, unwrapped_type) => unwrapped_type == t,
            AcornValue::ForAll(_, _) => *t == AcornType::Bool,
            AcornValue::Exists(_, _) => *t == AcornType::Bool,
            AcornValue::Grouping(value) => value.is_type(t),
            AcornValue::Constant(c) => c.instance_type == *t,
            AcornValue::Bool(_) => *t == AcornType::Bool,
            AcornValue::IfThenElse(_, if_value, _) => if_value.is_type(t),
            AcornValue::Match(_, cases) => {
                if let Some(case) = cases.first() {
                    case.result.is_type(t)
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

    pub fn type_apply(
        function: AcornValue,
        type_param_names: Vec<String>,
        type_param_constraints: Vec<Option<Typeclass>>,
        type_args: Vec<AcornType>,
    ) -> AcornValue {
        if type_args.is_empty() {
            function
        } else {
            AcornValue::TypeApplication(TypeApplication {
                function: Box::new(function),
                type_param_names,
                type_param_constraints,
                type_args,
            })
        }
    }

    /// Recursively extract the base function from applications.
    /// For example, if we have f(a)(b)(c), this returns f.
    /// This is useful for getting the original function from partial applications.
    pub fn unapply(&self) -> &AcornValue {
        match self {
            AcornValue::Application(app) => app.function.unapply(),
            AcornValue::TypeApplication(app) => app.function.unapply(),
            AcornValue::Grouping(value) => value.unapply(),
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

    /// Make the internal constant used for a concrete instance implementation.
    ///
    /// This is intentionally monomorphic and is only meant to exist while elaborating or
    /// normalizing an `instance` block. Outside that context, the public-facing spelling
    /// remains the typeclass attribute form such as `Add.add[Nat]`.
    pub fn instance_impl_constant(
        defining_module: ModuleId,
        instance_name: InstanceName,
        instance_type: AcornType,
    ) -> AcornValue {
        AcornValue::constant(
            ConstantName::instance_attr(defining_module, instance_name),
            vec![],
            instance_type.clone(),
            instance_type,
            vec![],
            vec![],
        )
    }

    /// Creates a constant value.
    /// For non-generic constants (params is empty), generic_type should equal instance_type
    /// and type_param_names should be empty.
    pub fn constant(
        name: ConstantName,
        params: Vec<AcornType>,
        instance_type: AcornType,
        generic_type: AcornType,
        type_param_names: Vec<String>,
        value_param_types: Vec<AcornType>,
    ) -> AcornValue {
        let ci = ConstantInstance {
            name,
            params,
            instance_type,
            generic_type,
            type_param_names,
            value_param_types,
            bound_value_args: vec![],
        };
        AcornValue::Constant(ci)
    }

    pub fn bind_value_params(
        self,
        values: &[AcornValue],
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        match self {
            AcornValue::Constant(constant) => Ok(AcornValue::Constant(
                constant.bind_value_params(values, source)?,
            )),
            other => {
                if values.is_empty() {
                    Ok(other)
                } else {
                    Err(source
                        .error("only constants can be specialized with family value arguments"))
                }
            }
        }
    }

    /// Checks if this value is a lambda function
    pub fn is_lambda(&self) -> bool {
        match self {
            AcornValue::Lambda(_, _) => true,
            AcornValue::TypeApplication(app) => app.function.is_lambda(),
            AcornValue::Grouping(value) => value.is_lambda(),
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
            AcornValue::TypeApplication(app) => app.function.is_term(),
            AcornValue::Lambda(_, _) => false,
            AcornValue::Binary(_, _, _) => false,
            AcornValue::Not(_) => false,
            AcornValue::Try(inner, _) => inner.is_term(),
            AcornValue::ForAll(_, _) => false,
            AcornValue::Exists(_, _) => false,
            AcornValue::Grouping(value) => value.is_term(),
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
            AcornValue::Grouping(x) => AcornValue::Grouping(Box::new(x.negate())),
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
            AcornValue::Grouping(x) => AcornValue::Grouping(Box::new(x.pretty_negate())),
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

    fn bind_binder_types(
        binder_types: &[AcornType],
        first_binding_index: AtomId,
        stack_size: AtomId,
        values: &[AcornValue],
    ) -> Vec<AcornType> {
        let mut current_stack_size = stack_size;
        binder_types
            .iter()
            .map(|binder_type| {
                let bound =
                    binder_type.bind_values(first_binding_index, current_stack_size, values);
                current_stack_size += 1;
                bound
            })
            .collect()
    }

    fn replace_constants_in_binder_types(
        binder_types: &[AcornType],
        stack_size: AtomId,
        replacer: &impl Fn(&ConstantInstance) -> Option<AcornValue>,
    ) -> Vec<AcornType> {
        let mut current_stack_size = stack_size;
        binder_types
            .iter()
            .map(|binder_type| {
                let replaced = binder_type.replace_constants(current_stack_size, replacer);
                current_stack_size += 1;
                replaced
            })
            .collect()
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
                let bound_type = var_type.bind_values(first_binding_index, stack_size, values);
                if i < first_binding_index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, bound_type);
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
                AcornValue::Variable(i - values.len() as AtomId, bound_type)
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
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.bind_values(
                    first_binding_index,
                    stack_size,
                    values,
                )),
                type_param_names: app.type_param_names,
                type_param_constraints: app.type_param_constraints,
                type_args: app
                    .type_args
                    .iter()
                    .map(|t| t.bind_values(first_binding_index, stack_size, values))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => {
                let new_args =
                    Self::bind_binder_types(&args, first_binding_index, stack_size, values);
                let return_value_stack_size = stack_size + args.len() as AtomId;
                AcornValue::Lambda(
                    new_args,
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
            AcornValue::Try(x, t) => AcornValue::Try(
                Box::new(x.bind_values(first_binding_index, stack_size, values)),
                t.bind_values(first_binding_index, stack_size, values),
            ),
            AcornValue::ForAll(quants, value) => {
                let new_quants =
                    Self::bind_binder_types(&quants, first_binding_index, stack_size, values);
                let value_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::ForAll(
                    new_quants,
                    Box::new(value.bind_values(first_binding_index, value_stack_size, values)),
                )
            }
            AcornValue::Exists(quants, value) => {
                let new_quants =
                    Self::bind_binder_types(&quants, first_binding_index, stack_size, values);
                let value_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(
                    new_quants,
                    Box::new(value.bind_values(first_binding_index, value_stack_size, values)),
                )
            }
            AcornValue::Grouping(value) => AcornValue::Grouping(Box::new(value.bind_values(
                first_binding_index,
                stack_size,
                values,
            ))),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.bind_values(first_binding_index, stack_size, values)),
                Box::new(if_value.bind_values(first_binding_index, stack_size, values)),
                Box::new(else_value.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.bind_values(first_binding_index, stack_size, values);
                let new_cases = cases
                    .into_iter()
                    .map(|case| {
                        let new_vars = Self::bind_binder_types(
                            &case.new_vars,
                            first_binding_index,
                            stack_size,
                            values,
                        );
                        let new_stack_size = stack_size + case.new_vars.len() as AtomId;
                        MatchCase {
                            new_vars,
                            pattern: case.pattern.bind_values(
                                first_binding_index,
                                new_stack_size,
                                values,
                            ),
                            result: case.result.bind_values(
                                first_binding_index,
                                new_stack_size,
                                values,
                            ),
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        }
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Constant(c) => AcornValue::Constant(ConstantInstance {
                name: c.name,
                params: c
                    .params
                    .iter()
                    .map(|t| t.bind_values(first_binding_index, stack_size, values))
                    .collect(),
                instance_type: c
                    .instance_type
                    .bind_values(first_binding_index, stack_size, values),
                generic_type: c
                    .generic_type
                    .bind_values(first_binding_index, stack_size, values),
                type_param_names: c.type_param_names,
                value_param_types: c
                    .value_param_types
                    .iter()
                    .map(|t| t.bind_values(first_binding_index, stack_size, values))
                    .collect(),
                bound_value_args: c
                    .bound_value_args
                    .into_iter()
                    .map(|value| value.bind_values(first_binding_index, stack_size, values))
                    .collect(),
            }),
            AcornValue::Bool(_) => self,
        }
    }

    /// Inserts 'increment' stack entries, starting with the provided index, that this value
    /// doesn't use.
    /// This moves the value from a context that has 'index' stack entries, to one that
    /// has 'index + increment' entries.
    /// Every reference at index or higher should be incremented by increment.
    ///
    /// Because this codebase uses de Bruijn levels (not indices), when you wrap a value
    /// in a new binder, you need to shift ALL existing variable references up. For example,
    /// if you have `Exists([Bool], Variable(0, Bool))` and wrap it in `ForAll([Foo], ...)`,
    /// the inner Variable(0) must become Variable(1) so it still refers to the Bool from
    /// the Exists, not the new Foo from the ForAll.
    pub fn insert_stack(self, index: AtomId, increment: AtomId) -> AcornValue {
        if increment == 0 {
            return self;
        }
        match self {
            AcornValue::Variable(i, var_type) => {
                if i < index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, var_type.insert_stack(index, increment));
                }
                // This reference just needs to be shifted
                AcornValue::Variable(i + increment, var_type.insert_stack(index, increment))
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.insert_stack(index, increment)),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.insert_stack(index, increment))
                    .collect(),
            }),
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.insert_stack(index, increment)),
                type_param_names: app.type_param_names,
                type_param_constraints: app.type_param_constraints,
                type_args: app
                    .type_args
                    .iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => AcornValue::Lambda(
                args.into_iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
                Box::new(return_value.insert_stack(index, increment)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.insert_stack(index, increment))),
            AcornValue::Try(x, t) => AcornValue::Try(
                Box::new(x.insert_stack(index, increment)),
                t.insert_stack(index, increment),
            ),
            AcornValue::ForAll(quants, value) => AcornValue::ForAll(
                quants
                    .into_iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
                Box::new(value.insert_stack(index, increment)),
            ),
            AcornValue::Exists(quants, value) => AcornValue::Exists(
                quants
                    .into_iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
                Box::new(value.insert_stack(index, increment)),
            ),
            AcornValue::Grouping(value) => {
                AcornValue::Grouping(Box::new(value.insert_stack(index, increment)))
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
                    .map(|case| MatchCase {
                        new_vars: case
                            .new_vars
                            .into_iter()
                            .map(|t| t.insert_stack(index, increment))
                            .collect(),
                        pattern: case.pattern.insert_stack(index, increment),
                        result: case.result.insert_stack(index, increment),
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Constant(c) => AcornValue::Constant(ConstantInstance {
                name: c.name,
                params: c
                    .params
                    .into_iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
                instance_type: c.instance_type.insert_stack(index, increment),
                generic_type: c.generic_type.insert_stack(index, increment),
                type_param_names: c.type_param_names,
                value_param_types: c
                    .value_param_types
                    .into_iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
                bound_value_args: c
                    .bound_value_args
                    .into_iter()
                    .map(|value| value.insert_stack(index, increment))
                    .collect(),
            }),
            AcornValue::Bool(_) => self,
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
                // Expand lambdas in the arguments first
                let expanded_args: Vec<AcornValue> = app
                    .args
                    .iter()
                    .map(|x| x.expand_lambdas(stack_size))
                    .collect();
                if let AcornValue::Lambda(_lambda_args, return_value) = function {
                    // Expand the lambda
                    let expanded = return_value.bind_values(stack_size, stack_size, &expanded_args);
                    expanded.expand_lambdas(stack_size)
                } else {
                    AcornValue::Application(FunctionApplication {
                        function: Box::new(function),
                        args: expanded_args,
                    })
                }
            }
            AcornValue::TypeApplication(app) => {
                app.instantiated_function().expand_lambdas(stack_size)
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.expand_lambdas(stack_size))),
            AcornValue::Try(x, t) => {
                AcornValue::Try(Box::new(x.expand_lambdas(stack_size)), t.clone())
            }
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
            AcornValue::Grouping(value) => {
                AcornValue::Grouping(Box::new(value.expand_lambdas(stack_size)))
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
                    .map(|case| {
                        let new_stack_size = stack_size + case.new_vars.len() as AtomId;
                        MatchCase {
                            new_vars: case.new_vars.clone(),
                            pattern: case.pattern.expand_lambdas(new_stack_size),
                            result: case.result.expand_lambdas(new_stack_size),
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        }
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
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.replace_constants(stack_size, replacer))
            }
            AcornValue::Bool(_) => self.clone(),
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
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.replace_constants(stack_size, replacer)),
                type_param_names: app.type_param_names.clone(),
                type_param_constraints: app.type_param_constraints.clone(),
                type_args: app
                    .type_args
                    .iter()
                    .map(|t| t.replace_constants(stack_size, replacer))
                    .collect(),
            }),
            AcornValue::Lambda(arg_types, value) => {
                let new_arg_types =
                    Self::replace_constants_in_binder_types(arg_types, stack_size, replacer);
                let new_value =
                    value.replace_constants(stack_size + arg_types.len() as AtomId, replacer);
                AcornValue::Lambda(new_arg_types, Box::new(new_value))
            }
            AcornValue::Binary(op, left, right) => {
                let new_left = left.replace_constants(stack_size, replacer);
                let new_right = right.replace_constants(stack_size, replacer);
                AcornValue::Binary(*op, Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.replace_constants(stack_size, replacer)))
            }
            AcornValue::Try(x, t) => AcornValue::Try(
                Box::new(x.replace_constants(stack_size, replacer)),
                t.replace_constants(stack_size, replacer),
            ),
            AcornValue::ForAll(quants, value) => {
                let new_quants =
                    Self::replace_constants_in_binder_types(quants, stack_size, replacer);
                let new_value =
                    value.replace_constants(stack_size + quants.len() as AtomId, replacer);
                AcornValue::ForAll(new_quants, Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_quants =
                    Self::replace_constants_in_binder_types(quants, stack_size, replacer);
                let new_value =
                    value.replace_constants(stack_size + quants.len() as AtomId, replacer);
                AcornValue::Exists(new_quants, Box::new(new_value))
            }
            AcornValue::Grouping(value) => {
                AcornValue::Grouping(Box::new(value.replace_constants(stack_size, replacer)))
            }
            AcornValue::Constant(c) => replacer(c).unwrap_or_else(|| {
                AcornValue::Constant(ConstantInstance {
                    name: c.name.clone(),
                    params: c
                        .params
                        .iter()
                        .map(|t| t.replace_constants(stack_size, replacer))
                        .collect(),
                    instance_type: c.instance_type.replace_constants(stack_size, replacer),
                    generic_type: c.generic_type.replace_constants(stack_size, replacer),
                    type_param_names: c.type_param_names.clone(),
                    value_param_types: c
                        .value_param_types
                        .iter()
                        .map(|t| t.replace_constants(stack_size, replacer))
                        .collect(),
                    bound_value_args: c
                        .bound_value_args
                        .iter()
                        .map(|value| value.replace_constants(stack_size, replacer))
                        .collect(),
                })
            }),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.replace_constants(stack_size, replacer)),
                Box::new(if_value.replace_constants(stack_size, replacer)),
                Box::new(else_value.replace_constants(stack_size, replacer)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.replace_constants(stack_size, replacer);
                let new_cases = cases
                    .iter()
                    .map(|case| {
                        let new_stack_size = stack_size + case.new_vars.len() as AtomId;
                        let new_vars = Self::replace_constants_in_binder_types(
                            &case.new_vars,
                            stack_size,
                            replacer,
                        );
                        MatchCase {
                            new_vars,
                            pattern: case.pattern.replace_constants(new_stack_size, replacer),
                            result: case.result.replace_constants(new_stack_size, replacer),
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        }
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
        }
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
            AcornValue::TypeApplication(app) => {
                if app.type_param_names.len() != app.type_args.len()
                    || app.type_param_constraints.len() != app.type_args.len()
                {
                    return Err("type application has mismatched parameter metadata".to_string());
                }
                app.function.validate_against_stack(stack)
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
            AcornValue::Grouping(value) => value.validate_against_stack(stack),
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
                for case in cases {
                    let original_len = stack.len();
                    stack.extend(case.new_vars.iter().cloned());
                    case.pattern.validate_against_stack(stack)?;
                    case.result.validate_against_stack(stack)?;
                    stack.truncate(original_len);
                }
                Ok(())
            }
            AcornValue::Not(x) => x.validate_against_stack(stack),
            AcornValue::Try(x, _) => x.validate_against_stack(stack),
            AcornValue::Constant(ci) => {
                if !ci.bound_value_args.is_empty()
                    && ci.bound_value_args.len() != ci.value_param_types.len()
                {
                    return Err(format!(
                        "'{}' has {} hidden value args but {} hidden value param types",
                        ci,
                        ci.bound_value_args.len(),
                        ci.value_param_types.len()
                    ));
                }
                for value_arg in &ci.bound_value_args {
                    value_arg.validate_against_stack(stack)?;
                }
                // Quoted kernel clauses can legitimately contain bare polymorphic constants
                // like `some = new` after extensionality peels all value arguments.
                // Those still carry generic parameter metadata even with no explicit type args.
                if ci.params.is_empty()
                    && ci.has_generic()
                    && ci.type_param_names.is_empty()
                    && ci.value_param_types.is_empty()
                    && ci.bound_value_args.is_empty()
                {
                    Err(format!("'{}' has generic type but no params", ci))
                } else {
                    Ok(())
                }
            }
            AcornValue::Bool(_) => Ok(()),
        }
    }

    /// Validate that all constants have the correct number of type parameters.
    /// Requires access to bindings to look up constant definitions.
    ///
    /// This catches bugs where a constant is instantiated with the wrong number of params,
    /// which can happen when UnresolvedConstant is incorrectly constructed during type inference.
    pub fn validate_constants(
        &self,
        bindings: &crate::elaborator::binding_map::BindingMap,
    ) -> Result<(), String> {
        let mut error = None;
        self.for_each_constant(&mut |ci| {
            if error.is_some() {
                return; // Already found an error
            }
            if let Some((def, def_params)) = bindings.get_definition_and_params(&ci.name) {
                // Check param count
                if ci.params.len() != def_params.len() {
                    error = Some(format!(
                        "Constant {} has {} params but definition has {}",
                        ci.name,
                        ci.params.len(),
                        def_params.len()
                    ));
                    return;
                }

                // Check that instance_type matches what we'd get by substituting params
                if !ci.params.is_empty() {
                    let substitution: Vec<_> = def_params.iter()
                        .zip(ci.params.iter())
                        .map(|(def_param, actual_param)| (def_param.name.clone(), actual_param.clone()))
                        .collect();
                    let expected_type = def.get_type().instantiate(&substitution);
                    if ci.instance_type != expected_type {
                        error = Some(format!(
                            "Constant {} has inconsistent instance_type.\nParams: {:?}\nExpected type: {}\nActual type: {}",
                            ci.name,
                            ci.params,
                            expected_type,
                            ci.instance_type
                        ));
                    }
                }
            }
        });
        error.map_or(Ok(()), Err)
    }

    fn instantiate_with_stack(
        &self,
        stack_size: AtomId,
        params: &[(String, AcornType)],
    ) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.instantiate_with_stack(stack_size, params))
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.instantiate_with_stack(stack_size, params)),
                args: app
                    .args
                    .iter()
                    .map(|x| x.instantiate_with_stack(stack_size, params))
                    .collect(),
            }),
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.instantiate_with_stack(stack_size, params)),
                type_param_names: app.type_param_names.clone(),
                type_param_constraints: app.type_param_constraints.clone(),
                type_args: app
                    .type_args
                    .iter()
                    .map(|x| x.instantiate_with_stack(stack_size, params))
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => {
                let mut current_stack_size = stack_size;
                let args = args
                    .iter()
                    .map(|arg_type| {
                        let instantiated =
                            arg_type.instantiate_with_stack(current_stack_size, params);
                        current_stack_size += 1;
                        instantiated
                    })
                    .collect::<Vec<_>>();
                AcornValue::Lambda(
                    args,
                    Box::new(value.instantiate_with_stack(current_stack_size, params)),
                )
            }
            AcornValue::ForAll(args, value) => {
                let mut current_stack_size = stack_size;
                let args = args
                    .iter()
                    .map(|arg_type| {
                        let instantiated =
                            arg_type.instantiate_with_stack(current_stack_size, params);
                        current_stack_size += 1;
                        instantiated
                    })
                    .collect::<Vec<_>>();
                AcornValue::ForAll(
                    args,
                    Box::new(value.instantiate_with_stack(current_stack_size, params)),
                )
            }
            AcornValue::Exists(args, value) => {
                let mut current_stack_size = stack_size;
                let args = args
                    .iter()
                    .map(|arg_type| {
                        let instantiated =
                            arg_type.instantiate_with_stack(current_stack_size, params);
                        current_stack_size += 1;
                        instantiated
                    })
                    .collect::<Vec<_>>();
                AcornValue::Exists(
                    args,
                    Box::new(value.instantiate_with_stack(current_stack_size, params)),
                )
            }
            AcornValue::Grouping(value) => {
                AcornValue::Grouping(Box::new(value.instantiate_with_stack(stack_size, params)))
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.instantiate_with_stack(stack_size, params)),
                Box::new(right.instantiate_with_stack(stack_size, params)),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.instantiate_with_stack(stack_size, params)),
                Box::new(if_value.instantiate_with_stack(stack_size, params)),
                Box::new(else_value.instantiate_with_stack(stack_size, params)),
            ),
            AcornValue::Match(scrutinee, cases) => {
                let new_scrutinee = scrutinee.instantiate_with_stack(stack_size, params);
                let new_cases = cases
                    .iter()
                    .map(|case| {
                        let mut current_stack_size = stack_size;
                        let new_vars = case
                            .new_vars
                            .iter()
                            .map(|t| {
                                let instantiated =
                                    t.instantiate_with_stack(current_stack_size, params);
                                current_stack_size += 1;
                                instantiated
                            })
                            .collect();
                        MatchCase {
                            new_vars,
                            pattern: case.pattern.instantiate_with_stack(
                                stack_size + case.new_vars.len() as AtomId,
                                params,
                            ),
                            result: case.result.instantiate_with_stack(
                                stack_size + case.new_vars.len() as AtomId,
                                params,
                            ),
                            constructor_index: case.constructor_index,
                            constructor_total: case.constructor_total,
                        }
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.instantiate_with_stack(stack_size, params)))
            }
            AcornValue::Try(x, t) => AcornValue::Try(
                Box::new(x.instantiate_with_stack(stack_size, params)),
                t.instantiate_with_stack(stack_size, params),
            ),
            AcornValue::Constant(c) => AcornValue::Constant(c.instantiate(params)),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    // Replace some type variables with other types.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornValue {
        self.instantiate_with_stack(0, params)
    }

    /// A value has_generic if anything within it has type variables.
    pub fn has_generic(&self) -> bool {
        match self {
            AcornValue::Variable(_, t) => t.has_generic(),
            AcornValue::Application(app) => {
                app.function.has_generic() || app.args.iter().any(|x| x.has_generic())
            }
            AcornValue::TypeApplication(ta) => {
                ta.function.has_generic() || ta.type_args.iter().any(|x| x.has_generic())
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                args.iter().any(|x| x.has_generic()) || value.has_generic()
            }
            AcornValue::Grouping(value) => value.has_generic(),
            AcornValue::Binary(_, left, right) => left.has_generic() || right.has_generic(),
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.has_generic() || if_value.has_generic() || else_value.has_generic()
            }
            AcornValue::Not(x) => x.has_generic(),
            AcornValue::Try(x, t) => x.has_generic() || t.has_generic(),
            AcornValue::Constant(c) => c.has_generic(),
            AcornValue::Bool(_) => false,
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.has_generic()
                    || cases
                        .iter()
                        .any(|case| case.pattern.has_generic() || case.result.has_generic())
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
            AcornValue::TypeApplication(ta) => {
                ta.function.has_arbitrary() || ta.type_args.iter().any(|x| x.has_arbitrary())
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.has_arbitrary(),
            AcornValue::Grouping(value) => value.has_arbitrary(),
            AcornValue::Binary(_, left, right) => left.has_arbitrary() || right.has_arbitrary(),
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.has_arbitrary() || if_value.has_arbitrary() || else_value.has_arbitrary()
            }
            AcornValue::Not(x) => x.has_arbitrary(),
            AcornValue::Try(x, t) => x.has_arbitrary() || t.has_arbitrary(),
            AcornValue::Constant(c) => c.has_arbitrary(),
            AcornValue::Bool(_) => false,
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.has_arbitrary()
                    || cases
                        .iter()
                        .any(|case| case.pattern.has_arbitrary() || case.result.has_arbitrary())
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
            AcornValue::TypeApplication(app) => {
                app.function.for_each_constant(f);
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.for_each_constant(f),
            AcornValue::Grouping(value) => value.for_each_constant(f),
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
                for case in cases {
                    case.pattern.for_each_constant(f);
                    case.result.for_each_constant(f);
                }
            }
            AcornValue::Not(x) => x.for_each_constant(f),
            AcornValue::Try(x, _) => x.for_each_constant(f),
            AcornValue::Constant(c) => {
                for value_arg in &c.bound_value_args {
                    value_arg.for_each_constant(f);
                }
                f(c)
            }
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
            AcornValue::TypeApplication(app) => {
                app.function.for_each_type(f);
                for type_arg in &app.type_args {
                    f(type_arg);
                }
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
            AcornValue::Grouping(value) => value.for_each_type(f),
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
                for case in cases {
                    // Process types introduced by the match
                    for var_type in &case.new_vars {
                        f(var_type);
                    }
                    case.pattern.for_each_type(f);
                    case.result.for_each_type(f);
                }
            }
            AcornValue::Not(x) => x.for_each_type(f),
            AcornValue::Try(x, t) => {
                x.for_each_type(f);
                f(t);
            }
            AcornValue::Constant(c) => {
                // Process instance type
                f(&c.instance_type);
                // Also process type parameters
                for param in &c.params {
                    f(param);
                }
                for value_param_type in &c.value_param_types {
                    f(value_param_type);
                }
                for bound_value_arg in &c.bound_value_args {
                    bound_value_arg.for_each_type(f);
                }
            }
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

    /// Converts all the type variables to arbitrary types.
    pub fn to_arbitrary(&self) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => AcornValue::Variable(*i, var_type.to_arbitrary()),
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.to_arbitrary()),
                args: app.args.iter().map(|x| x.to_arbitrary()).collect(),
            }),
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.to_arbitrary()),
                type_param_names: app.type_param_names.clone(),
                type_param_constraints: app.type_param_constraints.clone(),
                type_args: app.type_args.iter().map(|x| x.to_arbitrary()).collect(),
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
            AcornValue::Grouping(value) => AcornValue::Grouping(Box::new(value.to_arbitrary())),
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
                    .map(|case| MatchCase {
                        new_vars: case.new_vars.clone(),
                        pattern: case.pattern.to_arbitrary(),
                        result: case.result.to_arbitrary(),
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.to_arbitrary())),
            AcornValue::Try(x, t) => AcornValue::Try(Box::new(x.to_arbitrary()), t.to_arbitrary()),
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
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.genericize(params)),
                type_param_names: app.type_param_names.clone(),
                type_param_constraints: app.type_param_constraints.clone(),
                type_args: app.type_args.iter().map(|x| x.genericize(params)).collect(),
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
            AcornValue::Grouping(value) => AcornValue::Grouping(Box::new(value.genericize(params))),
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
                for case in cases {
                    let new_vars = case
                        .new_vars
                        .iter()
                        .map(|t| t.genericize(params))
                        .collect::<Vec<_>>();
                    let new_pattern = case.pattern.genericize(params);
                    let new_result = case.result.genericize(params);
                    new_cases.push(MatchCase {
                        new_vars,
                        pattern: new_pattern,
                        result: new_result,
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    });
                }
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.genericize(params))),
            AcornValue::Try(x, t) => {
                AcornValue::Try(Box::new(x.genericize(params)), t.genericize(params))
            }
            AcornValue::Constant(c) => AcornValue::Constant(c.genericize(params)),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    pub fn arbitrary_to_variable(&self) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.arbitrary_to_variable())
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.arbitrary_to_variable()),
                args: app.args.iter().map(|x| x.arbitrary_to_variable()).collect(),
            }),
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.arbitrary_to_variable()),
                type_param_names: app.type_param_names.clone(),
                type_param_constraints: app.type_param_constraints.clone(),
                type_args: app
                    .type_args
                    .iter()
                    .map(|x| x.arbitrary_to_variable())
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter().map(|x| x.arbitrary_to_variable()).collect(),
                Box::new(value.arbitrary_to_variable()),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter().map(|x| x.arbitrary_to_variable()).collect(),
                Box::new(value.arbitrary_to_variable()),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter().map(|x| x.arbitrary_to_variable()).collect(),
                Box::new(value.arbitrary_to_variable()),
            ),
            AcornValue::Grouping(value) => {
                AcornValue::Grouping(Box::new(value.arbitrary_to_variable()))
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.arbitrary_to_variable()),
                Box::new(right.arbitrary_to_variable()),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.arbitrary_to_variable()),
                Box::new(if_value.arbitrary_to_variable()),
                Box::new(else_value.arbitrary_to_variable()),
            ),
            AcornValue::Match(scrutinee, cases) => AcornValue::Match(
                Box::new(scrutinee.arbitrary_to_variable()),
                cases
                    .iter()
                    .map(|case| MatchCase {
                        new_vars: case
                            .new_vars
                            .iter()
                            .map(|t| t.arbitrary_to_variable())
                            .collect(),
                        pattern: case.pattern.arbitrary_to_variable(),
                        result: case.result.arbitrary_to_variable(),
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    })
                    .collect(),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.arbitrary_to_variable())),
            AcornValue::Try(x, t) => AcornValue::Try(
                Box::new(x.arbitrary_to_variable()),
                t.arbitrary_to_variable(),
            ),
            AcornValue::Constant(c) => AcornValue::Constant(ConstantInstance {
                name: c.name.clone(),
                params: c.params.iter().map(|t| t.arbitrary_to_variable()).collect(),
                instance_type: c.instance_type.arbitrary_to_variable(),
                generic_type: c.generic_type.arbitrary_to_variable(),
                type_param_names: c.type_param_names.clone(),
                value_param_types: c
                    .value_param_types
                    .iter()
                    .map(|t| t.arbitrary_to_variable())
                    .collect(),
                bound_value_args: c
                    .bound_value_args
                    .iter()
                    .map(|value| value.arbitrary_to_variable())
                    .collect(),
            }),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    pub fn abstract_over_datatype(&self, datatype: &Datatype, param: TypeParam) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.abstract_over_datatype(datatype, param))
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.abstract_over_datatype(datatype, param.clone())),
                args: app
                    .args
                    .iter()
                    .map(|x| x.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
            }),
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.abstract_over_datatype(datatype, param.clone())),
                type_param_names: app.type_param_names.clone(),
                type_param_constraints: app.type_param_constraints.clone(),
                type_args: app
                    .type_args
                    .iter()
                    .map(|x| x.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
                Box::new(value.abstract_over_datatype(datatype, param.clone())),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
                Box::new(value.abstract_over_datatype(datatype, param.clone())),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
                Box::new(value.abstract_over_datatype(datatype, param.clone())),
            ),
            AcornValue::Grouping(value) => AcornValue::Grouping(Box::new(
                value.abstract_over_datatype(datatype, param.clone()),
            )),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.abstract_over_datatype(datatype, param.clone())),
                Box::new(right.abstract_over_datatype(datatype, param.clone())),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.abstract_over_datatype(datatype, param.clone())),
                Box::new(if_value.abstract_over_datatype(datatype, param.clone())),
                Box::new(else_value.abstract_over_datatype(datatype, param.clone())),
            ),
            AcornValue::Match(scrutinee, cases) => AcornValue::Match(
                Box::new(scrutinee.abstract_over_datatype(datatype, param.clone())),
                cases
                    .iter()
                    .map(|case| MatchCase {
                        new_vars: case
                            .new_vars
                            .iter()
                            .map(|t| t.abstract_over_datatype(datatype, param.clone()))
                            .collect(),
                        pattern: case.pattern.abstract_over_datatype(datatype, param.clone()),
                        result: case.result.abstract_over_datatype(datatype, param.clone()),
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    })
                    .collect(),
            ),
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.abstract_over_datatype(datatype, param.clone())))
            }
            AcornValue::Try(x, t) => AcornValue::Try(
                Box::new(x.abstract_over_datatype(datatype, param.clone())),
                t.abstract_over_datatype(datatype, param.clone()),
            ),
            AcornValue::Constant(c) => AcornValue::Constant(ConstantInstance {
                name: c.name.clone(),
                params: c
                    .params
                    .iter()
                    .map(|t| t.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
                instance_type: c
                    .instance_type
                    .abstract_over_datatype(datatype, param.clone()),
                generic_type: c
                    .generic_type
                    .abstract_over_datatype(datatype, param.clone()),
                type_param_names: c.type_param_names.clone(),
                value_param_types: c
                    .value_param_types
                    .iter()
                    .map(|t| t.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
                bound_value_args: c
                    .bound_value_args
                    .iter()
                    .map(|value| value.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
            }),
            AcornValue::Bool(_) => self.clone(),
        }
    }

    pub fn has_arbitrary_type_param(&self, param: &TypeParam) -> bool {
        match self {
            AcornValue::Variable(_, var_type) => var_type.has_arbitrary_type_param(param),
            AcornValue::Application(app) => {
                app.function.has_arbitrary_type_param(param)
                    || app.args.iter().any(|x| x.has_arbitrary_type_param(param))
            }
            AcornValue::TypeApplication(app) => {
                app.function.has_arbitrary_type_param(param)
                    || app
                        .type_args
                        .iter()
                        .any(|x| x.has_arbitrary_type_param(param))
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                args.iter().any(|x| x.has_arbitrary_type_param(param))
                    || value.has_arbitrary_type_param(param)
            }
            AcornValue::Grouping(value) => value.has_arbitrary_type_param(param),
            AcornValue::Binary(_, left, right) => {
                left.has_arbitrary_type_param(param) || right.has_arbitrary_type_param(param)
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.has_arbitrary_type_param(param)
                    || if_value.has_arbitrary_type_param(param)
                    || else_value.has_arbitrary_type_param(param)
            }
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.has_arbitrary_type_param(param)
                    || cases.iter().any(|case| {
                        case.new_vars
                            .iter()
                            .any(|t| t.has_arbitrary_type_param(param))
                            || case.pattern.has_arbitrary_type_param(param)
                            || case.result.has_arbitrary_type_param(param)
                    })
            }
            AcornValue::Not(x) => x.has_arbitrary_type_param(param),
            AcornValue::Try(x, t) => {
                x.has_arbitrary_type_param(param) || t.has_arbitrary_type_param(param)
            }
            AcornValue::Constant(c) => {
                c.instance_type.has_arbitrary_type_param(param)
                    || c.params.iter().any(|t| t.has_arbitrary_type_param(param))
            }
            AcornValue::Bool(_) => false,
        }
    }

    pub fn contains_type_var(&self, param: &TypeParam) -> bool {
        match self {
            AcornValue::Variable(_, var_type) => var_type.contains_type_var(param),
            AcornValue::Application(app) => {
                app.function.contains_type_var(param)
                    || app.args.iter().any(|x| x.contains_type_var(param))
            }
            AcornValue::TypeApplication(app) => {
                app.function.contains_type_var(param)
                    || app.type_args.iter().any(|x| x.contains_type_var(param))
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                args.iter().any(|x| x.contains_type_var(param)) || value.contains_type_var(param)
            }
            AcornValue::Grouping(value) => value.contains_type_var(param),
            AcornValue::Binary(_, left, right) => {
                left.contains_type_var(param) || right.contains_type_var(param)
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.contains_type_var(param)
                    || if_value.contains_type_var(param)
                    || else_value.contains_type_var(param)
            }
            AcornValue::Match(scrutinee, cases) => {
                scrutinee.contains_type_var(param)
                    || cases.iter().any(|case| {
                        case.new_vars.iter().any(|t| t.contains_type_var(param))
                            || case.pattern.contains_type_var(param)
                            || case.result.contains_type_var(param)
                    })
            }
            AcornValue::Not(x) => x.contains_type_var(param),
            AcornValue::Try(x, t) => x.contains_type_var(param) || t.contains_type_var(param),
            AcornValue::Constant(c) => {
                c.instance_type.contains_type_var(param)
                    || c.params.iter().any(|t| t.contains_type_var(param))
            }
            AcornValue::Bool(_) => false,
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
            AcornValue::TypeApplication(app) => AcornValue::TypeApplication(TypeApplication {
                function: Box::new(app.function.set_params(name, params)),
                type_param_names: app.type_param_names,
                type_param_constraints: app.type_param_constraints,
                type_args: app.type_args,
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
            AcornValue::Grouping(value) => {
                AcornValue::Grouping(Box::new(value.set_params(name, params)))
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
                    .map(|case| MatchCase {
                        new_vars: case.new_vars,
                        pattern: case.pattern.set_params(name, params),
                        result: case.result.set_params(name, params),
                        constructor_index: case.constructor_index,
                        constructor_total: case.constructor_total,
                    })
                    .collect();
                AcornValue::Match(Box::new(new_scrutinee), new_cases)
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.set_params(name, params))),
            AcornValue::Try(x, t) => AcornValue::Try(Box::new(x.set_params(name, params)), t),
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
            AcornValue::TypeApplication(app) => app.function.as_attribute(),
            _ => None,
        }
    }

    /// If this is a plain constant, give access to its name.
    /// Otherwise, return None.
    pub fn as_name(&self) -> Option<&ConstantName> {
        match &self {
            AcornValue::Constant(c) => Some(&c.name),
            AcornValue::TypeApplication(app) => app.function.as_name(),
            _ => None,
        }
    }

    /// If this is a function call of a constant function, give access to its name.
    pub fn is_named_function_call(&self) -> Option<&ConstantName> {
        match self {
            AcornValue::Application(fa) => fa.function.as_name(),
            AcornValue::TypeApplication(app) => app.function.is_named_function_call(),
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
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
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
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        // Typecheck the arguments
        let (function_type, checked_args_start) = match &self {
            AcornValue::Constant(constant) if !constant.bound_value_args.is_empty() => {
                (constant.instance_type.clone(), 0)
            }
            AcornValue::Constant(constant) if !constant.value_param_types.is_empty() => {
                let num_specialization_args =
                    constant.pending_value_specialization_arg_count(args.len());
                for (arg, arg_type) in args[..num_specialization_args]
                    .iter()
                    .zip(constant.value_param_types.iter())
                {
                    arg.check_type(Some(arg_type), source)?;
                }
                let visible_prefix_count = constant
                    .visible_value_param_prefix_count()
                    .min(num_specialization_args);
                let mut function_type = constant
                    .instance_type
                    .bind_value_params(&args[..num_specialization_args]);
                if visible_prefix_count > 0 {
                    for arg in &args[..visible_prefix_count] {
                        function_type = match function_type {
                            AcornType::Function(function_type) => function_type
                                .applied_type(1)
                                .bind_values(0, 0, std::slice::from_ref(arg)),
                            _ => {
                                return Err(
                                    source.error("cannot apply visible dependent value parameters")
                                )
                            }
                        };
                    }
                }
                (function_type, num_specialization_args)
            }
            _ => (self.get_type(), 0),
        };
        let remaining_args = &args[checked_args_start..];
        match &function_type {
            AcornType::Function(_) => {}
            _ if remaining_args.is_empty() => {
                let value = AcornValue::apply(self, args);
                value.check_type(expected_type, source)?;
                return Ok(value);
            }
            _ => return Err(source.error("cannot apply a non-function")),
        }
        let value = AcornValue::apply(self, args);
        if let AcornValue::Application(app) = &value {
            app.typecheck().map_err(|e| source.error(&e))?;
        }
        value.check_type(expected_type, source)?;
        Ok(value)
    }

    /// A display version for when this value is a subvalue.
    pub fn display_as_subvalue(&self, stack_size: usize) -> String {
        let subvalue = Subvalue {
            value: self,
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
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
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
            AcornValue::TypeApplication(app) => {
                app.function.find_type_vars(vars, source)?;
                for type_arg in &app.type_args {
                    type_arg.find_type_vars(vars, source)?;
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
            AcornValue::Grouping(value) => {
                value.find_type_vars(vars, source)?;
            }
            AcornValue::Binary(_, left, right) => {
                left.find_type_vars(vars, source)?;
                right.find_type_vars(vars, source)?;
            }
            AcornValue::Not(x) => {
                x.find_type_vars(vars, source)?;
            }
            AcornValue::Try(x, t) => {
                x.find_type_vars(vars, source)?;
                t.find_type_vars(vars, source)?;
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
                for case in cases {
                    for var_type in &case.new_vars {
                        var_type.find_type_vars(vars, source)?;
                    }
                    case.pattern.find_type_vars(vars, source)?;
                    case.result.find_type_vars(vars, source)?;
                }
            }
            AcornValue::Bool(_) => {
                // Bool values don't contain type variables
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborator::acorn_type::DependentTypeArg;
    use crate::module::ModuleId;

    #[test]
    fn test_is_lambda_treats_grouped_lambda_as_lambda() {
        let lambda = AcornValue::lambda(vec![AcornType::Bool], AcornValue::Bool(true));
        let grouped = AcornValue::grouped(lambda.clone());
        let type_applied = AcornValue::type_apply(
            grouped,
            vec!["T".to_string()],
            vec![None],
            vec![AcornType::Bool],
        );

        assert!(lambda.is_lambda());
        assert!(type_applied.is_lambda());
    }

    #[test]
    fn test_genericize_with_nested_type_params() {
        // Test the bug where genericizing a ConstantInstance with params like [T, List<U>]
        // incorrectly adds U as a third parameter.

        // Create type params T and U
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let u_param = TypeParam {
            name: "U".to_string(),
            typeclass: None,
        };

        // Create List datatype
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };

        // Create a ConstantInstance with params: [Arbitrary(T), Data(List, [Arbitrary(U)])]
        // This is like a function that takes T and returns something with List<U>
        let generic_type = AcornType::functional(
            vec![
                AcornType::Variable(t_param.clone()),
                AcornType::functional(
                    vec![AcornType::Variable(t_param.clone())],
                    AcornType::Data(
                        list_datatype.clone(),
                        vec![AcornType::Variable(u_param.clone())],
                    ),
                ),
            ],
            AcornType::Data(
                list_datatype.clone(),
                vec![AcornType::Data(
                    list_datatype.clone(),
                    vec![AcornType::Variable(u_param.clone())],
                )],
            ),
        );
        let instance = ConstantInstance {
            name: ConstantName::unqualified(ModuleId(0), "test_fn"),
            params: vec![
                AcornType::Arbitrary(t_param.clone()),
                AcornType::Data(
                    list_datatype.clone(),
                    vec![AcornType::Arbitrary(u_param.clone())],
                ),
            ],
            instance_type: AcornType::functional(
                vec![
                    AcornType::Arbitrary(t_param.clone()),
                    AcornType::functional(
                        vec![AcornType::Arbitrary(t_param.clone())],
                        AcornType::Data(
                            list_datatype.clone(),
                            vec![AcornType::Arbitrary(u_param.clone())],
                        ),
                    ),
                ],
                AcornType::Data(
                    list_datatype.clone(),
                    vec![AcornType::Data(
                        list_datatype.clone(),
                        vec![AcornType::Arbitrary(u_param.clone())],
                    )],
                ),
            ),
            generic_type,
            type_param_names: vec!["T".to_string(), "U".to_string()],
            value_param_types: vec![],
            bound_value_args: vec![],
        };

        // Genericize with [T, U]
        let genericized = instance.genericize(&[t_param.clone(), u_param.clone()]);

        // The result should have exactly 2 params: [Variable(T), Data(List, [Variable(U)])]
        // NOT 3 params with Variable(U) added as a third parameter
        assert_eq!(
            genericized.params.len(),
            2,
            "Expected 2 params after genericization, got {}: {:?}",
            genericized.params.len(),
            genericized.params
        );

        // Verify the params are what we expect
        assert_eq!(genericized.params[0], AcornType::Variable(t_param.clone()));
        assert_eq!(
            genericized.params[1],
            AcornType::Data(
                list_datatype.clone(),
                vec![AcornType::Variable(u_param.clone())]
            )
        );
    }

    #[test]
    fn test_bind_value_params_keeps_outer_value_args_stable_through_function_type() {
        let nat_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let fin_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Fin".to_string(),
        };
        let nat_type = AcornType::Data(nat_datatype, vec![]);
        let family_arg = DependentTypeArg::Value(AcornValue::Variable(0, nat_type.clone()));
        let function_type = AcornType::functional(
            vec![
                nat_type.clone(),
                AcornType::Family(fin_datatype.clone(), vec![family_arg.clone()]),
            ],
            AcornType::Family(fin_datatype, vec![family_arg]),
        );

        let bound = function_type.bind_value_params(&[AcornValue::Variable(0, nat_type.clone())]);
        let expected = AcornType::functional(
            vec![
                nat_type.clone(),
                AcornType::Family(
                    Datatype {
                        module_id: ModuleId(0),
                        name: "Fin".to_string(),
                    },
                    vec![DependentTypeArg::Value(AcornValue::Variable(
                        0,
                        nat_type.clone(),
                    ))],
                ),
            ],
            AcornType::Family(
                Datatype {
                    module_id: ModuleId(0),
                    name: "Fin".to_string(),
                },
                vec![DependentTypeArg::Value(AcornValue::Variable(0, nat_type))],
            ),
        );

        assert_eq!(bound, expected);
    }

    #[test]
    fn test_function_application_type_keeps_hidden_family_args_stable() {
        struct TestContext;
        impl crate::elaborator::error::ErrorContext for TestContext {
            fn error(&self, msg: &str) -> crate::elaborator::error::Error {
                let token = crate::syntax::token::Token::empty();
                crate::elaborator::error::Error::new(&token, &token, msg)
            }
        }

        let nat_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let option_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Option".to_string(),
        };
        let fin_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Fin".to_string(),
        };
        let nat_type = AcornType::Data(nat_datatype, vec![]);
        let fin_of_n = AcornType::Family(
            fin_datatype,
            vec![DependentTypeArg::Value(AcornValue::Variable(
                0,
                nat_type.clone(),
            ))],
        );
        let option_fin_of_n = AcornType::Data(option_datatype, vec![fin_of_n.clone()]);
        let new_constant = ConstantInstance {
            name: ConstantName::unqualified(ModuleId(0), "new"),
            params: vec![],
            instance_type: AcornType::functional(vec![nat_type.clone()], option_fin_of_n.clone()),
            generic_type: AcornType::functional(vec![nat_type.clone()], option_fin_of_n.clone()),
            type_param_names: vec![],
            value_param_types: vec![nat_type.clone()],
            bound_value_args: vec![],
        }
        .bind_value_params(&[AcornValue::Variable(0, nat_type.clone())], &TestContext)
        .expect("specialize constant");

        let applied = AcornValue::apply(
            AcornValue::Constant(new_constant),
            vec![AcornValue::Variable(1, nat_type)],
        );
        assert_eq!(applied.get_type(), option_fin_of_n);
    }
}
