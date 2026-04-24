use std::{collections::HashMap, fmt};

use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::error::{self, ErrorContext, Result};
use crate::module::ModuleId;

/// Variance of a type parameter indicates how it appears in a type definition.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Variance {
    /// Type parameter appears only in positive positions (covariant)
    Positive,
    /// Type parameter appears only in negative positions (contravariant)
    Negative,
    /// Type parameter appears in both positive and negative positions (invariant)
    Both,
    /// Type parameter doesn't appear at all
    None,
}

impl Variance {
    /// Merge two variance occurrences
    pub fn merge(self, other: Variance) -> Variance {
        match (self, other) {
            (Variance::None, v) | (v, Variance::None) => v,
            (Variance::Positive, Variance::Positive) => Variance::Positive,
            (Variance::Negative, Variance::Negative) => Variance::Negative,
            (Variance::Both, _) | (_, Variance::Both) => Variance::Both,
            (Variance::Positive, Variance::Negative) | (Variance::Negative, Variance::Positive) => {
                Variance::Both
            }
        }
    }
}

/// Datatypes are represented by the module they were defined in, and their name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Datatype {
    pub module_id: ModuleId,
    pub name: String,
}

/// Typeclasses are represented by the module they were defined in, and their name.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Typeclass {
    pub module_id: ModuleId,
    pub name: String,
}

impl Typeclass {
    pub fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D) -> pretty::DocBuilder<'a, D, A>
    where
        A: 'a,
        D: pretty::DocAllocator<'a, A>,
    {
        allocator.text(&self.name)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum DependentTypeArg {
    Type(AcornType),
    Value(AcornValue),
}

impl fmt::Display for DependentTypeArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DependentTypeArg::Type(acorn_type) => write!(f, "{}", acorn_type),
            DependentTypeArg::Value(value) => write!(f, "{}", value),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct UnresolvedType {
    /// The user-facing name for this generic type.
    pub name: String,

    /// The parameters we need to instantiate this type.
    pub params: Vec<FamilyParamKind>,

    /// The instantiated type template after applying those parameters.
    /// This is stored using canonical arbitrary type names T0, T1, ...
    pub template: AcornType,
}

impl UnresolvedType {
    pub fn canonical_type_args_for(params: &[FamilyParamKind]) -> Vec<AcornType> {
        let mut args = vec![];
        let mut next_index = 0;
        for param in params {
            if let FamilyParamKind::Type(typeclass) = param {
                args.push(AcornType::Arbitrary(TypeParam {
                    name: format!("T{}", next_index),
                    typeclass: typeclass.clone(),
                }));
                next_index += 1;
            }
        }
        args
    }

    pub fn canonical_args_for(params: &[FamilyParamKind]) -> Vec<DependentTypeArg> {
        let mut args = vec![];
        let mut next_type_index = 0;
        let mut next_value_index = 0;
        for param in params {
            match param {
                FamilyParamKind::Type(typeclass) => {
                    args.push(DependentTypeArg::Type(AcornType::Arbitrary(TypeParam {
                        name: format!("T{}", next_type_index),
                        typeclass: typeclass.clone(),
                    })));
                    next_type_index += 1;
                }
                FamilyParamKind::Value(value_type) => {
                    args.push(DependentTypeArg::Value(AcornValue::Variable(
                        next_value_index,
                        value_type.clone(),
                    )));
                    next_value_index += 1;
                }
            }
        }
        args
    }

    pub fn canonical_template_for_datatype(
        name: String,
        datatype: Datatype,
        params: Vec<FamilyParamKind>,
    ) -> UnresolvedType {
        let args = Self::canonical_args_for(&params);
        UnresolvedType {
            name,
            params,
            template: AcornType::new_datatype_application(datatype, args),
        }
    }

    pub fn base_datatype(&self) -> Option<&Datatype> {
        match &self.template {
            AcornType::Data(datatype, _) | AcornType::Family(datatype, _) => Some(datatype),
            _ => None,
        }
    }

    fn instantiate_template(&self, params: &[DependentTypeArg]) -> AcornType {
        let mut type_replacements = vec![];
        let mut value_replacements = vec![];
        let mut next_type_index = 0;
        for arg in params {
            match arg {
                DependentTypeArg::Type(param) => {
                    type_replacements.push((format!("T{}", next_type_index), param.clone()));
                    next_type_index += 1;
                }
                DependentTypeArg::Value(value) => value_replacements.push(value.clone()),
            }
        }
        self.template
            .instantiate(&type_replacements)
            .bind_value_params(&value_replacements)
    }

    pub fn has_value_params(&self) -> bool {
        self.params
            .iter()
            .any(|param| matches!(param, FamilyParamKind::Value(_)))
    }

    pub fn type_param_constraints(&self) -> Option<Vec<Option<Typeclass>>> {
        let mut constraints = vec![];
        for param in &self.params {
            match param {
                FamilyParamKind::Type(typeclass) => constraints.push(typeclass.clone()),
                FamilyParamKind::Value(_) => return None,
            }
        }
        Some(constraints)
    }

    pub fn is_identity_alias(&self) -> bool {
        !self.has_value_params()
            && self.base_datatype().is_some()
            && self.template
                == AcornType::new_datatype_application(
                    self.base_datatype().unwrap().clone(),
                    Self::canonical_args_for(&self.params),
                )
    }

    /// Just sticks fake names in there to print.
    pub fn to_display_type(&self) -> AcornType {
        self.template.arbitrary_to_variable()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PotentialType {
    /// A usable type.
    Resolved(AcornType),

    /// A generic type that we don't know the parameters for yet.
    /// (module, name, number of parameters).
    Unresolved(UnresolvedType),
}

impl PotentialType {
    pub fn resolve_args(
        self,
        params: Vec<DependentTypeArg>,
        source: &dyn ErrorContext,
    ) -> Result<AcornType> {
        match self {
            PotentialType::Resolved(t) => {
                if !params.is_empty() {
                    Err(source.error("resolved type cannot take parameters"))
                } else {
                    Ok(t)
                }
            }
            PotentialType::Unresolved(ut) => {
                if params.len() != ut.params.len() {
                    Err(source.error(&format!(
                        "type {} expects {} parameters, but got {}",
                        ut.name,
                        ut.params.len(),
                        params.len()
                    )))
                } else {
                    // TODO: check that params obey the constraints in ut.params.
                    Ok(ut.instantiate_template(&params))
                }
            }
        }
    }

    /// Resolves the type given the parameters.
    /// Every replacement must be a type variable being replaced with an arbitrary type.
    pub fn invertible_resolve(
        self,
        params: Vec<AcornType>,
        source: &dyn ErrorContext,
    ) -> Result<AcornType> {
        if let PotentialType::Unresolved(ut) = &self {
            let Some(type_params) = ut.type_param_constraints() else {
                return Err(source.error(&format!(
                    "type {} has dependent value parameters and cannot be resolved here",
                    ut.name
                )));
            };
            if ut.params.len() != params.len() {
                return Err(source.error(&format!(
                    "type {} expects {} parameters, but got {}",
                    ut.name,
                    ut.params.len(),
                    params.len()
                )));
            }
            for (i, (typeclass, param_type)) in type_params.iter().zip(params.iter()).enumerate() {
                match param_type {
                    AcornType::Arbitrary(param) => {
                        if typeclass != &param.typeclass {
                            return Err(source.error(&format!(
                                "expected param {} to have typeclass {:?}, but got {:?}",
                                i, typeclass, param.typeclass
                            )));
                        }
                    }
                    _ => {
                        // Can this even happen?
                        return Err(source.error("bad parameter syntax"));
                    }
                }
            }
        }
        self.resolve_args(
            params.into_iter().map(DependentTypeArg::Type).collect(),
            source,
        )
    }

    /// Resolves the type given parameters with arbitrary types.
    /// Like invertible_resolve, but allows the parameters to have more restrictive typeclass
    /// constraints than the base type. This is useful for attributes blocks where we want to
    /// add additional typeclass constraints.
    /// For example: structure Set[K] can have attributes Set[T: Twosome].
    pub fn resolve_with_arbitrary(
        self,
        params: Vec<AcornType>,
        source: &dyn ErrorContext,
    ) -> Result<AcornType> {
        if let PotentialType::Unresolved(ut) = &self {
            if ut.has_value_params() {
                return Err(source.error(&format!(
                    "type {} has dependent value parameters and cannot be resolved here",
                    ut.name
                )));
            }
            if ut.params.len() != params.len() {
                return Err(source.error(&format!(
                    "type {} expects {} parameters, but got {}",
                    ut.name,
                    ut.params.len(),
                    params.len()
                )));
            }
            for (i, param_type) in params.iter().enumerate() {
                match param_type {
                    AcornType::Arbitrary(_) => {
                        // Arbitrary types are allowed.
                        // We don't validate typeclass constraints here because attributes
                        // are allowed to add more restrictive constraints.
                    }
                    _ => {
                        return Err(source.error(&format!(
                            "expected param {} to be an arbitrary type variable",
                            i
                        )));
                    }
                }
            }
        }
        self.resolve_args(
            params.into_iter().map(DependentTypeArg::Type).collect(),
            source,
        )
    }

    /// Resolves the type given the parameters.
    /// Reports an error if the parameters don't match what we expected.
    pub fn resolve(self, params: Vec<AcornType>, source: &dyn ErrorContext) -> Result<AcornType> {
        if let PotentialType::Unresolved(ut) = &self {
            if ut.has_value_params() {
                return Err(source.error(&format!(
                    "type {} has dependent value parameters and cannot be resolved here",
                    ut.name
                )));
            }
        }
        self.resolve_args(
            params.into_iter().map(DependentTypeArg::Type).collect(),
            source,
        )
    }

    /// If this potential type represents a base datatype, ie with no type parameters,
    /// return a reference to the datatype.
    /// Thus, Nat is a base datatype, and List[T] is a base datatype, but List[Bool] is not.
    pub fn as_base_datatype(&self) -> Option<&Datatype> {
        match self {
            PotentialType::Resolved(AcornType::Data(datatype, params)) => {
                if params.is_empty() {
                    Some(datatype)
                } else {
                    None
                }
            }
            PotentialType::Unresolved(ut) => ut.base_datatype(),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct FunctionType {
    pub arg_types: Vec<AcornType>,
    pub return_type: Box<AcornType>,
}

impl fmt::Display for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lhs = if self.arg_types.len() == 1 {
            let arg_type = &self.arg_types[0];
            if arg_type.is_functional() {
                format!("({})", arg_type)
            } else {
                format!("{}", arg_type)
            }
        } else {
            format!("({})", AcornType::types_to_str(&self.arg_types))
        };
        // Since -> is right-associative, we need to parenthesize functional return types
        // to avoid ambiguity. For example, ((A, B) -> C) -> D should not be printed as
        // (A, B) -> C -> D, which would parse as (A, B) -> (C -> D).
        let rhs = if self.return_type.is_functional() {
            format!("({})", self.return_type)
        } else {
            format!("{}", self.return_type)
        };
        write!(f, "{} -> {}", lhs, rhs)
    }
}

impl FunctionType {
    /// Creates a new function type by normalizing arguments and return type.
    fn new(arg_types: Vec<AcornType>, return_type: AcornType) -> FunctionType {
        assert!(!arg_types.is_empty());
        if let AcornType::Function(ftype) = return_type {
            // Normalize function types by un-currying.
            let combined_args = arg_types.into_iter().chain(ftype.arg_types).collect();
            FunctionType {
                arg_types: combined_args,
                return_type: ftype.return_type,
            }
        } else {
            FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            }
        }
    }

    /// Makes a partial type by removing the first n arguments.
    fn remove_args(&self, n: usize) -> FunctionType {
        assert!(n < self.arg_types.len());
        FunctionType {
            arg_types: self.arg_types[n..].to_vec(),
            return_type: self.return_type.clone(),
        }
    }

    /// The type after applying this function to a certain number of arguments.
    /// Panics if the application is invalid.
    pub fn applied_type(&self, num_args: usize) -> AcornType {
        if num_args > self.arg_types.len() {
            panic!(
                "Can't apply function type {:?} taking {} args to {} args",
                self,
                self.arg_types.len(),
                num_args
            );
        }
        if num_args == self.arg_types.len() {
            *self.return_type.clone()
        } else {
            AcornType::Function(self.remove_args(num_args))
        }
    }

    /// Checks if this function type contains any arbitrary types.
    pub fn has_arbitrary(&self) -> bool {
        self.arg_types.iter().any(|t| t.has_arbitrary()) || self.return_type.has_arbitrary()
    }
}

/// A type parameter is a way of naming a type by its properties.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct TypeParam {
    pub name: String,
    pub typeclass: Option<Typeclass>,
}

impl fmt::Display for TypeParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(tc) = &self.typeclass {
            write!(f, "{}: {}", self.name, tc.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl TypeParam {
    /// Converts a list of type parameters to a string representation.
    pub fn params_to_str(params: &[TypeParam]) -> String {
        let mut result = "[".to_string();
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("{}", param));
        }
        result.push(']');
        result
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct ValueParam {
    pub name: String,
    pub value_type: AcornType,
}

impl fmt::Display for ValueParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.value_type)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum FamilyParam {
    Type(TypeParam),
    Value(ValueParam),
}

impl FamilyParam {
    pub fn name(&self) -> &str {
        match self {
            FamilyParam::Type(type_param) => &type_param.name,
            FamilyParam::Value(value_param) => &value_param.name,
        }
    }

    pub fn kind(&self) -> FamilyParamKind {
        match self {
            FamilyParam::Type(type_param) => FamilyParamKind::Type(type_param.typeclass.clone()),
            FamilyParam::Value(value_param) => {
                FamilyParamKind::Value(value_param.value_type.clone())
            }
        }
    }

    pub fn as_type_param(&self) -> Option<&TypeParam> {
        match self {
            FamilyParam::Type(type_param) => Some(type_param),
            FamilyParam::Value(_) => None,
        }
    }

    pub fn as_value_param(&self) -> Option<&ValueParam> {
        match self {
            FamilyParam::Type(_) => None,
            FamilyParam::Value(value_param) => Some(value_param),
        }
    }
}

impl fmt::Display for FamilyParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FamilyParam::Type(type_param) => write!(f, "{}", type_param),
            FamilyParam::Value(value_param) => write!(f, "{}", value_param),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum FamilyParamKind {
    Type(Option<Typeclass>),
    Value(AcornType),
}

/// Every AcornValue has an AcornType.
/// This is the "richer" form of a type. The environment uses these types; the prover uses ids.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum AcornType {
    /// Booleans are special
    Bool,

    /// Data types are structures, inductive types, or axiomatic types.
    /// They have a datatype, and may have type parameters.
    Data(Datatype, Vec<AcornType>),

    /// Datatype families with at least one value-level argument.
    /// The arguments remain in declaration order, so mixed families like `Vector[T, n]`
    /// can preserve which positions are types and which are values.
    Family(Datatype, Vec<DependentTypeArg>),

    /// Function types are defined by their inputs and output.
    Function(FunctionType),

    /// Type variables and arbitrary types are similar, but different.
    /// Type variables are generic (can be instantiated). Arbitrary types are fixed/concrete.
    /// They do share the same namespace; you shouldn't have type variables and arbitrary types
    /// inside the same type that have the same name.
    ///
    /// For example, in:
    ///
    /// ```acorn
    /// theorem reverse_twice[T](list: List[T]) {
    ///     // Imagine some proof here.
    ///     list.reverse.reverse = list
    /// }
    /// ```
    ///
    /// To an external user of this theorem, T is a type variable. You can apply it to any type.
    /// To use this theorem, we need to instantiate T to a concrete type, like Nat or Int.
    ///
    /// To the internal proof, T is an arbitrary type. It's fixed for the duration of the proof.
    /// To prove this theorem, we *don't* need to instantiate T to a specific concrete type.
    ///
    /// A type variable represents an unknown type, possibly belonging to a particular typeclass.
    /// Expressions with type variables can be instantiated to particular types.
    Variable(TypeParam),

    /// An arbitrary type represents a type that is (optionally) a fixed instance of a typeclass,
    /// but we don't know anything else about it.
    Arbitrary(TypeParam),

    /// The type of types (kind *). Used when denormalizing type variables.
    /// This appears as the "type" of a type variable in forall quantifiers.
    Type0,

    /// A typeclass constraint as a kind. Used when denormalizing constrained type variables.
    /// For example, a type variable T: Ring would have this as its kind.
    TypeclassConstraint(Typeclass),
}

impl AcornType {
    pub fn new_datatype_application(datatype: Datatype, args: Vec<DependentTypeArg>) -> AcornType {
        if args
            .iter()
            .all(|arg| matches!(arg, DependentTypeArg::Type(_)))
        {
            return AcornType::Data(
                datatype,
                args.into_iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => acorn_type,
                        DependentTypeArg::Value(_) => unreachable!(),
                    })
                    .collect(),
            );
        }
        AcornType::Family(datatype, args)
    }

    fn dependent_args_to_str(args: &[DependentTypeArg]) -> String {
        let mut result = String::new();
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&arg.to_string());
        }
        result
    }

    /// Collects all type variables used in this type into the provided HashMap.
    /// The HashMap keys are the variable names.
    /// Returns an error if a type variable name is used with different typeclasses.
    pub fn find_type_vars(
        &self,
        vars: &mut HashMap<String, TypeParam>,
        source: &dyn ErrorContext,
    ) -> Result<()> {
        match self {
            AcornType::Variable(param) => {
                if let Some(existing) = vars.get(&param.name) {
                    // Check if the typeclasses match
                    if existing.typeclass != param.typeclass {
                        return Err(source.error(&format!(
                            "Type variable '{}' used with two different typeclasses: {:?} and {:?}",
                            param.name, existing.typeclass, param.typeclass
                        )));
                    }
                } else {
                    vars.insert(param.name.clone(), param.clone());
                }
            }
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    arg_type.find_type_vars(vars, source)?;
                }
                function_type.return_type.find_type_vars(vars, source)?;
            }
            AcornType::Data(_, params) => {
                for param in params {
                    param.find_type_vars(vars, source)?;
                }
            }
            AcornType::Family(_, args) => {
                for arg in args {
                    match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            acorn_type.find_type_vars(vars, source)?
                        }
                        DependentTypeArg::Value(value) => {
                            value.get_type().find_type_vars(vars, source)?
                        }
                    }
                }
            }
            // Built-in scalar types and Arbitrary types don't contain type variables
            _ => {}
        }
        Ok(())
    }

    /// This just checks exact equality, without any generic stuff.
    pub fn check_eq(&self, expected: Option<&AcornType>, source: &dyn ErrorContext) -> Result<()> {
        if let Some(e) = expected {
            if e != self {
                return Err(source.error(&format!("expected type {}, but this is {}", e, self)));
            }
        }
        Ok(())
    }

    pub fn check_instance(&self, datatype: &Datatype, source: &dyn ErrorContext) -> Result<()> {
        match self {
            AcornType::Data(c, _) | AcornType::Family(c, _) => {
                if c != datatype {
                    return Err(source.error(&format!(
                        "expected type {} to be an instance of {}",
                        self, datatype.name
                    )));
                }
                Ok(())
            }

            _ => Err(source.error(&format!(
                "expected type {} to be an instance of {}",
                self, datatype.name
            ))),
        }
    }

    /// Create the type, in non-curried form, for a function with the given arguments and return type.
    /// arg_types can be empty.
    pub fn functional(arg_types: Vec<AcornType>, return_type: AcornType) -> AcornType {
        if arg_types.is_empty() {
            return_type
        } else {
            AcornType::Function(FunctionType::new(arg_types, return_type))
        }
    }

    /// Whether this type contains the given type variable within it somewhere.
    pub fn has_type_variable(&self, name: &str) -> bool {
        match self {
            AcornType::Variable(param) => param.name == name,
            AcornType::Data(_, types) => types.iter().any(|t| t.has_type_variable(name)),
            AcornType::Family(_, args) => args.iter().any(|arg| match arg {
                DependentTypeArg::Type(acorn_type) => acorn_type.has_type_variable(name),
                DependentTypeArg::Value(value) => value.has_generic(),
            }),
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    if arg_type.has_type_variable(name) {
                        return true;
                    }
                }
                function_type.return_type.has_type_variable(name)
            }
            _ => false,
        }
    }

    /// Create the type you get when you apply this type to the given type.
    /// Panics if the application is invalid.
    /// Does partial application.
    pub fn apply(&self, arg_type: &AcornType) -> AcornType {
        if let AcornType::Function(function_type) = self {
            assert_eq!(function_type.arg_types[0], *arg_type);
            function_type.applied_type(1)
        } else {
            panic!("Can't apply {:?} to {:?}", self, arg_type);
        }
    }

    /// Converts a list of types to a string representation.
    fn types_to_str(types: &[AcornType]) -> String {
        let mut result = String::new();
        for (i, acorn_type) in types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("{}", acorn_type));
        }
        result
    }

    /// Converts a list of declaration types to a string representation.
    /// Uses "T" prefix for type-level types (Type0, TypeclassConstraint)
    /// and "x" prefix for value-level types.
    pub fn decs_to_str(dec_types: &[AcornType], stack_size: usize) -> String {
        let mut result = String::new();
        for (i, dec_type) in dec_types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            let prefix = if matches!(
                dec_type,
                AcornType::Type0 | AcornType::TypeclassConstraint(_)
            ) {
                "T"
            } else {
                "x"
            };
            result.push_str(&format!("{}{}: {}", prefix, i + stack_size, dec_type));
        }
        result
    }

    /// Replaces type variables in the provided list with the corresponding type.
    /// Note that this does not check if typeclasses match.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornType {
        match self {
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                for (param_name, param_type) in params {
                    if &param.name == param_name {
                        return param_type.clone();
                    }
                }
                self.clone()
            }
            AcornType::Function(function_type) => AcornType::functional(
                function_type
                    .arg_types
                    .iter()
                    .map(|t| t.instantiate(params))
                    .collect(),
                function_type.return_type.instantiate(params),
            ),
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types.iter().map(|t| t.instantiate(params)).collect(),
            ),
            AcornType::Family(datatype, args) => AcornType::Family(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.instantiate(params))
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.instantiate(params))
                        }
                    })
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    pub fn bind_value_params(&self, values: &[AcornValue]) -> AcornType {
        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.bind_value_params(values))
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.clone().bind_values(0, 0, values))
                        }
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => AcornType::functional(
                function_type
                    .arg_types
                    .iter()
                    .map(|t| t.bind_value_params(values))
                    .collect(),
                function_type.return_type.bind_value_params(values),
            ),
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types.iter().map(|t| t.bind_value_params(values)).collect(),
            ),
            _ => self.clone(),
        }
    }

    /// Change the arbitrary types in this list of parameters to generic ones.
    pub fn genericize(&self, params: &[TypeParam]) -> AcornType {
        match self {
            AcornType::Arbitrary(param) => {
                for p in params {
                    if p.name == param.name {
                        return AcornType::Variable(p.clone());
                    }
                }
                self.clone()
            }
            AcornType::Function(ftype) => AcornType::functional(
                ftype
                    .arg_types
                    .iter()
                    .map(|t| t.genericize(params))
                    .collect(),
                ftype.return_type.genericize(params),
            ),
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types.iter().map(|t| t.genericize(params)).collect(),
            ),
            AcornType::Family(datatype, args) => AcornType::Family(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.genericize(params))
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.genericize(params))
                        }
                    })
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    /// A type is generic if it has any type variables within it.
    pub fn has_generic(&self) -> bool {
        match self {
            AcornType::Bool
            | AcornType::Arbitrary(..)
            | AcornType::Type0
            | AcornType::TypeclassConstraint(_) => false,
            AcornType::Variable(..) => true,
            AcornType::Data(_, types) => types.iter().any(|t| t.has_generic()),
            AcornType::Family(_, args) => args.iter().any(|arg| match arg {
                DependentTypeArg::Type(acorn_type) => acorn_type.has_generic(),
                DependentTypeArg::Value(value) => value.has_generic(),
            }),
            AcornType::Function(ftype) => {
                for arg_type in &ftype.arg_types {
                    if arg_type.has_generic() {
                        return true;
                    }
                }
                ftype.return_type.has_generic()
            }
        }
    }

    /// Converts all type variables to arbitrary types.
    pub fn to_arbitrary(&self) -> AcornType {
        match self {
            AcornType::Variable(param) => AcornType::Arbitrary(param.clone()),
            AcornType::Function(ftype) => AcornType::functional(
                ftype.arg_types.iter().map(|t| t.to_arbitrary()).collect(),
                ftype.return_type.to_arbitrary(),
            ),
            AcornType::Data(datatype, params) => AcornType::Data(
                datatype.clone(),
                params.iter().map(|t| t.to_arbitrary()).collect(),
            ),
            AcornType::Family(datatype, args) => AcornType::Family(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.to_arbitrary())
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.to_arbitrary())
                        }
                    })
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    /// Checks if this type contains any arbitrary types.
    pub fn has_arbitrary(&self) -> bool {
        match self {
            AcornType::Arbitrary(..) => true,
            AcornType::Function(ftype) => ftype.has_arbitrary(),
            AcornType::Data(_, params) => params.iter().any(|t| t.has_arbitrary()),
            AcornType::Family(_, args) => args.iter().any(|arg| match arg {
                DependentTypeArg::Type(acorn_type) => acorn_type.has_arbitrary(),
                DependentTypeArg::Value(value) => value.has_arbitrary(),
            }),
            _ => false,
        }
    }

    /// Collects all Arbitrary type parameters from this type.
    pub fn collect_arbitrary_params(&self, params: &mut Vec<TypeParam>) {
        match self {
            AcornType::Arbitrary(param) => {
                if !params.iter().any(|p| p.name == param.name) {
                    params.push(param.clone());
                }
            }
            AcornType::Function(ftype) => {
                for arg_type in &ftype.arg_types {
                    arg_type.collect_arbitrary_params(params);
                }
                ftype.return_type.collect_arbitrary_params(params);
            }
            AcornType::Data(_, type_params) => {
                for t in type_params {
                    t.collect_arbitrary_params(params);
                }
            }
            AcornType::Family(_, args) => {
                for arg in args {
                    match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            acorn_type.collect_arbitrary_params(params)
                        }
                        DependentTypeArg::Value(value) => {
                            value.get_type().collect_arbitrary_params(params)
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Converts all Arbitrary types to Variable types.
    pub fn arbitrary_to_variable(&self) -> AcornType {
        match self {
            AcornType::Arbitrary(param) => AcornType::Variable(param.clone()),
            AcornType::Function(ftype) => AcornType::functional(
                ftype
                    .arg_types
                    .iter()
                    .map(|t| t.arbitrary_to_variable())
                    .collect(),
                ftype.return_type.arbitrary_to_variable(),
            ),
            AcornType::Data(dt, params) => AcornType::Data(
                dt.clone(),
                params.iter().map(|t| t.arbitrary_to_variable()).collect(),
            ),
            AcornType::Family(dt, args) => AcornType::Family(
                dt.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.arbitrary_to_variable())
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.arbitrary_to_variable())
                        }
                    })
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    /// Replaces occurrences of a specific datatype with a type Variable.
    /// Used to abstract over a concrete type to get the generic form.
    pub fn abstract_over_datatype(&self, datatype: &Datatype, param: TypeParam) -> AcornType {
        match self {
            AcornType::Data(dt, params) if dt == datatype && params.is_empty() => {
                AcornType::Variable(param)
            }
            AcornType::Data(dt, params) => AcornType::Data(
                dt.clone(),
                params
                    .iter()
                    .map(|t| t.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
            ),
            AcornType::Family(dt, args) => AcornType::Family(
                dt.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => DependentTypeArg::Type(
                            acorn_type.abstract_over_datatype(datatype, param.clone()),
                        ),
                        DependentTypeArg::Value(value) => DependentTypeArg::Value(
                            value.abstract_over_datatype(datatype, param.clone()),
                        ),
                    })
                    .collect(),
            ),
            AcornType::Function(ftype) => AcornType::functional(
                ftype
                    .arg_types
                    .iter()
                    .map(|t| t.abstract_over_datatype(datatype, param.clone()))
                    .collect(),
                ftype.return_type.abstract_over_datatype(datatype, param),
            ),
            _ => self.clone(),
        }
    }

    /// Returns whether this type contains a specific arbitrary type parameter.
    pub fn has_arbitrary_type_param(&self, param: &TypeParam) -> bool {
        match self {
            AcornType::Arbitrary(p) => p == param,
            AcornType::Function(ftype) => {
                ftype
                    .arg_types
                    .iter()
                    .any(|t| t.has_arbitrary_type_param(param))
                    || ftype.return_type.has_arbitrary_type_param(param)
            }
            AcornType::Data(_, params) => params.iter().any(|t| t.has_arbitrary_type_param(param)),
            AcornType::Family(_, args) => args.iter().any(|arg| match arg {
                DependentTypeArg::Type(acorn_type) => acorn_type.has_arbitrary_type_param(param),
                DependentTypeArg::Value(value) => value.has_arbitrary_type_param(param),
            }),
            _ => false,
        }
    }

    /// Returns whether this type contains a specific type parameter (as a Variable or Arbitrary).
    /// This checks recursively, including nested type parameters inside Data and Function types.
    pub fn contains_type_var(&self, param: &TypeParam) -> bool {
        match self {
            AcornType::Variable(p) | AcornType::Arbitrary(p) => p == param,
            AcornType::Data(_, type_args) => type_args.iter().any(|t| t.contains_type_var(param)),
            AcornType::Family(_, args) => args.iter().any(|arg| match arg {
                DependentTypeArg::Type(acorn_type) => acorn_type.contains_type_var(param),
                DependentTypeArg::Value(value) => value.contains_type_var(param),
            }),
            AcornType::Function(ftype) => {
                ftype.arg_types.iter().any(|t| t.contains_type_var(param))
                    || ftype.return_type.contains_type_var(param)
            }
            _ => false,
        }
    }

    /// Computes the variance of a type parameter in this type.
    /// The `positive` parameter tracks whether we're in a positive or negative position.
    /// The `variance_lookup` function provides variance information for nested datatypes.
    pub fn compute_variance_with_lookup<'a, F>(
        &self,
        param: &TypeParam,
        positive: bool,
        variance_lookup: &F,
    ) -> Variance
    where
        F: Fn(&Datatype) -> Option<&'a Vec<Variance>>,
    {
        match self {
            AcornType::Variable(p) | AcornType::Arbitrary(p) => {
                if p == param {
                    if positive {
                        Variance::Positive
                    } else {
                        Variance::Negative
                    }
                } else {
                    Variance::None
                }
            }
            AcornType::Data(datatype, type_args) => {
                let mut combined = Variance::None;

                // If we have variance information for this datatype, use it
                if let Some(variances) = variance_lookup(datatype) {
                    for (i, arg) in type_args.iter().enumerate() {
                        // Determine the effective polarity based on the nested datatype's variance
                        let arg_positive = if i < variances.len() {
                            match &variances[i] {
                                Variance::Negative => !positive, // Flip polarity for contravariant
                                Variance::Both => {
                                    // Invariant: param appears in both positions if it's here
                                    let variance = arg.compute_variance_with_lookup(
                                        param,
                                        true,
                                        variance_lookup,
                                    );
                                    if variance != Variance::None {
                                        combined = combined.merge(Variance::Both);
                                    }
                                    continue;
                                }
                                Variance::Positive | Variance::None => positive,
                            }
                        } else {
                            positive
                        };
                        combined = combined.merge(arg.compute_variance_with_lookup(
                            param,
                            arg_positive,
                            variance_lookup,
                        ));
                    }
                } else {
                    // No variance info available, assume covariant
                    for arg in type_args {
                        combined = combined.merge(arg.compute_variance_with_lookup(
                            param,
                            positive,
                            variance_lookup,
                        ));
                    }
                }
                combined
            }
            AcornType::Family(_, args) => {
                let mut combined = Variance::None;
                for arg in args {
                    if let DependentTypeArg::Type(acorn_type) = arg {
                        combined = combined.merge(acorn_type.compute_variance_with_lookup(
                            param,
                            positive,
                            variance_lookup,
                        ));
                    }
                }
                combined
            }
            AcornType::Function(ftype) => {
                // Function arguments are in NEGATIVE position, return is in POSITIVE position
                let mut combined = Variance::None;
                for arg_type in &ftype.arg_types {
                    combined = combined.merge(arg_type.compute_variance_with_lookup(
                        param,
                        !positive,
                        variance_lookup,
                    ));
                }
                combined = combined.merge(ftype.return_type.compute_variance_with_lookup(
                    param,
                    positive,
                    variance_lookup,
                ));
                combined
            }
            AcornType::Bool | AcornType::Type0 | AcornType::TypeclassConstraint(_) => {
                Variance::None
            }
        }
    }

    /// Computes the variance of a type parameter in this type.
    /// The `positive` parameter tracks whether we're in a positive or negative position.
    /// This version does NOT look up variance for nested datatypes.
    pub fn compute_variance(&self, param: &TypeParam, positive: bool) -> Variance {
        self.compute_variance_with_lookup(param, positive, &|_| None)
    }

    /// Returns whether this type is a function type.
    pub fn is_functional(&self) -> bool {
        matches!(self, AcornType::Function(_))
    }

    /// Returns the typeclass if this type is an abstract representative of a typeclass.
    /// This means that with this type, you can use typeclass attributes with dot syntax.
    /// Specifically, this is type variables or arbitrary types.
    pub fn as_typeclass_representative(&self) -> Option<&Typeclass> {
        match &self {
            AcornType::Variable(param) | AcornType::Arbitrary(param) => param.typeclass.as_ref(),
            _ => None,
        }
    }

    /// Extracts the datatype from this type, or errors if it is not a data type.
    pub fn get_datatype(&self, source: &dyn ErrorContext) -> error::Result<&Datatype> {
        match self {
            AcornType::Data(datatype, _) | AcornType::Family(datatype, _) => Ok(datatype),
            _ => Err(source.error("not an attributable datatype")),
        }
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "Bool"),
            AcornType::Data(datatype, params) => {
                write!(f, "{}", datatype.name)?;
                if !params.is_empty() {
                    write!(f, "[{}]", AcornType::types_to_str(params))?;
                }
                Ok(())
            }
            AcornType::Family(datatype, args) => {
                write!(f, "{}", datatype.name)?;
                if !args.is_empty() {
                    write!(f, "[{}]", AcornType::dependent_args_to_str(args))?;
                }
                Ok(())
            }
            AcornType::Function(function_type) => write!(f, "{}", function_type),
            AcornType::Variable(param) => {
                // A type variable has a name that is generally hidden from the user.
                // You can't use these in explicit code, so this won't be used for codegen.
                // So just print out the typeclass name.
                match &param.typeclass {
                    Some(tc) => write!(f, "{}", tc.name),
                    None => write!(f, "{}*", param.name),
                }
            }
            AcornType::Arbitrary(param) => {
                // An arbitrary type will look to the user just like an opaque type.
                // So it's okay to print out only its name.
                write!(f, "{}", param.name)?;
                Ok(())
            }
            AcornType::Type0 => write!(f, "Type0"),
            AcornType::TypeclassConstraint(tc) => write!(f, "{}", tc.name),
        }
    }
}
