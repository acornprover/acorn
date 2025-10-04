use std::{collections::HashMap, fmt};

use crate::compilation::{self, ErrorSource, Result};
use crate::module::ModuleId;

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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct UnresolvedType {
    /// The underlying generic datatype.
    pub datatype: Datatype,

    /// The parameters we need to instantiate this type, along with their typeclass if any.
    pub params: Vec<Option<Typeclass>>,
}

impl UnresolvedType {
    /// Just sticks fake names in there to print.
    pub fn to_display_type(&self) -> AcornType {
        let mut params = vec![];
        for (i, param) in self.params.iter().enumerate() {
            params.push(AcornType::Variable(TypeParam {
                name: format!("T{}", i),
                typeclass: param.clone(),
            }));
        }
        AcornType::Data(self.datatype.clone(), params)
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
    /// Resolves the type given the parameters.
    /// Every replacement must be a type variable being replaced with an arbitrary type.
    pub fn invertible_resolve(
        self,
        params: Vec<AcornType>,
        source: &dyn ErrorSource,
    ) -> Result<AcornType> {
        if let PotentialType::Unresolved(ut) = &self {
            if ut.params.len() != params.len() {
                return Err(source.error(&format!(
                    "type {} expects {} parameters, but got {}",
                    ut.datatype.name,
                    ut.params.len(),
                    params.len()
                )));
            }
            for (i, (typeclass, param_type)) in ut.params.iter().zip(params.iter()).enumerate() {
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
        self.resolve(params, source)
    }

    /// Resolves the type given the parameters.
    /// Reports an error if the parameters don't match what we expected.
    pub fn resolve(self, params: Vec<AcornType>, source: &dyn ErrorSource) -> Result<AcornType> {
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
                        ut.datatype.name,
                        ut.params.len(),
                        params.len()
                    )))
                } else {
                    // TODO: check that params obeys ut's typeclasses
                    Ok(AcornType::Data(ut.datatype, params))
                }
            }
        }
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
            PotentialType::Unresolved(ut) => Some(&ut.datatype),
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
        write!(f, "{} -> {}", lhs, self.return_type)
    }
}

impl FunctionType {
    /// Creates a new function type by normalizing arguments and return type.
    fn new(arg_types: Vec<AcornType>, return_type: AcornType) -> FunctionType {
        assert!(arg_types.len() > 0);
        if let AcornType::Function(ftype) = return_type {
            // Normalize function types by un-currying.
            let combined_args = arg_types
                .into_iter()
                .chain(ftype.arg_types.into_iter())
                .collect();
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

/// Every AcornValue has an AcornType.
/// This is the "richer" form of a type. The environment uses these types; the prover uses ids.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum AcornType {
    /// Nothing can ever be the empty type.
    Empty,

    /// Booleans are special
    Bool,

    /// Data types are structures, inductive types, or axiomatic types.
    /// They have a datatype, and may have type parameters.
    Data(Datatype, Vec<AcornType>),

    /// Function types are defined by their inputs and output.
    Function(FunctionType),

    /// Type variables and arbitrary types are similar, but different.
    /// Type variables are not monomorphic. Arbitrary types are monomorphic.
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
    /// To prove this theorem, we *don't* need to instantiate T to a monomorphic type.
    ///
    /// A type variable represents an unknown type, possibly belonging to a particular typeclass.
    /// Expressions with type variables can be instantiated to particular types.
    Variable(TypeParam),

    /// An arbitrary type represents a type that is (optionally) a fixed instance of a typeclass,
    /// but we don't know anything else about it.
    Arbitrary(TypeParam),
}

impl AcornType {
    /// Collects all type variables used in this type into the provided HashMap.
    /// The HashMap keys are the variable names.
    /// Returns an error if a type variable name is used with different typeclasses.
    pub fn find_type_vars(
        &self,
        vars: &mut HashMap<String, TypeParam>,
        source: &dyn ErrorSource,
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
            // Empty, Bool, and Arbitrary types don't contain type variables
            _ => {}
        }
        Ok(())
    }

    /// This just checks exact equality, without any generic stuff.
    pub fn check_eq(&self, expected: Option<&AcornType>, source: &dyn ErrorSource) -> Result<()> {
        if let Some(e) = expected {
            if e != self {
                return Err(source.error(&format!("expected type {}, but this is {}", e, self)));
            }
        }
        Ok(())
    }

    pub fn check_instance(&self, datatype: &Datatype, source: &dyn ErrorSource) -> Result<()> {
        match self {
            AcornType::Data(c, _) => {
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
    pub fn decs_to_str(dec_types: &Vec<AcornType>, stack_size: usize) -> String {
        let mut result = String::new();
        for (i, dec_type) in dec_types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("x{}: {}", i + stack_size, dec_type));
        }
        result
    }

    /// Replaces type variables in the provided list with the corresponding type.
    /// Note that this does not check if typeclasses match.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornType {
        match self {
            AcornType::Variable(param) => {
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
            _ => self.clone(),
        }
    }

    /// A type is generic if it has any type variables within it.
    pub fn has_generic(&self) -> bool {
        match self {
            AcornType::Bool | AcornType::Empty | AcornType::Arbitrary(..) => false,
            AcornType::Variable(..) => true,
            AcornType::Data(_, types) => types.iter().any(|t| t.has_generic()),
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
            _ => self.clone(),
        }
    }

    /// Checks if this type contains any arbitrary types.
    pub fn has_arbitrary(&self) -> bool {
        match self {
            AcornType::Arbitrary(..) => true,
            AcornType::Function(ftype) => ftype.has_arbitrary(),
            AcornType::Data(_, params) => params.iter().any(|t| t.has_arbitrary()),
            _ => false,
        }
    }

    /// Returns whether this type is a function type.
    pub fn is_functional(&self) -> bool {
        match self {
            AcornType::Function(_) => true,
            _ => false,
        }
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
    pub fn get_datatype(&self, source: &dyn ErrorSource) -> compilation::Result<&Datatype> {
        match self {
            AcornType::Data(datatype, _) => Ok(datatype),
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
            AcornType::Function(function_type) => write!(f, "{}", function_type),
            AcornType::Empty => write!(f, "empty"),
            AcornType::Variable(param) => {
                // A type variable has a name that is generally hidden from the user.
                // You can't use these in explicit code, so this won't be used for codegen.
                // So just print out the typeclass name.
                let nice_tc = match &param.typeclass {
                    Some(tc) => &tc.name,
                    None => "*",
                };
                write!(f, "{}", nice_tc)?;
                Ok(())
            }
            AcornType::Arbitrary(param) => {
                // An arbitrary type will look to the user just like an opaque type.
                // So it's okay to print out only its name.
                write!(f, "{}", param.name)?;
                Ok(())
            }
        }
    }
}
