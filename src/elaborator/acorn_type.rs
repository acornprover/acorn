use std::{collections::HashMap, fmt};

use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::error::{self, ErrorContext, Result};
use crate::kernel::atom::AtomId;
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
    pub fn as_unresolved(&self) -> Option<&UnresolvedType> {
        match self {
            PotentialType::Unresolved(ut) => Some(ut),
            PotentialType::Resolved(_) => None,
        }
    }

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
            // Normalize function types by un-currying. The nested function type was represented
            // under its own visible binders first, followed by these outer visible arguments.
            // After flattening, the outer arguments are the leading visible binders.
            let outer_arg_count = arg_types.len() as AtomId;
            let nested_arg_count = ftype.arg_types.len() as AtomId;
            let nested_args = ftype
                .arg_types
                .into_iter()
                .enumerate()
                .map(|(i, arg_type)| {
                    arg_type.move_ambient_after_visible(0, i as AtomId, outer_arg_count)
                });
            let combined_args = arg_types.into_iter().chain(nested_args).collect();
            let return_type = (*ftype.return_type).move_ambient_after_visible(
                0,
                nested_arg_count,
                outer_arg_count,
            );
            FunctionType {
                arg_types: combined_args,
                return_type: Box::new(return_type),
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

    pub fn canonical_kinds(params: &[FamilyParam]) -> Vec<FamilyParamKind> {
        let mut answer = vec![];
        let mut replacements = vec![];
        let mut next_type_index = 0;
        for param in params {
            match param {
                FamilyParam::Type(type_param) => {
                    answer.push(FamilyParamKind::Type(type_param.typeclass.clone()));
                    replacements.push((
                        type_param.name.clone(),
                        AcornType::Arbitrary(TypeParam {
                            name: format!("T{}", next_type_index),
                            typeclass: type_param.typeclass.clone(),
                        }),
                    ));
                    next_type_index += 1;
                }
                FamilyParam::Value(value_param) => {
                    answer.push(FamilyParamKind::Value(
                        value_param.value_type.instantiate(&replacements),
                    ));
                }
            }
        }
        answer
    }
}

/// An ordered list of type and value parameters.
///
/// Later value-parameter types are interpreted in the scope of earlier parameters.
/// This wraps the existing `FamilyParam` representation so call sites can keep
/// source order as the source of truth while still getting cheap split views
/// for older APIs that need type params and value params separately.
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Telescope {
    params: Vec<FamilyParam>,
    type_params: Vec<TypeParam>,
    value_params: Vec<ValueParam>,
}

impl Telescope {
    pub fn new(params: Vec<FamilyParam>) -> Telescope {
        let type_params = params
            .iter()
            .filter_map(|param| param.as_type_param().cloned())
            .collect();
        let value_params = params
            .iter()
            .filter_map(|param| param.as_value_param().cloned())
            .collect();
        Telescope {
            params,
            type_params,
            value_params,
        }
    }

    pub fn empty() -> Telescope {
        Telescope::default()
    }

    pub fn params(&self) -> &[FamilyParam] {
        &self.params
    }

    pub fn type_params(&self) -> &[TypeParam] {
        &self.type_params
    }

    pub fn value_params(&self) -> &[ValueParam] {
        &self.value_params
    }

    pub fn into_params(self) -> Vec<FamilyParam> {
        self.params
    }

    pub fn len(&self) -> usize {
        self.params.len()
    }

    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, FamilyParam> {
        self.params.iter()
    }

    pub fn canonical_kinds(&self) -> Vec<FamilyParamKind> {
        FamilyParam::canonical_kinds(&self.params)
    }

    pub fn value_param_types(&self) -> Vec<AcornType> {
        self.value_params
            .iter()
            .map(|param| param.value_type.clone())
            .collect()
    }

    pub fn value_block_args(&self) -> Vec<(String, AcornType)> {
        self.value_params
            .iter()
            .map(|param| (param.name.clone(), param.value_type.clone()))
            .collect()
    }

    pub fn family_args_for_type_args(
        &self,
        type_args: &[AcornType],
    ) -> (Vec<DependentTypeArg>, Vec<AcornValue>) {
        let mut next_type_arg = 0usize;
        let mut next_value_arg = 0usize;
        let mut value_args = vec![];
        let family_args = self
            .params
            .iter()
            .map(|param| match param {
                FamilyParam::Type(_) => {
                    let arg = DependentTypeArg::Type(type_args[next_type_arg].clone());
                    next_type_arg += 1;
                    arg
                }
                FamilyParam::Value(value_param) => {
                    let value = AcornValue::Variable(
                        next_value_arg as AtomId,
                        value_param.value_type.clone(),
                    );
                    next_value_arg += 1;
                    value_args.push(value.clone());
                    DependentTypeArg::Value(value)
                }
            })
            .collect();
        assert_eq!(next_type_arg, type_args.len());
        (family_args, value_args)
    }
}

impl IntoIterator for Telescope {
    type Item = FamilyParam;
    type IntoIter = std::vec::IntoIter<FamilyParam>;

    fn into_iter(self) -> Self::IntoIter {
        self.params.into_iter()
    }
}

impl<'a> IntoIterator for &'a Telescope {
    type Item = &'a FamilyParam;
    type IntoIter = std::slice::Iter<'a, FamilyParam>;

    fn into_iter(self) -> Self::IntoIter {
        self.params.iter()
    }
}

impl From<Vec<FamilyParam>> for Telescope {
    fn from(params: Vec<FamilyParam>) -> Self {
        Telescope::new(params)
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

/// A typeclass instance target, possibly quantified over datatype family parameters.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct TypeclassInstance {
    pub instance_type: AcornType,
    pub datatype: Datatype,
    pub family_params: Telescope,
    pub typeclass: Typeclass,
}

impl TypeclassInstance {
    pub fn type_params(&self) -> &[TypeParam] {
        self.family_params.type_params()
    }

    pub fn value_params(&self) -> &[ValueParam] {
        self.family_params.value_params()
    }

    pub fn is_concrete(&self) -> bool {
        self.family_params.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::ModuleId;

    #[test]
    fn telescope_preserves_family_order_while_exposing_split_views() {
        let t = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let u = TypeParam {
            name: "U".to_string(),
            typeclass: None,
        };
        let n = ValueParam {
            name: "n".to_string(),
            value_type: AcornType::Bool,
        };
        let telescope = Telescope::new(vec![
            FamilyParam::Type(t.clone()),
            FamilyParam::Value(n.clone()),
            FamilyParam::Type(u.clone()),
        ]);

        assert_eq!(telescope.type_params(), &[t.clone(), u.clone()]);
        assert_eq!(telescope.value_params(), std::slice::from_ref(&n));

        let type_args = vec![AcornType::Arbitrary(t.clone()), AcornType::Arbitrary(u)];
        let (family_args, value_args) = telescope.family_args_for_type_args(&type_args);

        assert_eq!(
            family_args,
            vec![
                DependentTypeArg::Type(AcornType::Arbitrary(t)),
                DependentTypeArg::Value(AcornValue::Variable(0, AcornType::Bool)),
                DependentTypeArg::Type(type_args[1].clone()),
            ]
        );
        assert_eq!(value_args, vec![AcornValue::Variable(0, AcornType::Bool)]);
    }

    #[test]
    fn promoted_ambient_prefix_rotates_nested_function_type_refs() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let set_t = AcornType::Data(set_datatype, vec![t_type.clone()]);
        let subspace_t_a = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type.clone()),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
            ],
        );
        let scoped_body_type = AcornType::functional_from_flat_context(
            vec![subspace_t_a.clone(), t_type.clone()],
            subspace_t_a.clone(),
        );

        let promoted =
            AcornType::functional_from_promoted_ambient(vec![set_t.clone()], scoped_body_type);

        let expected =
            AcornType::functional(vec![set_t, subspace_t_a.clone(), t_type], subspace_t_a);
        assert_eq!(promoted, expected);
    }

    #[test]
    fn uncurrying_preserves_outer_visible_arg_refs() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let set_t = AcornType::Data(set_datatype, vec![t_type.clone()]);
        let subspace_t_a = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type.clone()),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
            ],
        );
        let curried_return_type = AcornType::functional_from_flat_context(
            vec![subspace_t_a.clone(), t_type.clone()],
            subspace_t_a.clone(),
        );

        let flattened = AcornType::functional(vec![set_t.clone()], curried_return_type);

        let expected =
            AcornType::functional(vec![set_t, subspace_t_a.clone(), t_type], subspace_t_a);
        assert_eq!(flattened, expected);
    }

    #[test]
    fn insert_stack_enters_function_type_visible_scope() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let u_param = TypeParam {
            name: "U".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let u_type = AcornType::Variable(u_param);
        let set_t = AcornType::Data(set_datatype, vec![t_type.clone()]);
        let subspace_t_a = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type.clone()),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
            ],
        );
        let function_type = AcornType::functional_from_flat_context(
            vec![subspace_t_a.clone(), u_type.clone()],
            subspace_t_a,
        );

        let inserted = function_type.insert_stack(2, 1);

        assert_eq!(inserted, function_type);
    }

    #[test]
    fn bind_value_params_enters_function_type_visible_scope() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let u_param = TypeParam {
            name: "U".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let u_type = AcornType::Variable(u_param);
        let set_t = AcornType::Data(set_datatype, vec![t_type.clone()]);
        let a_const = AcornValue::constant(
            crate::elaborator::names::ConstantName::unqualified(ModuleId(0), "a"),
            vec![],
            set_t.clone(),
            set_t.clone(),
            vec![],
            vec![],
        );
        let subspace_t_a = AcornType::Family(
            subspace_datatype.clone(),
            vec![
                DependentTypeArg::Type(t_type.clone()),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
            ],
        );
        let function_type = AcornType::functional_from_flat_context(
            vec![subspace_t_a, u_type.clone()],
            AcornType::Family(
                subspace_datatype.clone(),
                vec![
                    DependentTypeArg::Type(t_type.clone()),
                    DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
                ],
            ),
        );
        let subspace_t_a_const = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type),
                DependentTypeArg::Value(a_const.clone()),
            ],
        );
        let expected = AcornType::functional_from_flat_context(
            vec![subspace_t_a_const.clone(), u_type],
            subspace_t_a_const,
        );

        let bound = function_type.bind_value_params(&[a_const]);

        assert_eq!(bound, expected);
    }

    #[test]
    fn bind_ambient_values_preserves_visible_function_arg_refs() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let set_t = AcornType::Data(set_datatype.clone(), vec![t_type.clone()]);
        let subspace_t_a = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
            ],
        );
        let function_type = AcornType::functional(
            vec![
                set_t.clone(),
                AcornType::Data(set_datatype, vec![subspace_t_a]),
                set_t.clone(),
            ],
            AcornType::Bool,
        );
        let replacement = AcornValue::constant(
            crate::elaborator::names::ConstantName::unqualified(ModuleId(0), "v"),
            vec![],
            set_t.clone(),
            set_t,
            vec![],
            vec![],
        );

        let bound = function_type.bind_ambient_values(0, 1, &[replacement]);

        assert_eq!(bound, function_type);
    }

    #[test]
    fn function_to_scoped_context_restores_source_telescope_order() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let u_param = TypeParam {
            name: "U".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let u_type = AcornType::Variable(u_param);
        let set_t = AcornType::Data(set_datatype, vec![t_type.clone()]);
        let subspace_t_a = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t)),
            ],
        );
        let canonical = AcornType::functional_from_scoped_context(
            vec![u_type.clone()],
            subspace_t_a.clone(),
            1,
        );
        let expected_source_view = AcornType::functional(vec![u_type], subspace_t_a);

        let source_view = canonical.function_to_scoped_context(1);

        assert_eq!(source_view, expected_source_view);
    }

    #[test]
    fn function_to_scoped_context_recurses_into_function_argument_type() {
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let u_param = TypeParam {
            name: "U".to_string(),
            typeclass: None,
        };
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_type = AcornType::Variable(t_param);
        let u_type = AcornType::Variable(u_param);
        let set_t = AcornType::Data(set_datatype, vec![t_type.clone()]);
        let subspace_t_a = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(t_type.clone()),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t)),
            ],
        );
        let nested_function_type = AcornType::functional_from_scoped_context(
            vec![u_type.clone()],
            subspace_t_a.clone(),
            1,
        );
        let canonical = AcornType::functional_from_scoped_context(
            vec![nested_function_type],
            subspace_t_a.clone(),
            1,
        );
        let expected_source_view = AcornType::functional(
            vec![AcornType::functional(vec![u_type], subspace_t_a.clone())],
            subspace_t_a,
        );

        let source_view = canonical.function_to_scoped_context(1);

        assert_eq!(source_view, expected_source_view);
    }
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
                let mut message = format!("expected type {}, but this is {}", e, self);
                if self.could_transport_to(e) {
                    message.push_str(
                        "\n\nif these indexed types are equivalent, explicitly transport the value. For example:\n",
                    );
                    message.push_str(&format!(
                        "let foo: {} = ...\nlet bar: {} = transport foo\nthen use bar where the expected type is required",
                        self, e
                    ));
                }
                return Err(source.error(&message));
            }
        }
        Ok(())
    }

    fn dependent_args_allow_transport(
        source_args: &[DependentTypeArg],
        target_args: &[DependentTypeArg],
    ) -> bool {
        if source_args.len() != target_args.len() {
            return false;
        }
        source_args
            .iter()
            .zip(target_args)
            .all(|(source_arg, target_arg)| match (source_arg, target_arg) {
                (DependentTypeArg::Type(source_type), DependentTypeArg::Type(target_type)) => {
                    source_type == target_type
                }
                (DependentTypeArg::Value(source_value), DependentTypeArg::Value(target_value)) => {
                    source_value.get_type() == target_value.get_type()
                }
                _ => false,
            })
    }

    fn could_transport_to(&self, target: &AcornType) -> bool {
        if self == target {
            return true;
        }
        match (self, target) {
            (AcornType::Function(source_fn), AcornType::Function(target_fn)) => {
                source_fn.arg_types.len() == target_fn.arg_types.len()
                    && source_fn
                        .arg_types
                        .iter()
                        .zip(&target_fn.arg_types)
                        .all(|(source_arg, target_arg)| source_arg.could_transport_to(target_arg))
                    && source_fn
                        .return_type
                        .could_transport_to(&target_fn.return_type)
            }
            (
                AcornType::Family(source_datatype, source_args),
                AcornType::Family(target_datatype, target_args),
            ) => {
                source_datatype == target_datatype
                    && AcornType::dependent_args_allow_transport(source_args, target_args)
            }
            _ => false,
        }
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

    /// Creates a function type from components evaluated in the same ambient value-stack context.
    ///
    /// The internal function representation treats each later argument and the return type as
    /// living under the previous visible argument binders. Source arrow syntax and datatype
    /// member declarations evaluate those component types before those visible binders exist, so
    /// ambient value references must be shifted under the visible binders here.
    pub fn functional_from_flat_context(
        arg_types: Vec<AcornType>,
        return_type: AcornType,
    ) -> AcornType {
        let shifted_args = arg_types
            .into_iter()
            .enumerate()
            .map(|(i, arg_type)| arg_type.insert_stack(0, i as AtomId))
            .collect::<Vec<_>>();
        let shifted_return = return_type.insert_stack(0, shifted_args.len() as AtomId);
        AcornType::functional(shifted_args, shifted_return)
    }

    /// Creates a function type from components evaluated in a normal source value scope.
    ///
    /// Source scopes put ambient datatype-family value parameters before the visible function
    /// arguments. The internal function representation puts each visible function argument before
    /// those ambient parameters in later argument and return types. This rotates only that ambient
    /// prefix; references to earlier visible arguments stay attached to those arguments.
    pub fn functional_from_scoped_context(
        arg_types: Vec<AcornType>,
        return_type: AcornType,
        ambient_stack_size: AtomId,
    ) -> AcornType {
        if ambient_stack_size == 0 {
            return AcornType::functional(arg_types, return_type);
        }

        let shifted_args = arg_types
            .into_iter()
            .enumerate()
            .map(|(i, arg_type)| {
                arg_type.move_ambient_after_visible(0, ambient_stack_size, i as AtomId)
            })
            .collect::<Vec<_>>();
        let shifted_return = return_type.move_ambient_after_visible(
            0,
            ambient_stack_size,
            shifted_args.len() as AtomId,
        );
        AcornType::functional(shifted_args, shifted_return)
    }

    /// Converts an internal function type back into the source-scoped view used by declarations.
    ///
    /// Internally, visible function binders are placed before the ambient source-scope prefix in
    /// later argument and return types. Source declaration syntax names the ambient prefix first,
    /// so code generation must rotate that prefix back before printing argument declarations.
    pub fn function_to_scoped_context(&self, ambient_stack_size: AtomId) -> AcornType {
        let AcornType::Function(function_type) = self else {
            return self.clone();
        };

        let arg_types = function_type
            .arg_types
            .iter()
            .enumerate()
            .map(|(i, arg_type)| {
                arg_type
                    .move_ambient_after_visible(0, i as AtomId, ambient_stack_size)
                    .function_to_scoped_context(ambient_stack_size + i as AtomId)
            })
            .collect();
        let arg_count = function_type.arg_types.len() as AtomId;
        let return_type = function_type
            .return_type
            .move_ambient_after_visible(0, arg_count, ambient_stack_size)
            .function_to_scoped_context(ambient_stack_size + arg_count);
        AcornType::Function(FunctionType {
            arg_types,
            return_type: Box::new(return_type),
        })
    }

    /// Creates a function type by promoting ambient value parameters to visible leading arguments.
    ///
    /// The body type was evaluated in a source scope where these value parameters were ambient.
    /// If the body is already a function type, its later argument and return types have those
    /// ambient references after the body's visible binders. Once the ambient values become leading
    /// visible arguments, rotate those references back before the body's visible binders.
    pub fn functional_from_promoted_ambient(
        prefix_arg_types: Vec<AcornType>,
        scoped_body_type: AcornType,
    ) -> AcornType {
        let ambient_count = prefix_arg_types.len() as AtomId;
        if ambient_count == 0 {
            return scoped_body_type;
        }

        let AcornType::Function(function_type) = scoped_body_type else {
            return AcornType::functional(prefix_arg_types, scoped_body_type);
        };

        let mut arg_types = prefix_arg_types;
        let body_arg_count = function_type.arg_types.len() as AtomId;
        arg_types.extend(
            function_type
                .arg_types
                .into_iter()
                .enumerate()
                .map(|(i, arg_type)| {
                    arg_type.move_ambient_after_visible(0, i as AtomId, ambient_count)
                }),
        );
        let return_type = (*function_type.return_type).move_ambient_after_visible(
            0,
            body_arg_count,
            ambient_count,
        );
        AcornType::functional(arg_types, return_type)
    }

    pub(crate) fn move_ambient_after_visible(
        &self,
        base: AtomId,
        ambient_count: AtomId,
        visible_count: AtomId,
    ) -> AcornType {
        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.move_ambient_after_visible(
                                base,
                                ambient_count,
                                visible_count,
                            ))
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.clone().move_ambient_after_visible(
                                base,
                                ambient_count,
                                visible_count,
                            ))
                        }
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => {
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .enumerate()
                    .map(|(i, t)| {
                        t.move_ambient_after_visible(
                            base + i as AtomId,
                            ambient_count,
                            visible_count,
                        )
                    })
                    .collect();
                AcornType::functional(
                    arg_types,
                    function_type.return_type.move_ambient_after_visible(
                        base + function_type.arg_types.len() as AtomId,
                        ambient_count,
                        visible_count,
                    ),
                )
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| t.move_ambient_after_visible(base, ambient_count, visible_count))
                    .collect(),
            ),
            _ => self.clone(),
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
            let scoped_type = dec_type.function_to_scoped_context((i + stack_size) as AtomId);
            result.push_str(&format!("{}{}: {}", prefix, i + stack_size, scoped_type));
        }
        result
    }

    pub(crate) fn instantiate_with_base_stack(
        &self,
        stack_size: AtomId,
        base_stack_size: AtomId,
        params: &[(String, AcornType)],
    ) -> AcornType {
        match self {
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                for (param_name, param_type) in params {
                    if &param.name == param_name {
                        assert!(stack_size >= base_stack_size);
                        return param_type
                            .clone()
                            .insert_stack(base_stack_size, stack_size - base_stack_size);
                    }
                }
                self.clone()
            }
            AcornType::Function(function_type) => {
                let mut current_stack_size = stack_size;
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .map(|t| {
                        let instantiated = t.instantiate_with_base_stack(
                            current_stack_size,
                            base_stack_size,
                            params,
                        );
                        current_stack_size += 1;
                        instantiated
                    })
                    .collect();
                AcornType::functional(
                    arg_types,
                    function_type.return_type.instantiate_with_base_stack(
                        current_stack_size,
                        base_stack_size,
                        params,
                    ),
                )
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| t.instantiate_with_base_stack(stack_size, base_stack_size, params))
                    .collect(),
            ),
            AcornType::Family(datatype, args) => AcornType::Family(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.instantiate_with_base_stack(
                                stack_size,
                                base_stack_size,
                                params,
                            ))
                        }
                        DependentTypeArg::Value(value) => DependentTypeArg::Value(
                            value.instantiate_with_base_stack(stack_size, base_stack_size, params),
                        ),
                    })
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    pub(crate) fn instantiate_with_stack(
        &self,
        stack_size: AtomId,
        params: &[(String, AcornType)],
    ) -> AcornType {
        self.instantiate_with_base_stack(stack_size, 0, params)
    }

    /// Replaces type variables in the provided list with the corresponding type.
    /// Note that this does not check if typeclasses match.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> AcornType {
        self.instantiate_with_stack(0, params)
    }

    fn bind_value_params_with_stack(&self, stack_size: AtomId, values: &[AcornValue]) -> AcornType {
        fn bind_value_at_stack(
            value: &AcornValue,
            stack_size: AtomId,
            values: &[AcornValue],
        ) -> AcornValue {
            let shifted_values: Vec<_> = values
                .iter()
                .cloned()
                .map(|value| value.insert_stack(0, stack_size))
                .collect();
            value
                .clone()
                .bind_values(stack_size, stack_size, &shifted_values)
        }

        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => DependentTypeArg::Type(
                            acorn_type.bind_value_params_with_stack(stack_size, values),
                        ),
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(bind_value_at_stack(value, stack_size, values))
                        }
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => {
                let mut current_stack_size = stack_size;
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .map(|t| {
                        let bound = t.bind_value_params_with_stack(current_stack_size, values);
                        current_stack_size += 1;
                        bound
                    })
                    .collect();
                AcornType::functional(
                    arg_types,
                    function_type
                        .return_type
                        .bind_value_params_with_stack(current_stack_size, values),
                )
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| t.bind_value_params_with_stack(stack_size, values))
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    pub fn bind_value_params(&self, values: &[AcornValue]) -> AcornType {
        self.bind_value_params_with_stack(0, values)
    }

    pub fn bind_values(
        &self,
        first_binding_index: AtomId,
        stack_size: AtomId,
        values: &[AcornValue],
    ) -> AcornType {
        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => DependentTypeArg::Type(
                            acorn_type.bind_values(first_binding_index, stack_size, values),
                        ),
                        DependentTypeArg::Value(value) => DependentTypeArg::Value(
                            value
                                .clone()
                                .bind_values(first_binding_index, stack_size, values),
                        ),
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => {
                let mut current_stack_size = stack_size;
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .map(|t| {
                        let bound = t.bind_values(first_binding_index, current_stack_size, values);
                        current_stack_size += 1;
                        bound
                    })
                    .collect();
                AcornType::functional(
                    arg_types,
                    function_type.return_type.bind_values(
                        first_binding_index,
                        current_stack_size,
                        values,
                    ),
                )
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| t.bind_values(first_binding_index, stack_size, values))
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    /// Binds values from the surrounding stack inside a type annotation.
    ///
    /// This differs from `bind_values` for function types: visible function
    /// arguments are inserted before ambient stack entries in later argument
    /// and return types, so the ambient binding range has to shift under them.
    pub fn bind_ambient_values(
        &self,
        first_binding_index: AtomId,
        stack_size: AtomId,
        values: &[AcornValue],
    ) -> AcornType {
        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => DependentTypeArg::Type(
                            acorn_type.bind_ambient_values(first_binding_index, stack_size, values),
                        ),
                        DependentTypeArg::Value(value) => DependentTypeArg::Value(
                            value
                                .clone()
                                .bind_values(first_binding_index, stack_size, values),
                        ),
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => {
                let mut current_stack_size = stack_size;
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .enumerate()
                    .map(|(i, t)| {
                        let visible_args = i as AtomId;
                        let bound = t.bind_ambient_values(
                            first_binding_index + visible_args,
                            current_stack_size,
                            values,
                        );
                        current_stack_size += 1;
                        bound
                    })
                    .collect();
                AcornType::functional(
                    arg_types,
                    function_type.return_type.bind_ambient_values(
                        first_binding_index + function_type.arg_types.len() as AtomId,
                        current_stack_size,
                        values,
                    ),
                )
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| t.bind_ambient_values(first_binding_index, stack_size, values))
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    pub fn insert_stack(&self, index: AtomId, increment: AtomId) -> AcornType {
        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.insert_stack(index, increment))
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.clone().insert_stack(index, increment))
                        }
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => {
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .enumerate()
                    .map(|(i, t)| t.insert_stack(index + i as AtomId, increment))
                    .collect();
                AcornType::Function(FunctionType {
                    arg_types,
                    return_type: Box::new(
                        function_type.return_type.insert_stack(
                            index + function_type.arg_types.len() as AtomId,
                            increment,
                        ),
                    ),
                })
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| t.insert_stack(index, increment))
                    .collect(),
            ),
            _ => self.clone(),
        }
    }

    pub fn replace_constants(
        &self,
        stack_size: AtomId,
        replacer: &impl Fn(&crate::elaborator::acorn_value::ConstantInstance) -> Option<AcornValue>,
    ) -> AcornType {
        self.replace_constants_with_base_stack(stack_size, 0, replacer)
    }

    pub(crate) fn replace_constants_with_base_stack(
        &self,
        stack_size: AtomId,
        base_stack_size: AtomId,
        replacer: &impl Fn(&crate::elaborator::acorn_value::ConstantInstance) -> Option<AcornValue>,
    ) -> AcornType {
        assert!(stack_size >= base_stack_size);
        match self {
            AcornType::Family(datatype, args) => AcornType::new_datatype_application(
                datatype.clone(),
                args.iter()
                    .map(|arg| match arg {
                        DependentTypeArg::Type(acorn_type) => {
                            DependentTypeArg::Type(acorn_type.replace_constants_with_base_stack(
                                stack_size,
                                base_stack_size,
                                replacer,
                            ))
                        }
                        DependentTypeArg::Value(value) => {
                            DependentTypeArg::Value(value.replace_constants_with_base_stack(
                                stack_size,
                                base_stack_size,
                                replacer,
                            ))
                        }
                    })
                    .collect(),
            ),
            AcornType::Function(function_type) => {
                let mut current_stack_size = stack_size;
                let arg_types = function_type
                    .arg_types
                    .iter()
                    .map(|t| {
                        let replaced = t.replace_constants_with_base_stack(
                            current_stack_size,
                            base_stack_size,
                            replacer,
                        );
                        current_stack_size += 1;
                        replaced
                    })
                    .collect();
                AcornType::functional(
                    arg_types,
                    function_type.return_type.replace_constants_with_base_stack(
                        current_stack_size,
                        base_stack_size,
                        replacer,
                    ),
                )
            }
            AcornType::Data(datatype, types) => AcornType::Data(
                datatype.clone(),
                types
                    .iter()
                    .map(|t| {
                        t.replace_constants_with_base_stack(stack_size, base_stack_size, replacer)
                    })
                    .collect(),
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
