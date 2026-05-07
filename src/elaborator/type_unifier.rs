use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, Datatype, TypeParam, Typeclass};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::unresolved_constant::UnresolvedConstant;
use crate::kernel::atom::AtomId;
use crate::module::ModuleId;

/// Utility for matching types during unification.
pub struct TypeUnifier<'a> {
    /// The registry tells us which classes are instances of which typeclasses,
    /// and which typeclasses have an extension relationship.
    registry: &'a dyn TypeclassRegistry,

    /// Type unification fills in a mapping for any parametric types that need to be specified,
    /// in order to make it match.
    /// Every parameter used in self will get a mapping entry.
    pub mapping: HashMap<String, AcornType>,

    /// Dependent value argument unification fills this in for hidden family/value parameters.
    pub value_mapping: HashMap<AtomId, AcornValue>,
}

/// The different errors we can get from unification.
pub enum Error {
    /// Unification failed, because this datatype is not an instance of this typeclass.
    Datatype(Datatype, Typeclass),

    /// Unification failed becaue the first typeclass is not an extension of the second.
    /// TypeclassFailure(A, B) indicates that A does not extend B.
    /// This is directional. Field extends Ring, but not vice versa.
    Typeclass(Typeclass, Typeclass),

    /// Unification failed for some other reason.
    Other,
}

/// The unifier itself does not know which typeclasses correspond to what.
/// The registry is responsible for that.
pub trait TypeclassRegistry {
    /// Returns whether the class is an instance of the typeclass.
    fn is_instance_of(&self, class: &Datatype, typeclass: &Typeclass) -> bool;

    /// Returns whether the full type is an instance of the typeclass.
    fn is_instance_of_type(&self, ty: &AcornType, typeclass: &Typeclass) -> bool {
        match ty {
            AcornType::Data(datatype, params) if params.is_empty() => {
                self.is_instance_of(datatype, typeclass)
            }
            _ => false,
        }
    }

    /// Returns whether typeclass extends base.
    /// In particular, this returns false when typeclass == base.
    fn extends(&self, typeclass: &Typeclass, base: &Typeclass) -> bool;

    /// Returns whether this type has the attributes defined on the given entity.
    /// The entity name can be either a class or typeclass.
    fn inherits_attributes(&self, t: &AcornType, module_id: ModuleId, entity_name: &str) -> bool {
        match t {
            AcornType::Data(dt, _) => dt.module_id == module_id && dt.name == entity_name,
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                let Some(param_tc) = &param.typeclass else {
                    return false;
                };
                if param_tc.module_id == module_id && param_tc.name == entity_name {
                    return true;
                }
                let typeclass = Typeclass {
                    module_id,
                    name: entity_name.to_string(),
                };
                self.extends(param_tc, &typeclass)
            }
            _ => false,
        }
    }
}

pub type Result = std::result::Result<(), Error>;

fn require_eq(t1: &AcornType, t2: &AcornType) -> Result {
    if t1 == t2 {
        Ok(())
    } else {
        Err(Error::Other)
    }
}

impl<'a> TypeUnifier<'a> {
    pub fn new(registry: &'a dyn TypeclassRegistry) -> Self {
        TypeUnifier {
            registry,
            mapping: HashMap::new(),
            value_mapping: HashMap::new(),
        }
    }

    /// Figures out whether it is possible to instantiate self to get instance.
    ///
    /// "validator" is a function that checks whether a typeclass is valid for a given type.
    /// This is abstracted out because the prover and the elaborator have different ideas of what is valid.
    ///
    /// Returns whether it was successful.
    pub fn match_instance(
        &mut self,
        generic_type: &AcornType,
        instance_type: &AcornType,
    ) -> Result {
        match (generic_type, instance_type) {
            (AcornType::Variable(param), _) => {
                if let Some(t) = self.mapping.get(&param.name) {
                    // This type variable is already mapped
                    return require_eq(t, instance_type);
                }
                if let Some(generic_typeclass) = param.typeclass.as_ref() {
                    match instance_type {
                        AcornType::Data(dt, _) | AcornType::Family(dt, _) => {
                            if !self
                                .registry
                                .is_instance_of_type(instance_type, generic_typeclass)
                            {
                                return Err(Error::Datatype(dt.clone(), generic_typeclass.clone()));
                            }
                        }
                        AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                            match &param.typeclass {
                                Some(instance_typeclass) => {
                                    if instance_typeclass != generic_typeclass
                                        && !self
                                            .registry
                                            .extends(instance_typeclass, generic_typeclass)
                                    {
                                        return Err(Error::Typeclass(
                                            instance_typeclass.clone(),
                                            generic_typeclass.clone(),
                                        ));
                                    }
                                }
                                None => return Err(Error::Other),
                            }
                        }
                        _ => return Err(Error::Other),
                    }
                }
                // Occurs check: reject cyclic types like T = List[T]
                if instance_type.has_type_variable(&param.name) {
                    return Err(Error::Other);
                }
                self.mapping
                    .insert(param.name.clone(), instance_type.clone());
            }
            (AcornType::Arbitrary(param), _) => {
                // Arbitrary types work like Variable types for unification purposes
                if let Some(t) = self.mapping.get(&param.name) {
                    // This type parameter is already mapped
                    return require_eq(t, instance_type);
                }
                if let Some(generic_typeclass) = param.typeclass.as_ref() {
                    match instance_type {
                        AcornType::Data(dt, _) | AcornType::Family(dt, _) => {
                            if !self
                                .registry
                                .is_instance_of_type(instance_type, generic_typeclass)
                            {
                                return Err(Error::Datatype(dt.clone(), generic_typeclass.clone()));
                            }
                        }
                        AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                            match &param.typeclass {
                                Some(instance_typeclass) => {
                                    if instance_typeclass != generic_typeclass
                                        && !self
                                            .registry
                                            .extends(instance_typeclass, generic_typeclass)
                                    {
                                        return Err(Error::Typeclass(
                                            instance_typeclass.clone(),
                                            generic_typeclass.clone(),
                                        ));
                                    }
                                }
                                None => return Err(Error::Other),
                            }
                        }
                        _ => return Err(Error::Other),
                    }
                }
                // Occurs check: reject cyclic types like T = List[T]
                // But allow identity (T = T) - if instance_type is exactly Arbitrary(param)
                if instance_type.has_arbitrary_type_param(param) {
                    // Allow identity mapping: T -> Arbitrary(T) is fine, it's not cyclic
                    if let AcornType::Arbitrary(p) = instance_type {
                        if p == param {
                            // This is T = T, add to mapping so type inference knows T was inferred
                            self.mapping
                                .insert(param.name.clone(), instance_type.clone());
                            return Ok(());
                        }
                    }
                    return Err(Error::Other);
                }
                self.mapping
                    .insert(param.name.clone(), instance_type.clone());
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() < g.arg_types.len() {
                    // Generic has fewer args than instance. This can happen when:
                    // - Generic is `A -> B` where B is a type variable
                    // - Instance is `A -> (C -> D)` which un-curries to `(A, C) -> D`
                    // We should unify B with `C -> D` (the re-curried remainder).
                    for (f_arg, g_arg) in f.arg_types.iter().zip(&g.arg_types) {
                        self.match_instance(f_arg, g_arg)?;
                    }
                    // Re-curry the remaining args of g into a function type
                    let remaining_args = g.arg_types[f.arg_types.len()..].to_vec();
                    let curried_remainder =
                        AcornType::functional(remaining_args, (*g.return_type).clone());
                    self.match_instance(&f.return_type, &curried_remainder)?;
                } else if f.arg_types.len() > g.arg_types.len() {
                    // Generic has more args than instance. This can happen when:
                    // - Generic is `(A, B) -> C` (un-curried from `A -> (B -> C)`)
                    // - Instance is `A -> D` where D is a type variable
                    // We should unify `B -> C` (the re-curried remainder) with D.
                    for (f_arg, g_arg) in f.arg_types.iter().zip(&g.arg_types) {
                        self.match_instance(f_arg, g_arg)?;
                    }
                    // Re-curry the remaining args of f into a function type
                    let remaining_args = f.arg_types[g.arg_types.len()..].to_vec();
                    let curried_remainder =
                        AcornType::functional(remaining_args, (*f.return_type).clone());
                    self.match_instance(&curried_remainder, &g.return_type)?;
                } else {
                    // Same number of args
                    self.match_instance(&f.return_type, &g.return_type)?;
                    for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                        self.match_instance(f_arg_type, g_arg_type)?;
                    }
                }
            }
            (AcornType::Data(g_class, g_params), AcornType::Data(i_class, i_params)) => {
                if g_class != i_class || g_params.len() != i_params.len() {
                    return Err(Error::Other);
                }
                for (g_param, i_param) in g_params.iter().zip(i_params) {
                    self.match_instance(g_param, i_param)?;
                }
            }
            (AcornType::Family(g_class, g_args), AcornType::Family(i_class, i_args)) => {
                if g_class != i_class || g_args.len() != i_args.len() {
                    return Err(Error::Other);
                }
                for (g_arg, i_arg) in g_args.iter().zip(i_args) {
                    self.match_dependent_arg(g_arg, i_arg)?;
                }
            }
            _ => return require_eq(generic_type, instance_type),
        }
        Ok(())
    }

    fn match_dependent_arg(
        &mut self,
        generic_arg: &crate::elaborator::acorn_type::DependentTypeArg,
        instance_arg: &crate::elaborator::acorn_type::DependentTypeArg,
    ) -> Result {
        match (generic_arg, instance_arg) {
            (
                crate::elaborator::acorn_type::DependentTypeArg::Type(generic_type),
                crate::elaborator::acorn_type::DependentTypeArg::Type(instance_type),
            ) => self.match_instance(generic_type, instance_type),
            (
                crate::elaborator::acorn_type::DependentTypeArg::Value(generic_value),
                crate::elaborator::acorn_type::DependentTypeArg::Value(instance_value),
            ) => match generic_value {
                AcornValue::Variable(index, generic_type) => {
                    self.match_instance(generic_type, &instance_value.get_type())?;
                    if let Some(existing) = self.value_mapping.get(index) {
                        if existing == instance_value {
                            Ok(())
                        } else {
                            Err(Error::Other)
                        }
                    } else {
                        self.value_mapping.insert(*index, instance_value.clone());
                        Ok(())
                    }
                }
                _ if generic_value == instance_value => Ok(()),
                _ => Err(Error::Other),
            },
            _ => Err(Error::Other),
        }
    }

    fn satisfies_typeclass_constraint(&self, ty: &AcornType, typeclass: &Typeclass) -> bool {
        match ty {
            AcornType::Data(_, _) | AcornType::Family(_, _) => {
                self.registry.is_instance_of_type(ty, typeclass)
            }
            AcornType::Arbitrary(param) | AcornType::Variable(param) => {
                let Some(actual) = &param.typeclass else {
                    return false;
                };
                actual == typeclass || self.registry.extends(actual, typeclass)
            }
            _ => false,
        }
    }

    pub fn check_type_param_constraints(
        &self,
        params: &[TypeParam],
        args: &[AcornType],
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        for (param, arg) in params.iter().zip(args) {
            let Some(typeclass) = &param.typeclass else {
                continue;
            };
            if !self.satisfies_typeclass_constraint(arg, typeclass) {
                return Err(source.error(&format!(
                    "type parameter '{}' expected an instance of '{}', but got '{}'",
                    param.name, typeclass.name, arg
                )));
            }
        }
        Ok(())
    }

    /// Runs match_instance but wraps it with a human-readable error message when it fails.
    pub fn user_match_instance(
        &mut self,
        generic: &AcornType,
        instance: &AcornType,
        what: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        if !self.match_instance(generic, instance).is_ok() {
            return Err(source.error(&format!(
                "{} has type {} but we expected some sort of {}",
                what, instance, generic
            )));
        }
        Ok(())
    }

    /// Infer the type of an unresolved constant, based on its arguments (if it is a function)
    /// and the expected type.
    /// Returns a value that applies the function to the arguments.
    /// If the type cannot be inferred, returns an error.
    pub fn resolve_with_inference(
        &mut self,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_return_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        let potential =
            self.try_resolve_with_inference(unresolved, args, expected_return_type, source)?;

        match potential {
            PotentialValue::Resolved(value) => Ok(value),
            PotentialValue::Unresolved(_) => Err(source.error(
                "The arguments are insufficient to infer the type of this function. \
                Try making its parameters explicit",
            )),
        }
    }

    /// Try to resolve with inference, allowing partial resolution.
    /// If all type parameters can be inferred, returns a resolved value.
    /// If some cannot be inferred, returns an unresolved value with args accumulated.
    /// This method never "partially resolves". It either fully resolves the type, or just adds
    /// arguments to the unresolved constant.
    pub fn try_resolve_with_inference(
        &mut self,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_return_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let original_mapping = self.mapping.clone();
        let original_value_mapping = self.value_mapping.clone();
        let explicit_result = self.try_resolve_with_inference_inner(
            unresolved.clone(),
            args.clone(),
            expected_return_type,
            source,
            false,
        );
        match explicit_result {
            Ok(result) => return Ok(result),
            Err(explicit_error) => {
                if unresolved.value_param_types.is_empty() {
                    return Err(explicit_error);
                }
                self.mapping = original_mapping;
                self.value_mapping = original_value_mapping;
                match self.try_resolve_with_inference_inner(
                    unresolved,
                    args,
                    expected_return_type,
                    source,
                    true,
                ) {
                    Ok(result) => Ok(result),
                    Err(_) => Err(explicit_error),
                }
            }
        }
    }

    fn visible_value_param_prefix_len(unresolved: &UnresolvedConstant) -> usize {
        let AcornType::Function(function_type) = &unresolved.generic_type else {
            return 0;
        };
        let value_param_count = unresolved.value_param_types.len();
        if function_type.arg_types.len() < value_param_count {
            return 0;
        }
        let generic_value_param_types = unresolved
            .value_param_types
            .iter()
            .map(|value_type| value_type.genericize(&unresolved.params))
            .collect::<Vec<_>>();
        if function_type.arg_types[..value_param_count] != *generic_value_param_types {
            return 0;
        }
        value_param_count
    }

    fn inferred_value_args(
        &self,
        unresolved: &UnresolvedConstant,
        type_args: &[AcornType],
        source: &dyn ErrorContext,
    ) -> error::Result<Option<Vec<AcornValue>>> {
        if !unresolved.bound_value_args.is_empty() || unresolved.value_param_types.is_empty() {
            return Ok(None);
        }

        let type_replacements = unresolved
            .params
            .iter()
            .zip(type_args.iter())
            .map(|(param, arg)| (param.name.clone(), arg.clone()))
            .collect::<Vec<_>>();
        let mut value_args = Vec::with_capacity(unresolved.value_param_types.len());
        for (i, value_type) in unresolved.value_param_types.iter().enumerate() {
            let Some(value_arg) = self.value_mapping.get(&(i as AtomId)).cloned() else {
                return Err(source.error(
                    "The arguments are insufficient to infer the dependent value parameters",
                ));
            };
            let expected_type = value_type
                .instantiate(&type_replacements)
                .bind_value_params(&value_args);
            value_arg.check_type(Some(&expected_type), source)?;
            value_args.push(value_arg);
        }
        Ok(Some(value_args))
    }

    fn try_resolve_with_inference_inner(
        &mut self,
        unresolved: UnresolvedConstant,
        args: Vec<AcornValue>,
        expected_return_type: Option<&AcornType>,
        source: &dyn ErrorContext,
        infer_hidden_value_args: bool,
    ) -> error::Result<PotentialValue> {
        // Combine stored args with new args for type inference
        let combined_args = [unresolved.args.clone(), args].concat();
        let hidden_arg_prefix = if infer_hidden_value_args {
            Self::visible_value_param_prefix_len(&unresolved)
        } else {
            0
        };

        // Use the arguments to infer types
        let unresolved_return_type = if combined_args.is_empty() && hidden_arg_prefix == 0 {
            unresolved.generic_type.clone()
        } else if let AcornType::Function(unresolved_function_type) = &unresolved.generic_type {
            for (i, arg) in combined_args.iter().enumerate() {
                let arg_type: &AcornType = match &unresolved_function_type.arg_types.get(i) {
                    Some(t) => t,
                    None => {
                        return Err(source.error(&format!(
                            "expected {} arguments but got {}",
                            unresolved_function_type.arg_types.len(),
                            combined_args.len()
                        )));
                    }
                };
                let arg_type = if hidden_arg_prefix > 0 {
                    match unresolved_function_type
                        .arg_types
                        .get(hidden_arg_prefix + i)
                    {
                        Some(t) => t,
                        None => {
                            return Err(source.error(&format!(
                                "expected {} arguments but got {}",
                                unresolved_function_type.arg_types.len() - hidden_arg_prefix,
                                combined_args.len()
                            )));
                        }
                    }
                } else {
                    arg_type
                };
                self.user_match_instance(
                    arg_type,
                    &arg.get_type(),
                    &format!("argument {}", i),
                    source,
                )?;
            }

            unresolved_function_type.applied_type(hidden_arg_prefix + combined_args.len())
        } else {
            return Err(source.error("expected a function type"));
        };

        if let Some(target_type) = expected_return_type {
            // Use the expected type to infer types
            self.user_match_instance(&unresolved_return_type, target_type, "return value", source)?;
        }

        // Determine which parameters have been inferred and which haven't
        let mut all_params = vec![];
        let mut uninferred_params = vec![];

        for param in &unresolved.params {
            match self.mapping.get(&param.name) {
                Some(t) => {
                    // Check if the inferred type is actually concrete.
                    // If it's a Variable, it's not really resolved - it's just
                    // unified with another type parameter from a different context.
                    if t.has_generic() {
                        // The mapped type contains type variables, so this param
                        // is not truly inferred to a concrete type yet.
                        all_params.push(t.clone());
                        uninferred_params.push(param.clone());
                    } else {
                        // Parameter was inferred to a concrete type
                        all_params.push(t.clone());
                    }
                }
                None => {
                    // Parameter not inferred - keep as type variable
                    all_params.push(AcornType::Variable(param.clone()));
                    uninferred_params.push(param.clone());
                }
            }
        }

        self.check_type_param_constraints(&unresolved.params, &all_params, source)?;
        let inferred_value_args = if infer_hidden_value_args {
            self.inferred_value_args(&unresolved, &all_params, source)?
        } else {
            None
        };

        if uninferred_params.is_empty() {
            // All parameters inferred - fully resolve
            // Create unresolved without stored args to avoid double-application
            let unresolved_without_args = UnresolvedConstant {
                name: unresolved.name,
                params: unresolved.params,
                generic_type: unresolved.generic_type,
                value_param_types: unresolved.value_param_types,
                bound_value_args: unresolved.bound_value_args,
                args: vec![], // Don't apply args in resolve(), we'll apply combined_args here
            };
            let mut instance_fn = unresolved_without_args.resolve(source, all_params)?;
            if let Some(value_args) = inferred_value_args {
                instance_fn = instance_fn.bind_value_params(&value_args, source)?;
            }
            let value = AcornValue::apply(instance_fn, combined_args);
            value.check_type(expected_return_type, source)?;
            Ok(PotentialValue::Resolved(value))
        } else {
            // We could not infer all parameters.
            // We don't partially infer, here. We just append the new arguments.
            // Later we will use them to fully infer.
            let unresolved_partial = UnresolvedConstant {
                name: unresolved.name.clone(),
                params: unresolved.params.clone(),
                generic_type: unresolved.generic_type.clone(),
                value_param_types: unresolved.value_param_types.clone(),
                bound_value_args: inferred_value_args.unwrap_or(unresolved.bound_value_args),
                args: combined_args,
            };

            Ok(PotentialValue::Unresolved(unresolved_partial))
        }
    }

    /// If we have an expected type and this is still a potential value, resolve it.
    pub fn maybe_resolve_value(
        &mut self,
        potential: PotentialValue,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let expected_type = match expected_type {
            Some(t) => t,
            None => return Ok(potential),
        };
        let uc = match potential {
            PotentialValue::Unresolved(uc) => uc,
            p => return Ok(p),
        };
        let value = self.resolve_with_inference(uc, vec![], Some(expected_type), source)?;
        Ok(PotentialValue::Resolved(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborator::acorn_type::{DependentTypeArg, TypeParam};

    /// A dummy registry that says nothing is an instance of anything.
    struct DummyRegistry;

    impl TypeclassRegistry for DummyRegistry {
        fn is_instance_of(&self, _class: &Datatype, _typeclass: &Typeclass) -> bool {
            false
        }

        fn extends(&self, _typeclass: &Typeclass, _base: &Typeclass) -> bool {
            false
        }
    }

    /// Test that the unifier rejects cyclic type mappings (occurs check).
    ///
    /// Unifying T with List[T] should fail because it would create an
    /// infinite type T = List[List[List[...]]].
    #[test]
    fn test_occurs_check_rejects_cyclic_type() {
        let registry = DummyRegistry;
        let mut unifier = TypeUnifier::new(&registry);

        // Create type variable T
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let t = AcornType::Variable(t_param);

        // Create List[T] datatype
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_t = AcornType::Data(list_datatype, vec![t.clone()]);

        // Try to unify T with List[T] - should fail due to occurs check
        let result = unifier.match_instance(&t, &list_t);
        assert!(result.is_err(), "Unifying T with List[T] should fail");

        // The mapping should not have been created
        assert!(
            unifier.mapping.get("T").is_none(),
            "No mapping should be created for cyclic unification"
        );
    }

    /// Test that the occurs check also works for Arbitrary types.
    #[test]
    fn test_occurs_check_arbitrary_type() {
        let registry = DummyRegistry;
        let mut unifier = TypeUnifier::new(&registry);

        // Create arbitrary type T
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let t = AcornType::Arbitrary(t_param.clone());

        // Create List[T] datatype where T is also Arbitrary
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_t = AcornType::Data(list_datatype, vec![AcornType::Arbitrary(t_param)]);

        // Try to unify T with List[T] - should fail due to occurs check
        let result = unifier.match_instance(&t, &list_t);
        assert!(result.is_err(), "Unifying T with List[T] should fail");
    }

    /// Test that Variable can unify with a type containing Arbitrary of same name.
    /// This is NOT cyclic because Variable and Arbitrary are semantically different.
    #[test]
    fn test_variable_can_unify_with_arbitrary_same_name() {
        let registry = DummyRegistry;
        let mut unifier = TypeUnifier::new(&registry);

        // Create type variable T (generic)
        let t_var = AcornType::Variable(TypeParam {
            name: "T".to_string(),
            typeclass: None,
        });

        // Create Pair[T, U] where T and U are Arbitrary (fixed)
        let pair_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Pair".to_string(),
        };
        let t_arb = AcornType::Arbitrary(TypeParam {
            name: "T".to_string(),
            typeclass: None,
        });
        let u_arb = AcornType::Arbitrary(TypeParam {
            name: "U".to_string(),
            typeclass: None,
        });
        let pair_tu = AcornType::Data(pair_datatype, vec![t_arb.clone(), u_arb]);

        // Unifying Variable(T) with Pair[Arbitrary(T), Arbitrary(U)] should succeed
        // because Variable and Arbitrary are different - this isn't cyclic
        let result = unifier.match_instance(&t_var, &pair_tu);
        assert!(
            result.is_ok(),
            "Variable(T) should unify with Pair[Arbitrary(T), U]"
        );
        assert_eq!(unifier.mapping.get("T"), Some(&pair_tu));
    }

    /// Test that valid (non-cyclic) unifications still work.
    #[test]
    fn test_valid_unification_still_works() {
        let registry = DummyRegistry;
        let mut unifier = TypeUnifier::new(&registry);

        // Create type variable T
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let t = AcornType::Variable(t_param);

        // Unify T with Bool - this should succeed
        let result = unifier.match_instance(&t, &AcornType::Bool);
        assert!(result.is_ok(), "Unifying T with Bool should succeed");
        assert_eq!(unifier.mapping.get("T"), Some(&AcornType::Bool));
    }

    #[test]
    fn test_dependent_value_arg_type_uses_type_mapping() {
        let registry = DummyRegistry;
        let mut unifier = TypeUnifier::new(&registry);
        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: None,
        };
        let generic_t = AcornType::Variable(t_param.clone());
        let instance_t = AcornType::Arbitrary(t_param.clone());
        let generic_set_t = AcornType::Data(set_datatype.clone(), vec![generic_t.clone()]);
        let instance_set_t = AcornType::Data(set_datatype, vec![instance_t.clone()]);
        let generic_value = AcornValue::Variable(0, generic_set_t);
        let instance_value = AcornValue::Variable(0, instance_set_t);
        let generic_subspace = AcornType::Family(
            subspace_datatype.clone(),
            vec![
                DependentTypeArg::Type(generic_t),
                DependentTypeArg::Value(generic_value),
            ],
        );
        let instance_subspace = AcornType::Family(
            subspace_datatype,
            vec![
                DependentTypeArg::Type(instance_t.clone()),
                DependentTypeArg::Value(instance_value),
            ],
        );

        let result = unifier.match_instance(&generic_subspace, &instance_subspace);
        assert!(
            result.is_ok(),
            "dependent value argument type should use the mapped type parameter"
        );
        assert_eq!(unifier.mapping.get("T"), Some(&instance_t));
    }
}
