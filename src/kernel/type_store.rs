use std::collections::HashMap as StdHashMap;
use std::collections::HashSet as StdHashSet;

use im::HashMap as ImHashMap;
use im::Vector as ImVector;

use crate::elaborator::acorn_type::{AcornType, Datatype, FunctionType, TypeParam, Typeclass};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::kernel::types::{GroundTypeId, TypeclassId};
use crate::module::ModuleId;

/// Manages ground type registration and typeclass relationships.
#[derive(Clone)]
pub struct TypeStore {
    /// ground_id_to_type[module_id][local_id] is the AcornType for that ground type.
    /// Only ground types are stored here.
    /// Uses im::Vector for O(1) clones.
    ground_id_to_type: ImVector<ImVector<AcornType>>,

    /// ground_id_to_arity[module_id][local_id] is the number of type parameters for that type.
    /// For proper types like Bool, arity is 0.
    /// For type constructors like List, arity is 1.
    ground_id_to_arity: ImVector<ImVector<u8>>,

    /// Maps Datatype (bare data type with no params) to its GroundTypeId.
    datatype_to_ground_id: ImHashMap<Datatype, GroundTypeId>,

    /// Maps Arbitrary type parameters to their GroundTypeId.
    arbitrary_to_ground_id: ImHashMap<TypeParam, GroundTypeId>,

    /// typeclass_to_id[typeclass] is the TypeclassId
    typeclass_to_id: ImHashMap<Typeclass, TypeclassId>,

    /// id_to_typeclass[module_id][local_id] is the Typeclass
    /// Uses im::Vector for O(1) clones.
    id_to_typeclass: ImVector<ImVector<Typeclass>>,

    /// typeclass_extends[module_id][local_id] is the set of TypeclassIds that this typeclass extends.
    /// This is the transitive closure, so if A extends B and B extends C, then A's set contains both B and C.
    typeclass_extends: ImVector<ImVector<StdHashSet<TypeclassId>>>,

    /// typeclass_instances[module_id][local_id] is the set of GroundTypeIds that are instances of this typeclass.
    typeclass_instances: ImVector<ImVector<StdHashSet<GroundTypeId>>>,
}

impl TypeStore {
    pub fn new() -> TypeStore {
        // Empty, Bool, and TypeSort are now Symbol variants, not GroundTypeIds.
        // No pre-registration needed.
        TypeStore {
            ground_id_to_type: ImVector::new(),
            ground_id_to_arity: ImVector::new(),
            datatype_to_ground_id: ImHashMap::new(),
            arbitrary_to_ground_id: ImHashMap::new(),
            typeclass_to_id: ImHashMap::new(),
            id_to_typeclass: ImVector::new(),
            typeclass_extends: ImVector::new(),
            typeclass_instances: ImVector::new(),
        }
    }

    /// Ensures the vector has an entry for the given module_id, extending with empty vectors if needed.
    fn ensure_ground_module(&mut self, module_id: ModuleId) {
        let idx = module_id.get() as usize;
        while self.ground_id_to_type.len() <= idx {
            self.ground_id_to_type.push_back(ImVector::new());
        }
        while self.ground_id_to_arity.len() <= idx {
            self.ground_id_to_arity.push_back(ImVector::new());
        }
    }

    /// Ensures the vector has an entry for the given module_id for typeclass storage.
    fn ensure_typeclass_module(&mut self, module_id: ModuleId) {
        let idx = module_id.get() as usize;
        while self.id_to_typeclass.len() <= idx {
            self.id_to_typeclass.push_back(ImVector::new());
        }
        while self.typeclass_extends.len() <= idx {
            self.typeclass_extends.push_back(ImVector::new());
        }
        while self.typeclass_instances.len() <= idx {
            self.typeclass_instances.push_back(ImVector::new());
        }
    }

    /// Register a type in the type store. Call this before using to_type_term()
    /// to ensure ground types are registered.
    pub fn add_type(&mut self, acorn_type: &AcornType) {
        self.add_type_internal(acorn_type);
    }

    /// Internal implementation that registers ground types.
    /// Only user-defined ground types (bare Data types, Arbitrary) get GroundTypeIds.
    /// Empty, Bool, and TypeSort are Symbol variants, not GroundTypeIds.
    /// Non-ground types (Function, parameterized Data) are just recursively processed.
    fn add_type_internal(&mut self, acorn_type: &AcornType) {
        match acorn_type {
            // Empty and Bool are now Symbol variants, no registration needed
            AcornType::Empty | AcornType::Bool => {}

            // Bare data type: assign a new GroundTypeId
            AcornType::Data(datatype, params) if params.is_empty() => {
                if self.datatype_to_ground_id.contains_key(datatype) {
                    return; // Already registered
                }
                let module_id = datatype.module_id;
                let ground_id = self.next_ground_id(module_id);
                self.ensure_ground_module(module_id);
                let idx = module_id.get() as usize;
                self.ground_id_to_type[idx].push_back(acorn_type.clone());
                self.ground_id_to_arity[idx].push_back(0); // Default arity 0, will be updated by set_datatype_arity
                self.datatype_to_ground_id
                    .insert(datatype.clone(), ground_id);
            }

            // Parameterized data type: ensure bare constructor exists, then process params
            AcornType::Data(datatype, params) => {
                let bare_constructor = AcornType::Data(datatype.clone(), vec![]);
                self.add_type_internal(&bare_constructor);
                // Update arity if we see a parameterized version
                // This handles cases where we first see List (arity 0) then List[Int] (arity 1)
                let arity = params.len() as u8;
                if let Some(ground_id) = self.datatype_to_ground_id.get(datatype) {
                    let module_id = ground_id.module_id();
                    let local_idx = ground_id.local_id() as usize;
                    let mod_idx = module_id.get() as usize;
                    if let Some(arities) = self.ground_id_to_arity.get_mut(mod_idx) {
                        if local_idx < arities.len() && arities[local_idx] < arity {
                            arities[local_idx] = arity;
                        }
                    }
                }
                for param in params {
                    self.add_type_internal(param);
                }
            }

            // Function type: recursively process component types (no GroundTypeId needed)
            AcornType::Function(ft) => {
                for arg_type in &ft.arg_types {
                    self.add_type_internal(arg_type);
                }
                self.add_type_internal(&ft.return_type);
            }

            // Arbitrary type: assign a new GroundTypeId
            // Use module 0 for arbitrary types since they don't have a home module
            AcornType::Arbitrary(type_param) => {
                if self.arbitrary_to_ground_id.contains_key(type_param) {
                    return; // Already registered
                }
                let module_id = ModuleId(0);
                let ground_id = self.next_ground_id(module_id);
                self.ensure_ground_module(module_id);
                let idx = module_id.get() as usize;
                self.ground_id_to_type[idx].push_back(acorn_type.clone());
                self.ground_id_to_arity[idx].push_back(0); // Arbitrary types have arity 0
                self.arbitrary_to_ground_id
                    .insert(type_param.clone(), ground_id);
            }

            // Variable types are represented as FreeVariable atoms, not registered as ground types.
            // They will be converted to FreeVariable by to_type_term_with_vars.
            AcornType::Variable(_) => {}

            // Type0 and TypeclassConstraint are kind-level types, not value types.
            // They don't need registration.
            AcornType::Type0 | AcornType::TypeclassConstraint(_) => {}
        }
    }

    /// Allocate the next GroundTypeId for a given module.
    fn next_ground_id(&self, module_id: ModuleId) -> GroundTypeId {
        let idx = module_id.get() as usize;
        let local_id = self
            .ground_id_to_type
            .get(idx)
            .map(|v| v.len())
            .unwrap_or(0) as u16;
        GroundTypeId::new(module_id, local_id)
    }

    /// Get the GroundTypeId for a bare Datatype (no type parameters).
    /// Returns None if the datatype hasn't been registered.
    pub fn get_datatype_id(&self, datatype: &Datatype) -> Option<GroundTypeId> {
        self.datatype_to_ground_id.get(datatype).copied()
    }

    /// Set the arity (number of type parameters) for a datatype.
    /// This should be called after the datatype is registered and its arity is known.
    pub fn set_datatype_arity(&mut self, datatype: &Datatype, arity: u8) {
        if let Some(ground_id) = self.datatype_to_ground_id.get(datatype) {
            let module_id = ground_id.module_id();
            let local_idx = ground_id.local_id() as usize;
            let mod_idx = module_id.get() as usize;
            if let Some(arities) = self.ground_id_to_arity.get_mut(mod_idx) {
                if local_idx < arities.len() {
                    arities[local_idx] = arity;
                }
            }
        }
    }

    /// Get the arity (number of type parameters) for a ground type.
    pub fn get_arity(&self, ground_id: GroundTypeId) -> u8 {
        let mod_idx = ground_id.module_id().get() as usize;
        self.ground_id_to_arity
            .get(mod_idx)
            .and_then(|v| v.get(ground_id.local_id() as usize))
            .copied()
            .unwrap_or(0)
    }

    /// Generate the kind Term for a type constructor with the given arity.
    /// arity 0 → Type
    /// arity 1 → Type -> Type (Pi from Type to Type)
    /// arity 2 → Type -> Type -> Type
    pub fn kind_for_arity(&self, arity: u8) -> Term {
        let type_term = Term::type_sort();
        let mut result = type_term.clone();
        for _ in 0..arity {
            result = Term::pi(type_term.clone(), result);
        }
        result
    }

    /// Get the kind (type) of a ground type.
    /// Proper types like Bool have kind Type.
    /// Type constructors like List (arity 1) have kind Type -> Type.
    pub fn get_type_kind(&self, ground_id: GroundTypeId) -> Term {
        let arity = self.get_arity(ground_id);
        self.kind_for_arity(arity)
    }

    /// Look up a GroundTypeId by datatype name string.
    /// Only works for types created by `KernelContext::add_datatype` (assumes ModuleId(0)).
    #[cfg(test)]
    pub fn get_ground_id_by_name(&self, name: &str) -> Option<GroundTypeId> {
        use crate::module::ModuleId;

        let datatype = Datatype {
            module_id: ModuleId(0),
            name: name.to_string(),
        };
        self.datatype_to_ground_id.get(&datatype).copied()
    }

    /// Get the type Term for an AcornType.
    /// Ground types must be registered first via add_type().
    pub fn get_type_term(&self, acorn_type: &AcornType) -> Result<Term, String> {
        Ok(self.to_type_term(acorn_type))
    }

    /// Convert an AcornType to a type Term.
    /// Only ground types (Bool, Empty, bare data types, arbitrary types) need to be registered.
    /// Function types and parameterized data types are constructed on the fly.
    ///
    /// If `type_var_map` is provided, type variables are converted to FreeVariable atoms
    /// using the mapping. The map contains (AtomId, Term) pairs where the Term is the
    /// kind/constraint of the type variable (used elsewhere, ignored here).
    /// This is used in polymorphic mode where type variables participate
    /// in unification like term variables.
    pub fn to_type_term_with_vars(
        &self,
        acorn_type: &AcornType,
        type_var_map: Option<&StdHashMap<String, (AtomId, Term)>>,
    ) -> Term {
        match acorn_type {
            // Built-in types: use dedicated Symbol variants
            AcornType::Empty => Term::empty_type(),
            AcornType::Bool => Term::bool_type(),

            AcornType::Data(datatype, params) if params.is_empty() => {
                // Bare data type - use direct Datatype -> GroundTypeId lookup
                let ground_id = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                Term::ground_type(*ground_id)
            }

            AcornType::Data(datatype, params) => {
                // Parameterized data type: build Application using Term::type_application()
                let constructor_ground = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                let head = Term::ground_type(*constructor_ground);

                let args: Vec<Term> = params
                    .iter()
                    .map(|param| self.to_type_term_with_vars(param, type_var_map))
                    .collect();

                Term::type_application(head, args)
            }

            AcornType::Function(ft) => {
                // Function type: build nested Pi types (curried)
                let mut result = self.to_type_term_with_vars(&ft.return_type, type_var_map);

                // Build Pi types from right to left
                for arg_type in ft.arg_types.iter().rev() {
                    let arg_type_term = self.to_type_term_with_vars(arg_type, type_var_map);
                    result = Term::pi(arg_type_term, result);
                }

                result
            }

            AcornType::Variable(type_param) => {
                // Type variables become FreeVariable atoms if we have a mapping
                if let Some(map) = type_var_map {
                    if let Some((var_id, _)) = map.get(&type_param.name) {
                        return Term::atom(Atom::FreeVariable(*var_id));
                    }
                }
                panic!(
                    "Variable type {:?} not found in type_var_map. The type_var_map must include all type variables.",
                    type_param
                );
            }

            AcornType::Arbitrary(type_param) => {
                // In polymorphic mode, check if this arbitrary type corresponds to a type parameter.
                // If so, convert it to a FreeVariable just like we do for Variable types.
                // This is needed because:
                // 1. Type parameters are "pinned" as FreeVariable(0), FreeVariable(1), etc.
                // 2. Synthetic definitions use these FreeVariables for matching
                // 3. Certificate type params may be renamed (e.g., "G" -> "T0"), so we match by position
                if let Some(map) = type_var_map {
                    if let Some((var_id, _)) = map.get(&type_param.name) {
                        return Term::atom(Atom::FreeVariable(*var_id));
                    }
                }
                // Otherwise, use the registered ground type
                let ground_id = self
                    .arbitrary_to_ground_id
                    .get(type_param)
                    .unwrap_or_else(|| panic!("Arbitrary type {:?} not registered", type_param));
                Term::ground_type(*ground_id)
            }

            AcornType::Type0 => Term::type_sort(),

            AcornType::TypeclassConstraint(tc) => {
                let tc_id = self
                    .typeclass_to_id
                    .get(tc)
                    .unwrap_or_else(|| panic!("Typeclass {:?} not registered", tc));
                Term::typeclass(*tc_id)
            }
        }
    }

    /// Convert an AcornType to a type Term (no type variable support).
    /// This is a convenience wrapper that panics on type variables.
    pub fn to_type_term(&self, acorn_type: &AcornType) -> Term {
        self.to_type_term_with_vars(acorn_type, None)
    }

    /// Convert an AcornType with type parameters to a type Term using bound variables.
    /// Type parameters in `params` are converted to BoundVariable(index) based on their position.
    /// For example, if params = [T, U] and the type is T -> U, we get Pi(b0, b1) where
    /// b0 = BoundVariable(0) and b1 = BoundVariable(1).
    /// The result should be wrapped in Pi(Type, ...) binders for each type parameter.
    pub fn to_polymorphic_type_term(&self, acorn_type: &AcornType, params: &[AcornType]) -> Term {
        self.to_polymorphic_type_term_impl(acorn_type, params)
    }

    fn to_polymorphic_type_term_impl(&self, acorn_type: &AcornType, params: &[AcornType]) -> Term {
        use crate::kernel::atom::Atom;

        match acorn_type {
            AcornType::Empty => Term::empty_type(),
            AcornType::Bool => Term::bool_type(),

            AcornType::Data(datatype, type_args) if type_args.is_empty() => {
                let ground_id = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                Term::ground_type(*ground_id)
            }

            AcornType::Data(datatype, type_args) => {
                let constructor_ground = self
                    .datatype_to_ground_id
                    .get(datatype)
                    .unwrap_or_else(|| panic!("Data type {} not registered", datatype.name));
                let head = Term::ground_type(*constructor_ground);

                let args: Vec<Term> = type_args
                    .iter()
                    .map(|arg| self.to_polymorphic_type_term_impl(arg, params))
                    .collect();

                Term::type_application(head, args)
            }

            AcornType::Function(ft) => {
                let mut result = self.to_polymorphic_type_term_impl(&ft.return_type, params);

                // When wrapping with Pi, we need to shift bound variables in the result
                // because they're now inside a binder. Each Pi adds one to the De Bruijn index.
                for arg_type in ft.arg_types.iter().rev() {
                    let arg_type_term = self.to_polymorphic_type_term_impl(arg_type, params);
                    // Shift bound variables in result up by 1 since we're entering a Pi
                    result = result.shift_bound(0, 1);
                    result = Term::pi(arg_type_term, result);
                }

                result
            }

            AcornType::Variable(type_param) => {
                // Find the index of this type parameter in the params list by name.
                // We compare by name only, not the full TypeParam struct, because
                // the typeclass constraint might differ between generic_type and params.
                //
                // The bound variable index is computed as (n - 1 - i) because after the
                // caller wraps the result with Pi binders for type params, the first type
                // param (index 0) will be at the outermost binder, accessible via BV(n-1)
                // from inside, while the last type param (index n-1) will be at the
                // innermost binder, accessible via BV(0).
                let n = params.len();
                for (i, param) in params.iter().enumerate() {
                    if let AcornType::Variable(p) = param {
                        if p.name == type_param.name {
                            return Term::atom(Atom::BoundVariable((n - 1 - i) as u16));
                        }
                    }
                }
                panic!(
                    "Type variable {:?} not found in params: {:?}",
                    type_param, params
                );
            }

            AcornType::Arbitrary(type_param) => {
                // Arbitrary types should be registered, use as ground types
                let ground_id = self
                    .arbitrary_to_ground_id
                    .get(type_param)
                    .unwrap_or_else(|| panic!("Arbitrary type {:?} not registered", type_param));
                Term::ground_type(*ground_id)
            }

            AcornType::Type0 => Term::type_sort(),

            AcornType::TypeclassConstraint(tc) => {
                let tc_id = self
                    .typeclass_to_id
                    .get(tc)
                    .unwrap_or_else(|| panic!("Typeclass {:?} not registered", tc));
                Term::typeclass(*tc_id)
            }
        }
    }

    /// Convert a type Term back to an AcornType.
    /// This is the inverse of `to_type_term`.
    pub fn type_term_to_acorn_type(&self, type_term: &Term) -> AcornType {
        self.type_term_to_acorn_type_impl(type_term, 0)
    }

    /// Helper for type_term_to_acorn_type that tracks depth.
    ///
    /// `outer_depth` is the number of type param Pis we've skipped at the outer level.
    /// `local_depth` is the number of Pi binders we've entered within the current function type.
    ///
    /// For BoundVariable(i):
    /// - If i < local_depth: refers to a local function arg binder
    /// - If i >= local_depth: refers to an outer type param at index (i - local_depth)
    fn type_term_to_acorn_type_impl(&self, type_term: &Term, outer_depth: u16) -> AcornType {
        self.type_term_to_acorn_type_with_local(&type_term, outer_depth, 0)
    }

    /// Inner helper that also tracks local depth within function types.
    fn type_term_to_acorn_type_with_local(
        &self,
        type_term: &Term,
        outer_depth: u16,
        local_depth: u16,
    ) -> AcornType {
        // Check for built-in types first
        if type_term.as_ref().is_bool_type() {
            return AcornType::Bool;
        }
        if type_term.as_ref().is_empty_type() {
            return AcornType::Empty;
        }
        // Type0 is the "type of types" (kind *). Return the new AcornType::Type0 variant.
        if type_term.as_ref().is_type0() {
            return AcornType::Type0;
        }

        // Check for user-defined ground type
        if let Some(ground_id) = type_term.as_ref().as_type_atom() {
            // Ground type - look up in ground_id_to_type
            let mod_idx = ground_id.module_id().get() as usize;
            return self.ground_id_to_type[mod_idx][ground_id.local_id() as usize].clone();
        }

        // Check for Pi type
        if let Some((input, output)) = type_term.as_ref().split_pi() {
            // Pi type: convert to function type
            // Pi(A, Pi(B, C)) becomes (A, B) -> C
            // But Pi(Type, ...) and Pi(Typeclass, ...) are dependent types for polymorphic functions
            // - skip type parameter kinds since they're not value arguments
            let input_owned = input.to_owned();
            let is_type_param = input_owned.as_ref().is_type_param_kind();

            let mut arg_types = if is_type_param {
                vec![] // Skip type parameter kinds (they're not value arguments)
            } else {
                // Process input at current local depth (input is before entering this Pi's binder)
                vec![self.type_term_to_acorn_type_with_local(
                    &input_owned,
                    outer_depth,
                    local_depth,
                )]
            };

            // Track depths:
            // - Type param Pis increment outer_depth
            // - Function arg Pis increment local_depth
            let (mut current_outer, mut current_local) = if is_type_param {
                (outer_depth + 1, local_depth)
            } else {
                (outer_depth, local_depth + 1)
            };
            let mut current_output = output.to_owned();

            // Uncurry nested Pi types
            while let Some((next_input, next_output)) = current_output.as_ref().split_pi() {
                let next_input_owned = next_input.to_owned();
                let is_next_type_param = next_input_owned.as_ref().is_type_param_kind();
                // Skip type parameter kinds in nested Pi types too
                if !is_next_type_param {
                    // Process input at current local depth
                    arg_types.push(self.type_term_to_acorn_type_with_local(
                        &next_input_owned,
                        current_outer,
                        current_local,
                    ));
                }
                if is_next_type_param {
                    current_outer += 1;
                } else {
                    current_local += 1;
                }
                current_output = next_output.to_owned();
            }

            // Process return type at current depths
            let return_type = self.type_term_to_acorn_type_with_local(
                &current_output,
                current_outer,
                current_local,
            );

            // If we skipped all type arguments, just return the return type
            // (this happens with polymorphic constants that only have type params)
            if arg_types.is_empty() {
                return return_type;
            }

            let ft = FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            };
            return AcornType::Function(ft);
        }

        // Check for type application
        if let Some((head, args)) = type_term.as_ref().split_application_multi() {
            // Type application like List[Int]
            // Extract the datatype from head (must be a ground type)
            let base_type =
                self.type_term_to_acorn_type_with_local(&head, outer_depth, local_depth);
            let datatype = match &base_type {
                AcornType::Data(dt, params) if params.is_empty() => dt.clone(),
                _ => panic!(
                    "Expected ground data type in type application, got {:?}",
                    base_type
                ),
            };

            // Convert parameter types
            let params: Vec<AcornType> = args
                .iter()
                .map(|arg| self.type_term_to_acorn_type_with_local(arg, outer_depth, local_depth))
                .collect();

            return AcornType::Data(datatype, params);
        }

        // Handle BoundVariable - these can appear in dependent types that weren't fully instantiated
        // Convert to type variable for display purposes
        if type_term.as_ref().is_atomic() {
            if let Atom::BoundVariable(i) = type_term.as_ref().get_head_atom() {
                // BoundVariable(i) at local_depth d refers to:
                // - If i < d: a function argument binder (shouldn't happen for types in type positions)
                // - If i >= d: an outer binder at index (i - d), which is a type parameter
                //
                // De Bruijn indices go innermost to outermost, but type params are numbered
                // outermost to innermost (T0, T1, ...). So we need to invert:
                // - outer_index = i - local_depth (which outer binder, 0 = innermost skipped)
                // - type_param_index = (outer_depth - 1) - outer_index
                //
                // Example: 2 type params (outer_depth = 2)
                // - BoundVariable(0) at local_depth 0: outer_index = 0, type_param_index = 1 (T1)
                // - BoundVariable(1) at local_depth 0: outer_index = 1, type_param_index = 0 (T0)
                let type_param_index = if *i >= local_depth && outer_depth > 0 {
                    let outer_index = *i - local_depth;
                    if outer_index < outer_depth {
                        outer_depth - 1 - outer_index
                    } else {
                        // Refers to something beyond the skipped type params
                        outer_index
                    }
                } else {
                    // Fallback for i < local_depth (shouldn't happen in well-formed types)
                    *i
                };
                let type_param = TypeParam {
                    name: format!("T{}", type_param_index),
                    typeclass: None,
                };
                return AcornType::Variable(type_param);
            }
        }

        // Handle FreeVariable - these are used for type variables in polymorphic mode
        if type_term.as_ref().is_atomic() {
            if let Atom::FreeVariable(i) = type_term.as_ref().get_head_atom() {
                // Create a synthetic type variable for display purposes
                // Use "T" prefix since these are type variables (they appear in type terms)
                let type_param = TypeParam {
                    name: format!("T{}", i),
                    typeclass: None,
                };
                return AcornType::Variable(type_param);
            }
        }

        // Handle Typeclass - these are used as type constraints in polymorphic mode
        if type_term.as_ref().is_atomic() {
            if let Atom::Symbol(Symbol::Typeclass(tc_id)) = type_term.as_ref().get_head_atom() {
                // Convert back to a Typeclass. We need to look up the name.
                let mod_idx = tc_id.module_id().get() as usize;
                if let Some(typeclass) = self
                    .id_to_typeclass
                    .get(mod_idx)
                    .and_then(|v| v.get(tc_id.local_id() as usize))
                {
                    // Return as a TypeclassConstraint kind
                    return AcornType::TypeclassConstraint(typeclass.clone());
                }
            }
        }

        panic!("Unexpected type Term structure: {:?}", type_term);
    }

    /// Convert a type Term to AcornType, looking up typeclass constraints from LocalContext.
    /// When the type_term is a FreeVariable, this method checks its type in the context
    /// to determine if it has a typeclass constraint.
    ///
    /// If `instantiate_type_vars` is true, FreeVariable type atoms are converted to concrete
    /// types rather than becoming AcornType::Variable. If the type variable has a typeclass
    /// constraint, we find a concrete type implementing that typeclass; otherwise we use Bool.
    pub fn type_term_to_acorn_type_with_context(
        &self,
        type_term: &Term,
        local_context: &LocalContext,
        instantiate_type_vars: bool,
    ) -> AcornType {
        // Check for FreeVariable first - we need to look up its typeclass constraint
        if type_term.as_ref().is_atomic() {
            if let Atom::FreeVariable(var_id) = type_term.as_ref().get_head_atom() {
                // Look up the type of this variable in the context
                let var_type = local_context.get_var_type(*var_id as usize);
                let typeclass_id = if let Some(vt) = var_type {
                    // Check if the type is a Typeclass constraint
                    if let Atom::Symbol(Symbol::Typeclass(tc_id)) = vt.as_ref().get_head_atom() {
                        Some(*tc_id)
                    } else {
                        None
                    }
                } else {
                    None
                };

                if instantiate_type_vars {
                    // Convert to a concrete type
                    if let Some(tc_id) = typeclass_id {
                        // Find a type that implements this typeclass
                        if let Some(ground_id) = self.find_instance_of_typeclass(tc_id) {
                            let mod_idx = ground_id.module_id().get() as usize;
                            return self.ground_id_to_type[mod_idx][ground_id.local_id() as usize]
                                .clone();
                        }
                    }
                    // No typeclass constraint or no implementing type found - use Bool
                    return AcornType::Bool;
                }

                // Not instantiating - return a type variable
                // Use "T" prefix since these are type variables
                let typeclass = typeclass_id.and_then(|tc_id| {
                    let mod_idx = tc_id.module_id().get() as usize;
                    self.id_to_typeclass
                        .get(mod_idx)
                        .and_then(|v| v.get(tc_id.local_id() as usize).cloned())
                });
                let type_param = TypeParam {
                    name: format!("T{}", var_id),
                    typeclass,
                };
                return AcornType::Variable(type_param);
            }
        }
        // Fall back to regular conversion for non-FreeVariable types
        self.type_term_to_acorn_type(type_term)
    }

    /// Convert a type Term back to an AcornType, using provided names for FreeVariables.
    /// The `var_id_to_name` map translates FreeVariable IDs to their original type param names.
    /// This is useful when denormalizing terms that need to preserve the original type names.
    pub fn type_term_to_acorn_type_with_var_names(
        &self,
        type_term: &Term,
        var_id_to_name: &StdHashMap<AtomId, String>,
    ) -> AcornType {
        self.type_term_to_acorn_type_with_var_names_impl(type_term, 0, 0, var_id_to_name)
    }

    /// Inner helper that converts a type Term to AcornType using provided variable names.
    fn type_term_to_acorn_type_with_var_names_impl(
        &self,
        type_term: &Term,
        outer_depth: u16,
        local_depth: u16,
        var_id_to_name: &StdHashMap<AtomId, String>,
    ) -> AcornType {
        // Check for built-in types first
        if type_term.as_ref().is_bool_type() {
            return AcornType::Bool;
        }
        if type_term.as_ref().is_empty_type() {
            return AcornType::Empty;
        }
        // Type0 is the "type of types" (kind *). Return the new AcornType::Type0 variant.
        if type_term.as_ref().is_type0() {
            return AcornType::Type0;
        }

        // Check for user-defined ground type
        if let Some(ground_id) = type_term.as_ref().as_type_atom() {
            let mod_idx = ground_id.module_id().get() as usize;
            return self.ground_id_to_type[mod_idx][ground_id.local_id() as usize].clone();
        }

        // Check for Pi type
        if let Some((input, output)) = type_term.as_ref().split_pi() {
            let input_owned = input.to_owned();
            let is_type_param = input_owned.as_ref().is_type_param_kind();

            let mut arg_types = if is_type_param {
                vec![]
            } else {
                vec![self.type_term_to_acorn_type_with_var_names_impl(
                    &input_owned,
                    outer_depth,
                    local_depth,
                    var_id_to_name,
                )]
            };

            let (mut current_outer, mut current_local) = if is_type_param {
                (outer_depth + 1, local_depth)
            } else {
                (outer_depth, local_depth + 1)
            };
            let mut current_output = output.to_owned();

            // Uncurry nested Pi types
            while let Some((next_input, next_output)) = current_output.as_ref().split_pi() {
                let next_input_owned = next_input.to_owned();
                let next_is_type_param = next_input_owned.as_ref().is_type_param_kind();

                if !next_is_type_param {
                    arg_types.push(self.type_term_to_acorn_type_with_var_names_impl(
                        &next_input_owned,
                        current_outer,
                        current_local,
                        var_id_to_name,
                    ));
                }

                if next_is_type_param {
                    current_outer += 1;
                } else {
                    current_local += 1;
                }
                current_output = next_output.to_owned();
            }

            let return_type = self.type_term_to_acorn_type_with_var_names_impl(
                &current_output,
                current_outer,
                current_local,
                var_id_to_name,
            );

            if arg_types.is_empty() {
                return return_type;
            }

            let ft = FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            };
            return AcornType::Function(ft);
        }

        // Check for type application
        if let Some((head, args)) = type_term.as_ref().split_application_multi() {
            let base_type = self.type_term_to_acorn_type_with_var_names_impl(
                &head,
                outer_depth,
                local_depth,
                var_id_to_name,
            );
            let datatype = match &base_type {
                AcornType::Data(dt, params) if params.is_empty() => dt.clone(),
                _ => panic!(
                    "Expected ground data type in type application, got {:?}",
                    base_type
                ),
            };

            let params: Vec<AcornType> = args
                .iter()
                .map(|arg| {
                    self.type_term_to_acorn_type_with_var_names_impl(
                        arg,
                        outer_depth,
                        local_depth,
                        var_id_to_name,
                    )
                })
                .collect();

            return AcornType::Data(datatype, params);
        }

        // Handle BoundVariable
        if type_term.as_ref().is_atomic() {
            if let Atom::BoundVariable(i) = type_term.as_ref().get_head_atom() {
                let type_param_index = if *i >= local_depth && outer_depth > 0 {
                    let outer_index = *i - local_depth;
                    if outer_index < outer_depth {
                        outer_depth - 1 - outer_index
                    } else {
                        outer_index
                    }
                } else {
                    *i
                };
                // Look up the name by index in the sorted var_id_to_name mapping
                let name = {
                    let mut entries: Vec<_> = var_id_to_name.iter().collect();
                    entries.sort_by_key(|(id, _)| *id);
                    entries
                        .get(type_param_index as usize)
                        .map(|(_, name)| (*name).clone())
                        .unwrap_or_else(|| {
                            panic!(
                                "BoundVariable at type_param_index {} not found in var_id_to_name map (map has {} entries)",
                                type_param_index,
                                var_id_to_name.len()
                            )
                        })
                };
                let type_param = TypeParam {
                    name,
                    typeclass: None,
                };
                return AcornType::Variable(type_param);
            }
        }

        // Handle FreeVariable - look up in var_id_to_name map
        if type_term.as_ref().is_atomic() {
            if let Atom::FreeVariable(i) = type_term.as_ref().get_head_atom() {
                if let Some(name) = var_id_to_name.get(i) {
                    let type_param = TypeParam {
                        name: name.clone(),
                        typeclass: None,
                    };
                    return AcornType::Variable(type_param);
                }
                panic!(
                    "FreeVariable({}) not found in var_id_to_name map. \
                     When using type_term_to_acorn_type_with_var_names, all type variables must be in the map.",
                    i
                );
            }
        }

        // Handle Typeclass - return TypeclassConstraint
        if type_term.as_ref().is_atomic() {
            if let Atom::Symbol(Symbol::Typeclass(tc_id)) = type_term.as_ref().get_head_atom() {
                let mod_idx = tc_id.module_id().get() as usize;
                if let Some(typeclass) = self
                    .id_to_typeclass
                    .get(mod_idx)
                    .and_then(|v| v.get(tc_id.local_id() as usize))
                {
                    return AcornType::TypeclassConstraint(typeclass.clone());
                }
            }
        }

        panic!("Unexpected type Term structure: {:?}", type_term);
    }

    /// Get the id for a typeclass if it exists, otherwise return an error.
    pub fn get_typeclass_id(&self, typeclass: &Typeclass) -> Result<TypeclassId, String> {
        self.typeclass_to_id
            .get(typeclass)
            .copied()
            .ok_or_else(|| format!("Typeclass {} not registered in type store", typeclass.name))
    }

    /// Returns the id for the typeclass, adding it if it doesn't already exist.
    pub fn add_typeclass(&mut self, typeclass: &Typeclass) -> TypeclassId {
        if let Some(id) = self.typeclass_to_id.get(typeclass) {
            return *id;
        }

        let module_id = typeclass.module_id;
        let mod_idx = module_id.get() as usize;
        let local_id = self
            .id_to_typeclass
            .get(mod_idx)
            .map(|v| v.len())
            .unwrap_or(0) as u16;
        let id = TypeclassId::new(module_id, local_id);

        self.ensure_typeclass_module(module_id);
        self.id_to_typeclass[mod_idx].push_back(typeclass.clone());
        self.typeclass_extends[mod_idx].push_back(StdHashSet::new());
        self.typeclass_instances[mod_idx].push_back(StdHashSet::new());
        self.typeclass_to_id.insert(typeclass.clone(), id);
        id
    }

    /// Get the typeclass for a given id.
    pub fn get_typeclass(&self, typeclass_id: TypeclassId) -> &Typeclass {
        let mod_idx = typeclass_id.module_id().get() as usize;
        &self.id_to_typeclass[mod_idx][typeclass_id.local_id() as usize]
    }

    /// Get a typeclass by its ID, returning None if the ID is out of range.
    pub fn get_typeclass_by_id(&self, typeclass_id: TypeclassId) -> Option<&Typeclass> {
        let mod_idx = typeclass_id.module_id().get() as usize;
        self.id_to_typeclass
            .get(mod_idx)
            .and_then(|v| v.get(typeclass_id.local_id() as usize))
    }

    /// Get the TypeclassId for a typeclass by name.
    /// Returns None if not found.
    #[cfg(test)]
    pub fn get_typeclass_id_by_name(&self, name: &str) -> Option<TypeclassId> {
        for (mod_idx, typeclasses) in self.id_to_typeclass.iter().enumerate() {
            for (local_id, tc) in typeclasses.iter().enumerate() {
                if tc.name == name {
                    return Some(TypeclassId::new(ModuleId(mod_idx as u16), local_id as u16));
                }
            }
        }
        None
    }

    /// Register that one typeclass extends another.
    /// This should be the direct extension relationship; the transitive closure is computed automatically.
    pub fn add_typeclass_extends(&mut self, typeclass_id: TypeclassId, base_id: TypeclassId) {
        let mod_idx = typeclass_id.module_id().get() as usize;
        let local_idx = typeclass_id.local_id() as usize;

        // Add the direct extension
        self.ensure_typeclass_module(typeclass_id.module_id());
        if let Some(s) = self.typeclass_extends[mod_idx].get_mut(local_idx) {
            s.insert(base_id);
        }

        // Also add all typeclasses that the base extends (transitive closure)
        let base_mod_idx = base_id.module_id().get() as usize;
        let base_extends: Vec<TypeclassId> = self
            .typeclass_extends
            .get(base_mod_idx)
            .and_then(|v| v.get(base_id.local_id() as usize))
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default();
        for transitive_base in base_extends {
            if let Some(s) = self.typeclass_extends[mod_idx].get_mut(local_idx) {
                s.insert(transitive_base);
            }
        }
    }

    /// Register that a ground type is an instance of a typeclass.
    fn add_instance(&mut self, ground_id: GroundTypeId, typeclass_id: TypeclassId) {
        let mod_idx = typeclass_id.module_id().get() as usize;
        self.ensure_typeclass_module(typeclass_id.module_id());
        if let Some(s) = self.typeclass_instances[mod_idx].get_mut(typeclass_id.local_id() as usize)
        {
            s.insert(ground_id);
        }
    }

    /// Register that a type (given as AcornType) is an instance of a typeclass.
    /// The type must be a ground type (bare data type with no params).
    pub fn add_type_instance(&mut self, acorn_type: &AcornType, typeclass_id: TypeclassId) {
        // Ensure the type is registered
        self.add_type_internal(acorn_type);

        // Get the GroundTypeId - only ground types can be typeclass instances
        let ground_id = match acorn_type {
            AcornType::Data(datatype, params) if params.is_empty() => self
                .datatype_to_ground_id
                .get(datatype)
                .copied()
                .expect("Data type should have been registered"),
            _ => panic!(
                "Only bare data types can be typeclass instances, got {:?}",
                acorn_type
            ),
        };
        self.add_instance(ground_id, typeclass_id);
    }

    /// Check if one typeclass extends another (directly or transitively).
    pub fn typeclass_extends(&self, typeclass_id: TypeclassId, base_id: TypeclassId) -> bool {
        let mod_idx = typeclass_id.module_id().get() as usize;
        self.typeclass_extends
            .get(mod_idx)
            .and_then(|v| v.get(typeclass_id.local_id() as usize))
            .map_or(false, |extends| extends.contains(&base_id))
    }

    /// Get all typeclasses that a given typeclass extends (directly or transitively).
    pub fn get_typeclass_extends(
        &self,
        typeclass_id: TypeclassId,
    ) -> impl Iterator<Item = TypeclassId> + '_ {
        let mod_idx = typeclass_id.module_id().get() as usize;
        self.typeclass_extends
            .get(mod_idx)
            .and_then(|v| v.get(typeclass_id.local_id() as usize))
            .into_iter()
            .flat_map(|extends: &StdHashSet<TypeclassId>| extends.iter().copied())
    }

    /// Creates a Term representing a typeclass.
    /// This is used when a type variable is constrained to a typeclass.
    pub fn typeclass_to_term(&self, typeclass_id: TypeclassId) -> Term {
        Term::atom(Atom::Symbol(Symbol::Typeclass(typeclass_id)))
    }

    /// Checks if a ground type is an instance of a typeclass.
    /// This handles two cases:
    /// 1. The ground type was explicitly registered as an instance of the typeclass
    /// 2. The ground type is an arbitrary type with a compatible typeclass constraint
    pub fn is_instance_of(&self, ground_id: GroundTypeId, typeclass_id: TypeclassId) -> bool {
        // First check explicit instances
        let mod_idx = typeclass_id.module_id().get() as usize;
        if self
            .typeclass_instances
            .get(mod_idx)
            .and_then(|v| v.get(typeclass_id.local_id() as usize))
            .map_or(false, |instances| instances.contains(&ground_id))
        {
            return true;
        }

        // Also check if this is an arbitrary type with a compatible typeclass constraint
        if let Some(arb_tc_id) = self.get_arbitrary_typeclass(ground_id) {
            // The arbitrary type's constraint is compatible if it's the same typeclass
            // or if it extends the required typeclass
            if arb_tc_id == typeclass_id || self.typeclass_extends(arb_tc_id, typeclass_id) {
                return true;
            }
        }

        false
    }

    /// Find any ground type that implements the given typeclass.
    /// Returns None if no instances are registered.
    pub fn find_instance_of_typeclass(&self, typeclass_id: TypeclassId) -> Option<GroundTypeId> {
        let mod_idx = typeclass_id.module_id().get() as usize;
        self.typeclass_instances
            .get(mod_idx)
            .and_then(|v| v.get(typeclass_id.local_id() as usize))
            .and_then(|instances| instances.iter().next().copied())
    }

    /// Get the typeclass constraint for a ground type, if it represents an arbitrary type
    /// with a typeclass constraint.
    /// Returns the TypeclassId if the ground type is an arbitrary type with a typeclass.
    pub fn get_arbitrary_typeclass(&self, ground_id: GroundTypeId) -> Option<TypeclassId> {
        // Look through arbitrary_to_ground_id to find if this ground_id is an arbitrary type
        for (type_param, &gid) in &self.arbitrary_to_ground_id {
            if gid == ground_id {
                // Found it - check if it has a typeclass constraint
                if let Some(tc) = &type_param.typeclass {
                    return self.typeclass_to_id.get(tc).copied();
                }
            }
        }
        None
    }

    /// Merges another TypeStore into this one.
    /// Entries from `other` are added to `self`. If there are conflicts,
    /// the entries should be identical (same module_id, local_id -> same value).
    pub fn merge(&mut self, other: &TypeStore) {
        // Merge ground types and arities
        merge_nested_vecs(&mut self.ground_id_to_type, &other.ground_id_to_type);
        merge_nested_vecs(&mut self.ground_id_to_arity, &other.ground_id_to_arity);

        // Merge hash maps
        for (k, v) in other.datatype_to_ground_id.iter() {
            self.datatype_to_ground_id.insert(k.clone(), *v);
        }
        for (k, v) in other.arbitrary_to_ground_id.iter() {
            self.arbitrary_to_ground_id.insert(k.clone(), *v);
        }
        for (k, v) in other.typeclass_to_id.iter() {
            self.typeclass_to_id.insert(k.clone(), *v);
        }

        // Merge typeclass vectors
        merge_nested_vecs(&mut self.id_to_typeclass, &other.id_to_typeclass);

        // Merge typeclass_extends and typeclass_instances (union sets)
        merge_nested_vecs_with(
            &mut self.typeclass_extends,
            &other.typeclass_extends,
            |a, b| a.union(b).cloned().collect(),
        );
        merge_nested_vecs_with(
            &mut self.typeclass_instances,
            &other.typeclass_instances,
            |a, b| a.union(b).cloned().collect(),
        );
    }
}

/// Merge entries from `source` into `target`, extending as needed.
/// Entries are expected to be contiguous (no gaps).
fn merge_vec<T: Clone>(target: &mut ImVector<T>, source: &ImVector<T>) {
    for (idx, item) in source.iter().enumerate() {
        if idx < target.len() {
            target.set(idx, item.clone());
        } else {
            debug_assert_eq!(idx, target.len());
            target.push_back(item.clone());
        }
    }
}

/// Merge nested vectors: outer is indexed by module_id, inner by local_id.
fn merge_nested_vecs<T: Clone>(target: &mut ImVector<ImVector<T>>, source: &ImVector<ImVector<T>>) {
    while target.len() < source.len() {
        target.push_back(ImVector::new());
    }
    for (mod_idx, source_inner) in source.iter().enumerate() {
        merge_vec(&mut target[mod_idx], source_inner);
    }
}

/// Merge nested vectors with a custom combine function for overlapping entries.
fn merge_nested_vecs_with<T: Clone, F>(
    target: &mut ImVector<ImVector<T>>,
    source: &ImVector<ImVector<T>>,
    combine: F,
) where
    F: Fn(&T, &T) -> T,
{
    while target.len() < source.len() {
        target.push_back(ImVector::new());
    }
    for (mod_idx, source_inner) in source.iter().enumerate() {
        for (idx, item) in source_inner.iter().enumerate() {
            let target_len = target[mod_idx].len();
            if idx < target_len {
                let merged = combine(&target[mod_idx][idx], item);
                target[mod_idx].set(idx, merged);
            } else {
                debug_assert_eq!(idx, target_len);
                target[mod_idx].push_back(item.clone());
            }
        }
    }
}

impl Default for TypeStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_store_defaults() {
        let store = TypeStore::new();
        // Empty and Bool are now Symbol variants - verify via to_type_term
        let empty_term = store.to_type_term(&AcornType::Empty);
        assert!(empty_term.as_ref().is_empty_type());
        let bool_term = store.to_type_term(&AcornType::Bool);
        assert!(bool_term.as_ref().is_bool_type());
    }

    #[test]
    fn test_to_type_term_ground() {
        let store = TypeStore::new();

        // Built-in types should convert to their Symbol variants
        let bool_term = store.to_type_term(&AcornType::Bool);
        assert!(bool_term.as_ref().is_atomic());
        assert!(bool_term.as_ref().is_bool_type());

        let empty_term = store.to_type_term(&AcornType::Empty);
        assert!(empty_term.as_ref().is_atomic());
        assert!(empty_term.as_ref().is_empty_type());
    }

    #[test]
    fn test_to_type_term_function() {
        let mut store = TypeStore::new();

        // Create Bool -> Bool function type
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        store.add_type(&bool_to_bool);

        let type_term = store.to_type_term(&bool_to_bool);
        assert!(type_term.as_ref().is_pi());

        let (input, output) = type_term.as_ref().split_pi().unwrap();
        assert!(input.is_bool_type());
        assert!(output.is_bool_type());
    }

    #[test]
    fn test_to_type_term_curried_function() {
        let mut store = TypeStore::new();

        // Create (Bool, Bool) -> Bool function type
        // Should become Pi(Bool, Pi(Bool, Bool))
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        store.add_type(&bool2_to_bool);

        let type_term = store.to_type_term(&bool2_to_bool);
        assert!(type_term.as_ref().is_pi());

        // First Pi: Bool -> (Bool -> Bool)
        let (input1, rest) = type_term.as_ref().split_pi().unwrap();
        assert!(input1.is_bool_type());
        assert!(rest.is_pi());

        // Second Pi: Bool -> Bool
        let (input2, output) = rest.split_pi().unwrap();
        assert!(input2.is_bool_type());
        assert!(output.is_bool_type());
    }

    #[test]
    fn test_to_type_term_parameterized_data() {
        use crate::elaborator::acorn_type::Datatype;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Create a parameterized type like List[Bool]
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_bool = AcornType::Data(list_datatype.clone(), vec![AcornType::Bool]);
        store.add_type(&list_bool);

        // The bare constructor should have been auto-registered
        let list_ground = store
            .get_datatype_id(&list_datatype)
            .expect("List should be registered");

        // Get the type term
        let type_term = store.to_type_term(&list_bool);

        // It should be an Application
        assert!(
            type_term.as_ref().is_application(),
            "Expected Application, got {:?}",
            type_term
        );

        // Check structure using split_application_multi
        let (head, args) = type_term.as_ref().split_application_multi().unwrap();

        // The head should be the bare List constructor's GroundTypeId
        assert_eq!(
            head.as_ref().as_type_atom(),
            Some(list_ground),
            "Head should be List constructor, got {:?}",
            head
        );

        // There should be exactly one argument (Bool)
        assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());
        assert!(
            args[0].as_ref().is_bool_type(),
            "Argument should be Bool, got {:?}",
            args[0]
        );
    }

    #[test]
    fn test_to_type_term_nested_parameterized_data() {
        use crate::elaborator::acorn_type::Datatype;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Create List[List[Bool]] - nested parameterized type
        let list_datatype = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let list_bool = AcornType::Data(list_datatype.clone(), vec![AcornType::Bool]);
        let list_list_bool = AcornType::Data(list_datatype.clone(), vec![list_bool.clone()]);
        store.add_type(&list_list_bool);

        // Get GroundTypeId for List constructor
        let list_ground = store
            .get_datatype_id(&list_datatype)
            .expect("List should be registered");

        // Get the type term for List[List[Bool]]
        let type_term = store.to_type_term(&list_list_bool);

        // It should be an Application
        assert!(
            type_term.as_ref().is_application(),
            "Expected Application, got {:?}",
            type_term
        );

        // Check structure using split_application_multi
        let (head, args) = type_term.as_ref().split_application_multi().unwrap();

        // The head should be the bare List constructor
        assert_eq!(
            head.as_ref().as_type_atom(),
            Some(list_ground),
            "Head should be List constructor, got {:?}",
            head
        );

        // There should be exactly one argument (List[Bool])
        assert_eq!(args.len(), 1, "Expected 1 argument, got {}", args.len());

        // The argument should be List[Bool], which is also an Application
        let inner_term = &args[0];
        assert!(
            inner_term.as_ref().is_application(),
            "Inner type should be Application"
        );

        let (inner_head, inner_args) = inner_term.as_ref().split_application_multi().unwrap();
        assert_eq!(
            inner_head.as_ref().as_type_atom(),
            Some(list_ground),
            "Inner head should also be List constructor"
        );
        assert_eq!(inner_args.len(), 1, "Inner should have 1 argument");
        assert!(
            inner_args[0].as_ref().is_bool_type(),
            "Innermost argument should be Bool"
        );
    }

    #[test]
    fn test_typeclass_to_term() {
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = store.add_typeclass(&monoid);

        // Create a term for the typeclass
        let term = store.typeclass_to_term(monoid_id);

        // Verify it's an atomic term with Typeclass atom
        assert!(term.as_ref().is_atomic());
        assert_eq!(term.as_ref().as_typeclass(), Some(monoid_id));
    }

    #[test]
    fn test_is_instance_of() {
        use crate::elaborator::acorn_type::{Datatype, Typeclass};
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = store.add_typeclass(&monoid);

        // Register data types
        let int_type = Datatype {
            module_id: ModuleId(0),
            name: "Int".to_string(),
        };
        let int_acorn = AcornType::Data(int_type.clone(), vec![]);
        store.add_type(&int_acorn);
        let int_id = store.get_datatype_id(&int_type).unwrap();

        let nat_type = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let nat_acorn = AcornType::Data(nat_type.clone(), vec![]);
        store.add_type(&nat_acorn);
        let nat_id = store.get_datatype_id(&nat_type).unwrap();

        // Before adding as instance, should return false
        assert!(!store.is_instance_of(int_id, monoid_id));

        // Add Int as instance of Monoid
        store.add_type_instance(&int_acorn, monoid_id);

        // Now should return true
        assert!(store.is_instance_of(int_id, monoid_id));

        // Nat should not be an instance (we didn't add it)
        assert!(!store.is_instance_of(nat_id, monoid_id));
    }

    #[test]
    fn test_is_instance_of_with_arbitrary_type() {
        // Tests that is_instance_of correctly handles arbitrary types
        // that have typeclass constraints.
        //
        // This is the core bug fix: when we have an arbitrary type G: Foo,
        // is_instance_of(G, Foo) should return true.
        use crate::elaborator::acorn_type::{TypeParam, Typeclass};
        use crate::module::ModuleId;

        let mut store = TypeStore::new();

        // Register the Foo typeclass
        let foo_typeclass = Typeclass {
            module_id: ModuleId(0),
            name: "Foo".to_string(),
        };
        let foo_tc_id = store.add_typeclass(&foo_typeclass);

        // Create arbitrary type G with Foo typeclass constraint
        let g_type_param = TypeParam {
            name: "G".to_string(),
            typeclass: Some(foo_typeclass.clone()),
        };
        let g_type = AcornType::Arbitrary(g_type_param.clone());
        store.add_type(&g_type);

        // Get the ground ID for the arbitrary type via the arbitrary_to_ground_id map
        let g_ground_id = *store.arbitrary_to_ground_id.get(&g_type_param).unwrap();

        // G: Foo should be considered an instance of Foo
        assert!(
            store.is_instance_of(g_ground_id, foo_tc_id),
            "Arbitrary type G: Foo should be an instance of Foo"
        );

        // Register another typeclass that G doesn't implement
        let bar_typeclass = Typeclass {
            module_id: ModuleId(0),
            name: "Bar".to_string(),
        };
        let bar_tc_id = store.add_typeclass(&bar_typeclass);

        // G should NOT be an instance of Bar
        assert!(
            !store.is_instance_of(g_ground_id, bar_tc_id),
            "Arbitrary type G: Foo should NOT be an instance of Bar"
        );
    }

    #[test]
    fn test_type_term_to_acorn_type_nested_bound_variables() {
        // Tests that BoundVariables at different depths in a type term
        // are correctly identified as referring to the same type parameter.
        //
        // The type Pi(Type, Pi(Pi(b0, Pi(b1, Bool)), b1)) represents:
        //   forall T. ((T -> T -> Bool) -> T)
        // where b0, b1, and the final b1 all refer to the type parameter T.
        //
        // Converting to AcornType should give: ((T0, T0) -> Bool) -> T0
        // NOT: ((T0, T1) -> Bool) -> T1 (which would incorrectly treat them as different params)

        use super::*;
        use crate::kernel::atom::Atom;
        use crate::kernel::term::Term;

        let store = TypeStore::new();

        // Build Pi(Type, Pi(Pi(b0, Pi(b1, Bool)), b1))
        // Start from the inside out:
        // - Bool
        let bool_term = Term::bool_type();
        // - Pi(b1, Bool) - b1 at this depth (inside Pi(b0, ...)) refers to outer Type
        let b1 = Term::atom(Atom::BoundVariable(1));
        let pi_b1_bool = Term::pi(b1.clone(), bool_term);
        // - Pi(b0, Pi(b1, Bool)) - b0 at this depth refers to outer Type
        let b0 = Term::atom(Atom::BoundVariable(0));
        let arg_type = Term::pi(b0, pi_b1_bool);
        // - Pi(arg_type, b1) - b1 at this depth (output of middle Pi) refers to Type
        let middle_pi = Term::pi(arg_type, b1);
        // - Pi(Type, middle_pi)
        let type_sort = Term::type_sort();
        let full_type = Term::pi(type_sort, middle_pi);

        // Convert to AcornType
        let acorn_type = store.type_term_to_acorn_type(&full_type);

        // Verify the structure: ((T0, T0) -> Bool) -> T0
        match &acorn_type {
            AcornType::Function(ft) => {
                // Should have 1 argument (the function (T0, T0) -> Bool)
                assert_eq!(ft.arg_types.len(), 1, "Expected 1 arg type");

                // The argument should be a function type
                match &ft.arg_types[0] {
                    AcornType::Function(inner_ft) => {
                        // Should have 2 arguments, both T0
                        assert_eq!(
                            inner_ft.arg_types.len(),
                            2,
                            "Inner function should have 2 args"
                        );

                        // Both args should be T0 (same type variable)
                        for (i, arg) in inner_ft.arg_types.iter().enumerate() {
                            match arg {
                                AcornType::Variable(tp) => {
                                    assert_eq!(
                                        tp.name, "T0",
                                        "Arg {} should be T0, got {}",
                                        i, tp.name
                                    );
                                }
                                _ => panic!("Expected Variable, got {:?}", arg),
                            }
                        }

                        // Return type should be Bool
                        assert!(
                            matches!(*inner_ft.return_type, AcornType::Bool),
                            "Inner return should be Bool"
                        );
                    }
                    _ => panic!("Expected inner Function type, got {:?}", ft.arg_types[0]),
                }

                // Return type should be T0
                match ft.return_type.as_ref() {
                    AcornType::Variable(tp) => {
                        assert_eq!(tp.name, "T0", "Return type should be T0, got {}", tp.name);
                    }
                    _ => panic!("Expected return Variable, got {:?}", ft.return_type),
                }
            }
            _ => panic!("Expected Function type, got {:?}", acorn_type),
        }
    }
}
