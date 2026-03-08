use std::collections::HashMap as StdHashMap;

use im::{HashMap as ImHashMap, HashSet as ImHashSet, Vector as ImVector};

use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::{AcornValue, ConstantInstance};
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::kernel::type_store::TypeStore;
use crate::kernel::types::{GroundTypeId, TypeclassId};
use crate::module::ModuleId;

fn not_symbol_type_ref() -> &'static Term {
    use std::sync::LazyLock;
    static NOT_TYPE: LazyLock<Term> =
        LazyLock::new(|| Term::pi(Term::bool_type(), Term::bool_type()));
    &NOT_TYPE
}

fn bool_binary_symbol_type_ref() -> &'static Term {
    use std::sync::LazyLock;
    static BOOL_BINARY_TYPE: LazyLock<Term> = LazyLock::new(|| {
        Term::pi(
            Term::bool_type(),
            Term::pi(Term::bool_type(), Term::bool_type()),
        )
    });
    &BOOL_BINARY_TYPE
}

fn eq_symbol_type_ref() -> &'static Term {
    use std::sync::LazyLock;
    static EQ_TYPE: LazyLock<Term> = LazyLock::new(|| {
        // forall(T: Type0). T -> T -> Bool
        // Inside the second arrow, the type parameter T is at de Bruijn index 1.
        let first_arg_type = Term::atom(Atom::BoundVariable(0));
        let second_arg_type = Term::atom(Atom::BoundVariable(1));
        Term::pi(
            Term::type_sort(),
            Term::pi(first_arg_type, Term::pi(second_arg_type, Term::bool_type())),
        )
    });
    &EQ_TYPE
}

fn ite_symbol_type_ref() -> &'static Term {
    use std::sync::LazyLock;
    static ITE_TYPE: LazyLock<Term> = LazyLock::new(|| {
        // Pi(T: Type0). Bool -> T -> T -> T
        // After binding Bool and two branch values, T is at de Bruijn index 3.
        let then_arg_type = Term::atom(Atom::BoundVariable(1));
        let else_arg_type = Term::atom(Atom::BoundVariable(2));
        let result_type = Term::atom(Atom::BoundVariable(3));
        Term::pi(
            Term::type_sort(),
            Term::pi(
                Term::bool_type(),
                Term::pi(then_arg_type, Term::pi(else_arg_type, result_type)),
            ),
        )
    });
    &ITE_TYPE
}

fn choose_symbol_type_ref() -> &'static Term {
    use std::sync::LazyLock;
    static CHOOSE_TYPE: LazyLock<Term> = LazyLock::new(|| {
        // Pi(T: Type0). (T -> Bool) -> T
        // Under the input arrow binder, T is at de Bruijn index 1.
        let predicate_type = Term::pi(Term::atom(Atom::BoundVariable(1)), Term::bool_type());
        let result_type = Term::atom(Atom::BoundVariable(1));
        Term::pi(Term::type_sort(), Term::pi(predicate_type, result_type))
    });
    &CHOOSE_TYPE
}

#[derive(Clone, Copy, Debug)]
pub enum NewConstantType {
    Global,
    Local,
}

/// Info about a polymorphic constant's generic type structure.
/// Used to properly denormalize constants.
#[derive(Clone, Debug)]
pub struct PolymorphicInfo {
    /// The generic type with type Variables (not Arbitrary types).
    pub generic_type: AcornType,
    /// The ordered names of type parameters.
    pub type_param_names: Vec<String>,
}

/// Metadata for a datatype match eliminator (`Type.match`).
/// Stores constructor constants in constructor-index order.
#[derive(Clone, Debug)]
pub struct MatchEliminatorInfo {
    pub constructor_symbols: Vec<Symbol>,
}

/// In the Acorn language, constants and types have names, scoped by modules. They can be rich values
/// with internal structure, like polymorphic parameters or complex types.
/// The prover, on the other hand, operates in simply typed higher order logic.
/// The SymbolTable is a mapping between the two (excluding types, which are handled by TypeStore).
#[derive(Clone)]
pub struct SymbolTable {
    /// For global constant (module_id, local_id) in the prover,
    /// global_constants[module_id][local_id] is the corresponding ConstantName.
    /// Part of the Symbol -> ConstantName lookup direction.
    /// Uses im::Vector for O(1) clones.
    global_constants: ImVector<ImVector<Option<ConstantName>>>,

    /// For global constant (module_id, local_id) in the prover,
    /// global_constant_types[module_id][local_id] is the type.
    /// Uses im::Vector for O(1) clones.
    global_constant_types: ImVector<ImVector<Term>>,

    /// For local constant i in the prover, scoped_constants[i] is the corresponding ConstantName.
    /// Part of the Symbol -> ConstantName lookup direction.
    scoped_constants: ImVector<Option<ConstantName>>,

    /// For local constant i in the prover, scoped_constant_types[i] is the type.
    scoped_constant_types: ImVector<Term>,

    /// Inverse map of constants that can be referenced with a single name.
    /// The ConstantName -> Symbol lookup direction.
    name_to_symbol: ImHashMap<ConstantName, Symbol>,

    /// Maps constant instances (with type parameters) to their Symbol aliases.
    /// Used for instance definitions where e.g. Arf.foo[Foo] = Foo.foo.
    instance_to_symbol: ImHashMap<ConstantInstance, Symbol>,

    /// For synthetic atom (module_id, local_id), synthetic_types[module_id][local_id] is the type.
    /// Uses im::Vector for O(1) clones.
    synthetic_types: ImVector<ImVector<Term>>,

    /// Maps polymorphic constant names to their generic type info.
    /// Used to properly denormalize constants.
    polymorphic_info: ImHashMap<ConstantName, PolymorphicInfo>,

    /// Metadata for datatype match eliminators (`Type.match`) used to reconstruct
    /// `AcornValue::Match` from term applications in bridge mode.
    match_eliminator_info: ImHashMap<Symbol, MatchEliminatorInfo>,

    /// Maps a type to the first symbol registered with that type.
    /// Used to get an element of a particular type (e.g., for instantiating universal quantifiers).
    type_to_element: ImHashMap<Term, Symbol>,

    /// Type constructors known to be inhabited for any type arguments.
    /// For example, if we have `nil: forall[T]. List[T]`, then List is in this set.
    inhabited_type_constructors: ImHashSet<GroundTypeId>,

    /// A witness-provider symbol for each inhabited type constructor.
    /// The symbol has polymorphic type-level arguments and no value-level arguments.
    /// For example, `nil: forall[T]. List[T]` witnesses `List`.
    inhabited_type_constructor_witnesses: ImHashMap<GroundTypeId, Symbol>,

    /// Typeclasses that are known to provide inhabitants for their instance types.
    /// For example, if we have `point: forall[P: Pointed]. P`, then Pointed is in this set.
    inhabited_typeclasses: ImHashSet<TypeclassId>,

    /// A witness-provider symbol for each inhabited typeclass.
    /// For example, `point: forall[P: Pointed]. P` witnesses `Pointed`.
    inhabited_typeclass_witnesses: ImHashMap<TypeclassId, Symbol>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            global_constants: ImVector::new(),
            global_constant_types: ImVector::new(),
            scoped_constants: ImVector::new(),
            scoped_constant_types: ImVector::new(),
            name_to_symbol: ImHashMap::new(),
            instance_to_symbol: ImHashMap::new(),
            synthetic_types: ImVector::new(),
            polymorphic_info: ImHashMap::new(),
            match_eliminator_info: ImHashMap::new(),
            type_to_element: ImHashMap::new(),
            inhabited_type_constructors: ImHashSet::new(),
            inhabited_type_constructor_witnesses: ImHashMap::new(),
            inhabited_typeclasses: ImHashSet::new(),
            inhabited_typeclass_witnesses: ImHashMap::new(),
        }
    }

    /// Record a symbol as an element of a type (only if no element exists for that type yet).
    fn record_element(&mut self, var_type: Term, symbol: Symbol) {
        // Also track inhabited type constructors for polymorphic types.
        // If var_type is Pi(Type, ...) or Pi(Typeclass, ...), the return type's
        // ground type constructor is inhabited for any type arguments.
        self.record_inhabited_type_constructor(&var_type, symbol);

        self.type_to_element.entry(var_type).or_insert(symbol);
    }

    /// If the type is a polymorphic type (Pi with Type/Typeclass inputs),
    /// record its return type's ground type constructor as inhabited.
    /// Also tracks typeclasses that provide inhabitants for their instance types.
    fn record_inhabited_type_constructor(&mut self, var_type: &Term, symbol: Symbol) {
        let mut current = var_type.as_ref();
        let mut depth = 0; // Track how many Pi levels we've descended

        // Strip off Pi types with Type or Typeclass inputs
        loop {
            if let Some((input, output)) = current.split_pi() {
                let head = input.get_head_atom();
                // Check if the input is Type or Typeclass
                match head {
                    Atom::Symbol(Symbol::Type0) => {
                        current = output;
                        depth += 1;
                        continue;
                    }
                    Atom::Symbol(Symbol::Typeclass(tc_id)) => {
                        // Check if the output is just the bound variable (x_depth).
                        // This means the function returns a value of the typeclass-constrained type,
                        // proving that the typeclass makes its instance type inhabited.
                        // For example: point: forall[P: Pointed]. P has type Pi(Typeclass(Pointed), x0)
                        let output_var = if output.is_atomic() {
                            match output.get_head_atom() {
                                Atom::FreeVariable(i) | Atom::BoundVariable(i) => Some(*i),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        if output_var == Some(depth) {
                            self.inhabited_typeclasses.insert(*tc_id);
                            self.inhabited_typeclass_witnesses
                                .entry(*tc_id)
                                .or_insert(symbol);
                        }
                        current = output;
                        depth += 1;
                        continue;
                    }
                    _ => {}
                }
            }
            break;
        }

        // Prefer providers that can produce a value without additional value-level arguments.
        // If `current` is still a Pi here, the symbol requires value arguments.
        let has_value_args = current.split_pi().is_some();

        // Track the eventual codomain after all remaining (value-level) Pi binders.
        // This lets us use constructor-like symbols with value arguments as inhabitant providers,
        // e.g. `Subgroup.new : (G -> Bool) -> Subgroup[G]`.
        let mut result = current;
        while let Some((_input, output)) = result.split_pi() {
            result = output;
        }
        if depth > 0 && matches!(result.get_head_atom(), Atom::Symbol(Symbol::Type(_))) {
            let Atom::Symbol(Symbol::Type(ground_id)) = result.get_head_atom() else {
                unreachable!()
            };
            self.inhabited_type_constructors.insert(*ground_id);
            let existing = self
                .inhabited_type_constructor_witnesses
                .get(ground_id)
                .copied();
            let replace = match existing {
                None => true,
                Some(existing_symbol) => {
                    if matches!(symbol, Symbol::Synthetic(_, _))
                        && !matches!(existing_symbol, Symbol::Synthetic(_, _))
                    {
                        // Don't let provisional synthetics replace a concrete provider.
                        false
                    } else {
                        // Prefer providers that don't require value-level arguments.
                        !has_value_args
                    }
                }
            };
            if replace {
                self.inhabited_type_constructor_witnesses
                    .insert(*ground_id, symbol);
            }
        }
    }

    /// Check if a type constructor is known to be inhabited for any type arguments.
    pub fn is_type_constructor_inhabited(&self, ground_id: GroundTypeId) -> bool {
        self.inhabited_type_constructors.contains(&ground_id)
    }

    /// Get a witness-provider symbol for an inhabited type constructor.
    pub fn get_type_constructor_witness(&self, ground_id: GroundTypeId) -> Option<Symbol> {
        self.inhabited_type_constructor_witnesses
            .get(&ground_id)
            .copied()
    }

    /// Check if a typeclass is known to provide inhabitants for its instance types.
    pub fn is_typeclass_inhabited(&self, tc_id: TypeclassId) -> bool {
        self.inhabited_typeclasses.contains(&tc_id)
    }

    /// Get a witness-provider symbol for an inhabited typeclass.
    pub fn get_typeclass_witness(&self, tc_id: TypeclassId) -> Option<Symbol> {
        self.inhabited_typeclass_witnesses.get(&tc_id).copied()
    }

    /// Mark a typeclass as providing inhabitants for its instance types.
    pub fn mark_typeclass_inhabited(&mut self, tc_id: TypeclassId) {
        self.inhabited_typeclasses.insert(tc_id);
    }

    /// Get a symbol of a particular type, if one has been registered.
    pub fn get_element_of_type(&self, var_type: &Term) -> Option<Symbol> {
        self.type_to_element.get(var_type).copied()
    }

    pub fn get_symbol(&self, name: &ConstantName) -> Option<Symbol> {
        if let ConstantName::Synthetic(m, i) = name {
            return Some(Symbol::Synthetic(*m, *i));
        };
        self.name_to_symbol.get(name).cloned()
    }

    /// Get polymorphic info for a constant, if it's polymorphic.
    pub fn get_polymorphic_info(&self, name: &ConstantName) -> Option<&PolymorphicInfo> {
        self.polymorphic_info.get(name)
    }

    /// Get match-eliminator metadata for a datatype `match` constant, if known.
    pub fn get_match_eliminator_info(&self, match_symbol: Symbol) -> Option<&MatchEliminatorInfo> {
        self.match_eliminator_info.get(&match_symbol)
    }

    /// Get the type of a symbol.
    /// For Symbol::Type and built-in type symbols, this returns the Type kind (arity 0).
    /// Use get_symbol_type() with a TypeStore if you need proper kinds for type constructors.
    pub fn get_type(&self, symbol: Symbol) -> &Term {
        match symbol {
            Symbol::True | Symbol::False => Term::bool_type_ref(),
            Symbol::Not => not_symbol_type_ref(),
            Symbol::And | Symbol::Or => bool_binary_symbol_type_ref(),
            Symbol::Eq => eq_symbol_type_ref(),
            Symbol::Ite => ite_symbol_type_ref(),
            Symbol::Choose => choose_symbol_type_ref(),
            Symbol::Bool | Symbol::Type0 | Symbol::Type(_) | Symbol::Typeclass(_) => {
                Term::type_sort_ref()
            }
            Symbol::Synthetic(m, i) => &self.synthetic_types[m.get() as usize][i as usize],
            Symbol::GlobalConstant(m, i) => {
                &self.global_constant_types[m.get() as usize][i as usize]
            }
            Symbol::ScopedConstant(i) => &self.scoped_constant_types[i as usize],
        }
    }

    /// Get the type of a symbol, with proper kinds for type symbols.
    /// For Symbol::Type, this returns the proper kind based on arity (e.g., Type -> Type for List).
    pub fn get_symbol_type(&self, symbol: Symbol, type_store: &TypeStore) -> Term {
        let result = match symbol {
            Symbol::True | Symbol::False => Term::bool_type(),
            Symbol::Not => not_symbol_type_ref().clone(),
            Symbol::And | Symbol::Or => bool_binary_symbol_type_ref().clone(),
            Symbol::Eq => eq_symbol_type_ref().clone(),
            Symbol::Ite => ite_symbol_type_ref().clone(),
            Symbol::Choose => choose_symbol_type_ref().clone(),
            Symbol::Bool | Symbol::Type0 | Symbol::Typeclass(_) => Term::type_sort(),
            Symbol::Type(ground_id) => type_store.get_type_kind(ground_id),
            Symbol::Synthetic(m, i) => self.synthetic_types[m.get() as usize][i as usize].clone(),
            Symbol::GlobalConstant(m, i) => {
                self.global_constant_types[m.get() as usize][i as usize].clone()
            }
            Symbol::ScopedConstant(i) => self.scoped_constant_types[i as usize].clone(),
        };
        result.validate();
        result
    }

    /// Get the count of scoped constants for debugging.
    #[cfg(test)]
    pub fn scoped_constant_count(&self) -> usize {
        self.scoped_constant_types.len()
    }

    /// Get the number of scoped constants.
    #[cfg(test)]
    pub fn num_scoped_constants(&self) -> u32 {
        self.scoped_constant_types.len() as u32
    }

    /// Set the type for a scoped constant at a given index.
    #[cfg(test)]
    pub fn set_scoped_constant_type(&mut self, id: u32, var_type: Term) {
        self.scoped_constant_types[id as usize] = var_type;
    }

    /// Get the number of global constants in module 0 (for tests).
    #[cfg(test)]
    pub fn num_global_constants(&self) -> u32 {
        self.global_constant_types
            .front()
            .map(|v| v.len())
            .unwrap_or(0) as u32
    }

    /// Set the type for a global constant at a given index in module 0 (for tests).
    #[cfg(test)]
    pub fn set_global_constant_type(&mut self, id: u32, var_type: Term) {
        self.ensure_module_exists(ModuleId(0));
        self.global_constant_types[0][id as usize] = var_type;
    }

    /// Ensure the storage vectors are large enough for the given module_id.
    fn ensure_module_exists(&mut self, module_id: ModuleId) {
        let idx = module_id.get() as usize;
        while self.global_constants.len() <= idx {
            self.global_constants.push_back(ImVector::new());
        }
        while self.global_constant_types.len() <= idx {
            self.global_constant_types.push_back(ImVector::new());
        }
        while self.synthetic_types.len() <= idx {
            self.synthetic_types.push_back(ImVector::new());
        }
    }

    /// Get the number of synthetics.
    #[cfg(test)]
    pub fn num_synthetics(&self) -> u32 {
        self.synthetic_types.front().map(|v| v.len()).unwrap_or(0) as u32
    }

    /// Set the type for a synthetic at a given index in module 0 (for tests).
    #[cfg(test)]
    pub fn set_synthetic_type(&mut self, id: u32, var_type: Term) {
        #[cfg(any(test, feature = "validate"))]
        if var_type.has_free_variable() {
            panic!(
                "Symbol type contains free variable: {}. \
                 Symbol types should use BoundVariable for parameters bound by Pi.",
                var_type
            );
        }
        self.ensure_module_exists(ModuleId(0));
        self.synthetic_types[0][id as usize] = var_type;
    }

    /// Declare a new synthetic atom with the given type.
    /// The module_id identifies which module's normalization is creating this synthetic.
    pub fn declare_synthetic(&mut self, module_id: ModuleId, var_type: Term) -> Symbol {
        // Symbol types should be closed - no free variables allowed.
        // Free variables in a type like Π(T, x0) indicate a bug where BoundVariable
        // should have been used instead.
        #[cfg(any(test, feature = "validate"))]
        if var_type.has_free_variable() {
            panic!(
                "Symbol type contains free variable: {}. \
                 Symbol types should use BoundVariable for parameters bound by Pi.",
                var_type
            );
        }

        self.ensure_module_exists(module_id);
        let idx = module_id.get() as usize;
        let atom_id = self.synthetic_types[idx].len() as AtomId;
        let symbol = Symbol::Synthetic(module_id, atom_id);
        self.record_element(var_type.clone(), symbol);
        self.synthetic_types[idx].push_back(var_type);
        symbol
    }

    /// Add a scoped constant with the given type, without a name.
    /// Returns the Symbol for the new constant.
    /// Primarily for testing with parsed terms like "c0", "c1".
    #[cfg(test)]
    pub fn add_scoped_constant(&mut self, var_type: Term) -> Symbol {
        let atom_id = self.scoped_constant_types.len() as AtomId;
        let symbol = Symbol::ScopedConstant(atom_id);
        self.record_element(var_type.clone(), symbol);
        self.scoped_constants.push_back(None);
        self.scoped_constant_types.push_back(var_type);
        symbol
    }

    /// Add a global constant with the given type, without a name.
    /// Returns the Symbol for the new constant.
    /// Primarily for testing with parsed terms like "g0_0", "g0_1".
    /// Uses ModuleId(0) for all test constants.
    #[cfg(test)]
    pub fn add_global_constant(&mut self, var_type: Term) -> Symbol {
        let module_id = ModuleId(0);
        self.ensure_module_exists(module_id);
        let idx = module_id.get() as usize;
        let atom_id = self.global_constant_types[idx].len() as AtomId;
        let symbol = Symbol::GlobalConstant(module_id, atom_id);
        self.record_element(var_type.clone(), symbol);
        self.global_constants[idx].push_back(None);
        self.global_constant_types[idx].push_back(var_type);
        symbol
    }

    /// Assigns an id to this (module, name) pair if it doesn't already have one.
    /// local determines whether the constant will be represented as a local or global symbol.
    pub fn add_constant(
        &mut self,
        name: ConstantName,
        ctype: NewConstantType,
        var_type: Term,
    ) -> Symbol {
        if name.is_synthetic() {
            panic!("synthetic atoms should not be stored in the ConstantMap");
        }
        if let Some(&symbol) = self.name_to_symbol.get(&name) {
            return symbol;
        }
        let symbol = match ctype {
            NewConstantType::Local => {
                let atom_id = self.scoped_constant_types.len() as AtomId;
                self.scoped_constants.push_back(Some(name.clone()));
                self.scoped_constant_types.push_back(var_type.clone());
                Symbol::ScopedConstant(atom_id)
            }
            NewConstantType::Global => {
                let module_id = name.module_id();
                self.ensure_module_exists(module_id);
                let idx = module_id.get() as usize;
                let atom_id = self.global_constant_types[idx].len() as AtomId;
                self.global_constants[idx].push_back(Some(name.clone()));
                self.global_constant_types[idx].push_back(var_type.clone());
                Symbol::GlobalConstant(module_id, atom_id)
            }
        };
        self.record_element(var_type, symbol);
        self.name_to_symbol.insert(name, symbol);
        symbol
    }

    /// Add all constant names and types from a value to the symbol table.
    /// Polymorphic constants get Pi-wrapped types for dependent type representation.
    pub fn add_from(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        type_store: &mut TypeStore,
    ) {
        use crate::elaborator::acorn_type::{AcornType, TypeParam};

        // Add all types first, so they can be resolved to type Terms
        value.for_each_type(&mut |t| {
            type_store.add_type(t);
        });

        // Now add all constants (types are now registered)
        value.for_each_constant(&mut |c| {
            if self.get_symbol(&c.name).is_none() {
                // A constant is polymorphic if:
                // - type_param_names is non-empty (the constant definition has type parameters)
                // - params is non-empty (this is an instance of a polymorphic constant)
                let is_polymorphic = !c.type_param_names.is_empty() || !c.params.is_empty();
                let var_type = if !is_polymorphic {
                    // Non-polymorphic: use instance_type directly
                    type_store
                        .get_type_term(&c.instance_type)
                        .expect("type should be valid")
                } else {
                    // Polymorphic: compute the polymorphic type term.
                    //
                    // Extract type params. Priority:
                    // 1. If type_param_names is provided, extract TypeParams from generic_type
                    //    using those names (to get typeclass constraints)
                    // 2. Otherwise, extract from generic_type (Variable types)
                    let type_params: Vec<TypeParam> = {
                        struct NoContext;
                        impl crate::elaborator::error::ErrorContext for NoContext {
                            fn error(&self, msg: &str) -> crate::elaborator::error::Error {
                                let empty_token = crate::syntax::token::Token::empty();
                                crate::elaborator::error::Error::new(
                                    &empty_token,
                                    &empty_token,
                                    msg,
                                )
                            }
                        }
                        let mut vars = std::collections::HashMap::new();
                        let _ = c.generic_type.find_type_vars(&mut vars, &NoContext);

                        if !c.type_param_names.is_empty() {
                            // Use provided order, but get typeclass info from vars if available
                            c.type_param_names
                                .iter()
                                .map(|name| {
                                    vars.get(name).cloned().unwrap_or_else(|| TypeParam {
                                        name: name.clone(),
                                        typeclass: None,
                                    })
                                })
                                .collect()
                        } else {
                            // Sort by name for consistency
                            let mut params: Vec<_> = vars.values().cloned().collect();
                            params.sort_by(|a, b| a.name.cmp(&b.name));
                            params
                        }
                    };

                    let variable_params: Vec<AcornType> = type_params
                        .iter()
                        .map(|p| AcornType::Variable(p.clone()))
                        .collect();

                    // Use generic_type which should have Variable types for polymorphic constants
                    let type_for_term = c.generic_type.clone();

                    // Convert to a term with bound variables
                    let body_type =
                        type_store.to_polymorphic_type_term(&type_for_term, &variable_params);

                    // Wrap in Pi for each type parameter (from outermost to innermost).
                    // Use Pi(Typeclass, ...) for constrained params, Pi(Type, ...) for unconstrained.
                    let mut result = body_type;
                    for param in type_params.iter().rev() {
                        let input_type = if let Some(tc) = &param.typeclass {
                            let tc_id = type_store.add_typeclass(tc);
                            Term::typeclass(tc_id)
                        } else {
                            Term::type_sort()
                        };
                        result = Term::pi(input_type, result);
                    }
                    result
                };
                let _symbol = self.add_constant(c.name.clone(), ctype, var_type.clone());

                // Store polymorphic info for later use in denormalization
                if is_polymorphic {
                    // Determine type param names (use provided or extract from generic_type)
                    let type_param_names: Vec<String> = if !c.type_param_names.is_empty() {
                        c.type_param_names.clone()
                    } else {
                        // Extract variable names from generic_type
                        struct NoContext;
                        impl crate::elaborator::error::ErrorContext for NoContext {
                            fn error(&self, msg: &str) -> crate::elaborator::error::Error {
                                let empty_token = crate::syntax::token::Token::empty();
                                crate::elaborator::error::Error::new(
                                    &empty_token,
                                    &empty_token,
                                    msg,
                                )
                            }
                        }
                        let mut vars = std::collections::HashMap::new();
                        let _ = c.generic_type.find_type_vars(&mut vars, &NoContext);
                        let mut names: Vec<_> = vars.keys().cloned().collect();
                        names.sort();
                        names
                    };

                    // Convert Arbitrary types to Variable types in generic_type
                    // The ConstantInstance we're visiting may have Arbitrary types,
                    // but we need Variable types for proper instantiation.
                    let params_for_genericize: Vec<TypeParam> = type_param_names
                        .iter()
                        .map(|name| TypeParam {
                            name: name.clone(),
                            typeclass: None,
                        })
                        .collect();
                    let generic_type_with_variables =
                        c.generic_type.genericize(&params_for_genericize);

                    self.polymorphic_info.insert(
                        c.name.clone(),
                        PolymorphicInfo {
                            generic_type: generic_type_with_variables,
                            type_param_names,
                        },
                    );
                }
            }
        });

        // Match expressions lower to datatype eliminator symbols (`Type.match`) in term elaboration.
        // Legacy normalization handled Match directly and didn't need these symbols registered.
        // Register them here so bridge-mode elaboration can always resolve them.
        fn replace_type_args_with_params(
            ty: &AcornType,
            concrete_type_args: &[AcornType],
            type_params: &[TypeParam],
        ) -> AcornType {
            for (i, concrete) in concrete_type_args.iter().enumerate() {
                if ty == concrete {
                    return AcornType::Variable(type_params[i].clone());
                }
            }
            match ty {
                AcornType::Function(ftype) => AcornType::functional(
                    ftype
                        .arg_types
                        .iter()
                        .map(|arg| {
                            replace_type_args_with_params(arg, concrete_type_args, type_params)
                        })
                        .collect(),
                    replace_type_args_with_params(
                        &ftype.return_type,
                        concrete_type_args,
                        type_params,
                    ),
                ),
                AcornType::Data(datatype, args) => AcornType::Data(
                    datatype.clone(),
                    args.iter()
                        .map(|arg| {
                            replace_type_args_with_params(arg, concrete_type_args, type_params)
                        })
                        .collect(),
                ),
                _ => ty.clone(),
            }
        }

        fn register_match_symbols_for_value(
            symbol_table: &mut SymbolTable,
            type_store: &mut TypeStore,
            value: &AcornValue,
        ) {
            match value {
                AcornValue::Match(scrutinee, cases) => {
                    if let AcornType::Data(datatype, concrete_type_args) = scrutinee.get_type() {
                        let match_name = ConstantName::datatype_attr(
                            datatype.module_id,
                            datatype.clone(),
                            "match",
                        );
                        let mut sorted_cases = cases.clone();
                        sorted_cases.sort_by_key(|case| case.constructor_index);

                        let match_symbol = if let Some(symbol) =
                            symbol_table.get_symbol(&match_name)
                        {
                            symbol
                        } else {
                            let type_params: Vec<TypeParam> = concrete_type_args
                                .iter()
                                .enumerate()
                                .map(|(i, _)| TypeParam {
                                    name: format!("T{}", i),
                                    typeclass: None,
                                })
                                .collect();
                            let result_param = TypeParam {
                                name: "R".to_string(),
                                typeclass: None,
                            };

                            let generic_datatype_args: Vec<AcornType> = type_params
                                .iter()
                                .map(|param| AcornType::Variable(param.clone()))
                                .collect();
                            let generic_scrutinee_type =
                                AcornType::Data(datatype.clone(), generic_datatype_args);
                            let generic_result_type = AcornType::Variable(result_param.clone());

                            let mut generic_match_arg_types = vec![generic_scrutinee_type];
                            for case in &sorted_cases {
                                let generic_case_args: Vec<AcornType> = case
                                    .new_vars
                                    .iter()
                                    .map(|arg_type| {
                                        replace_type_args_with_params(
                                            arg_type,
                                            &concrete_type_args,
                                            &type_params,
                                        )
                                    })
                                    .collect();
                                generic_match_arg_types.push(AcornType::functional(
                                    generic_case_args,
                                    generic_result_type.clone(),
                                ));
                            }

                            let generic_match_type = AcornType::functional(
                                generic_match_arg_types,
                                generic_result_type.clone(),
                            );
                            type_store.add_type(&generic_match_type);

                            let mut all_params = type_params.clone();
                            all_params.push(result_param);
                            let variable_params: Vec<AcornType> = all_params
                                .iter()
                                .map(|param| AcornType::Variable(param.clone()))
                                .collect();
                            let body_type = type_store
                                .to_polymorphic_type_term(&generic_match_type, &variable_params);
                            let mut symbol_type = body_type;
                            for _ in all_params.iter().rev() {
                                symbol_type = Term::pi(Term::type_sort(), symbol_type);
                            }

                            let symbol = symbol_table.add_constant(
                                match_name.clone(),
                                NewConstantType::Global,
                                symbol_type,
                            );
                            symbol_table.polymorphic_info.insert(
                                match_name,
                                PolymorphicInfo {
                                    generic_type: generic_match_type,
                                    type_param_names: all_params
                                        .iter()
                                        .map(|param| param.name.clone())
                                        .collect(),
                                },
                            );
                            symbol
                        };

                        // Record constructor-order metadata for denormalizing Type.match back
                        // into AcornValue::Match. Store kernel symbols (not names).
                        if let Some(constructor_symbols) = sorted_cases
                            .iter()
                            .map(|case| match case.pattern.unapply() {
                                AcornValue::Constant(c) => symbol_table.get_symbol(&c.name),
                                _ => None,
                            })
                            .collect::<Option<Vec<_>>>()
                        {
                            symbol_table
                                .match_eliminator_info
                                .entry(match_symbol)
                                .or_insert(MatchEliminatorInfo {
                                    constructor_symbols,
                                });
                        }
                    }

                    register_match_symbols_for_value(symbol_table, type_store, scrutinee);
                    for case in cases {
                        register_match_symbols_for_value(symbol_table, type_store, &case.pattern);
                        register_match_symbols_for_value(symbol_table, type_store, &case.result);
                    }
                }
                AcornValue::Application(app) => {
                    register_match_symbols_for_value(symbol_table, type_store, &app.function);
                    for arg in &app.args {
                        register_match_symbols_for_value(symbol_table, type_store, arg);
                    }
                }
                AcornValue::TypeApplication(app) => {
                    register_match_symbols_for_value(symbol_table, type_store, &app.function);
                }
                AcornValue::Lambda(_, subvalue)
                | AcornValue::ForAll(_, subvalue)
                | AcornValue::Exists(_, subvalue)
                | AcornValue::Choose(_, subvalue)
                | AcornValue::Not(subvalue)
                | AcornValue::Try(subvalue, _) => {
                    register_match_symbols_for_value(symbol_table, type_store, subvalue);
                }
                AcornValue::Binary(_, left, right) => {
                    register_match_symbols_for_value(symbol_table, type_store, left);
                    register_match_symbols_for_value(symbol_table, type_store, right);
                }
                AcornValue::IfThenElse(cond, then_value, else_value) => {
                    register_match_symbols_for_value(symbol_table, type_store, cond);
                    register_match_symbols_for_value(symbol_table, type_store, then_value);
                    register_match_symbols_for_value(symbol_table, type_store, else_value);
                }
                AcornValue::Variable(..) | AcornValue::Constant(..) | AcornValue::Bool(..) => {}
            }
        }

        register_match_symbols_for_value(self, type_store, value);
    }

    /// Get the name corresponding to a particular global (ModuleId, AtomId).
    pub fn name_for_global_id(&self, module_id: ModuleId, atom_id: AtomId) -> &ConstantName {
        self.global_constants[module_id.get() as usize][atom_id as usize]
            .as_ref()
            .unwrap()
    }

    /// Get the name corresponding to a particular local AtomId.
    pub fn name_for_local_id(&self, atom_id: AtomId) -> &ConstantName {
        &self.scoped_constants[atom_id as usize].as_ref().unwrap()
    }

    /// Make this constant instance an alias for the given name.
    /// If neither of the names map to anything, we create a new entry.
    /// This is rare but can happen if we're aliasing something that was structurally generated.
    pub fn alias_instance(
        &mut self,
        c: ConstantInstance,
        name: &ConstantName,
        constant_type: &AcornType,
        local: bool,
        type_store: &mut TypeStore,
    ) {
        // Register the type first so we can get its type Term
        type_store.add_type(constant_type);
        let var_type = type_store
            .get_type_term(constant_type)
            .expect("type should be valid");
        let ctype = if local {
            NewConstantType::Local
        } else {
            NewConstantType::Global
        };
        let symbol = self.add_constant(name.clone(), ctype, var_type);
        self.instance_to_symbol.insert(c, symbol);
    }

    /// Build a term application for a polymorphic constant.
    /// E.g., for add[Int], builds add(Int) with the type argument applied.
    /// However, if the constant has an alias (via alias_instance), use that instead.
    pub fn term_from_instance(
        &self,
        c: &ConstantInstance,
        type_store: &TypeStore,
    ) -> Result<Term, String> {
        self.term_from_instance_with_vars(c, type_store, None)
    }

    pub fn term_from_instance_with_vars(
        &self,
        c: &ConstantInstance,
        type_store: &TypeStore,
        type_var_map: Option<&StdHashMap<String, (AtomId, Term)>>,
    ) -> Result<Term, String> {
        // Check for an alias first - instance definitions create aliases
        // where Arf.foo[Foo] = Foo.foo makes them the same symbol
        if let Some(&symbol) = self.instance_to_symbol.get(c) {
            return Ok(Term::atom(Atom::Symbol(symbol)));
        }

        // Get the base constant symbol
        let Some(base_symbol) = self.get_symbol(&c.name) else {
            return Err(format!("Base constant {} not found", c.name));
        };

        if c.params.is_empty() {
            // No type params, just return the base symbol
            return Ok(Term::atom(Atom::Symbol(base_symbol)));
        }

        // Convert type params to Terms
        let type_args: Vec<Term> = c
            .params
            .iter()
            .map(|param| type_store.to_type_term_with_vars(param, type_var_map))
            .collect();

        // Build application: base(type_arg1, type_arg2, ...)
        let head = Term::atom(Atom::Symbol(base_symbol));
        Ok(head.apply(&type_args))
    }

    /// Merges another SymbolTable into this one.
    /// Entries from `other` are added to `self`.
    pub fn merge(&mut self, other: &SymbolTable) {
        // Merge global constants and their types
        merge_nested_vecs(&mut self.global_constants, &other.global_constants);
        merge_nested_vecs(
            &mut self.global_constant_types,
            &other.global_constant_types,
        );

        // Merge scoped constants
        merge_vec(&mut self.scoped_constants, &other.scoped_constants);
        merge_vec(
            &mut self.scoped_constant_types,
            &other.scoped_constant_types,
        );

        // Merge synthetic types
        merge_nested_vecs(&mut self.synthetic_types, &other.synthetic_types);

        // Merge hash maps
        for (k, v) in other.name_to_symbol.iter() {
            self.name_to_symbol.insert(k.clone(), *v);
        }
        for (k, v) in other.instance_to_symbol.iter() {
            self.instance_to_symbol.insert(k.clone(), *v);
        }
        for (k, v) in other.polymorphic_info.iter() {
            self.polymorphic_info.insert(k.clone(), v.clone());
        }
        for (k, v) in other.match_eliminator_info.iter() {
            self.match_eliminator_info.insert(k.clone(), v.clone());
        }
        for (k, v) in other.type_to_element.iter() {
            // Only insert if not already present (first registered wins)
            if !self.type_to_element.contains_key(k) {
                self.type_to_element.insert(k.clone(), *v);
            }
        }

        // Merge inhabited sets
        for id in other.inhabited_type_constructors.iter() {
            self.inhabited_type_constructors.insert(*id);
        }
        for (ground_id, symbol) in other.inhabited_type_constructor_witnesses.iter() {
            if !self
                .inhabited_type_constructor_witnesses
                .contains_key(ground_id)
            {
                self.inhabited_type_constructor_witnesses
                    .insert(*ground_id, *symbol);
            }
        }
        for id in other.inhabited_typeclasses.iter() {
            self.inhabited_typeclasses.insert(*id);
        }
        for (tc_id, symbol) in other.inhabited_typeclass_witnesses.iter() {
            if !self.inhabited_typeclass_witnesses.contains_key(tc_id) {
                self.inhabited_typeclass_witnesses.insert(*tc_id, *symbol);
            }
        }
    }

    /// Merges another SymbolTable into this one, excluding scoped constants.
    /// This is intended for merging import state only.
    pub fn merge_imports(&mut self, other: &SymbolTable) {
        // Merge global constants and their types
        merge_nested_vecs(&mut self.global_constants, &other.global_constants);
        merge_nested_vecs(
            &mut self.global_constant_types,
            &other.global_constant_types,
        );

        // Skip scoped constants (locals are not mergeable across modules)

        // Merge synthetic types
        merge_nested_vecs(&mut self.synthetic_types, &other.synthetic_types);

        // Merge hash maps
        for (k, v) in other.name_to_symbol.iter() {
            self.name_to_symbol.insert(k.clone(), *v);
        }
        for (k, v) in other.instance_to_symbol.iter() {
            self.instance_to_symbol.insert(k.clone(), *v);
        }
        for (k, v) in other.polymorphic_info.iter() {
            self.polymorphic_info.insert(k.clone(), v.clone());
        }
        for (k, v) in other.match_eliminator_info.iter() {
            self.match_eliminator_info.insert(k.clone(), v.clone());
        }
        for (k, v) in other.type_to_element.iter() {
            if !self.type_to_element.contains_key(k) {
                self.type_to_element.insert(k.clone(), *v);
            }
        }

        // Merge inhabited sets
        for id in other.inhabited_type_constructors.iter() {
            self.inhabited_type_constructors.insert(*id);
        }
        for (ground_id, symbol) in other.inhabited_type_constructor_witnesses.iter() {
            if !self
                .inhabited_type_constructor_witnesses
                .contains_key(ground_id)
            {
                self.inhabited_type_constructor_witnesses
                    .insert(*ground_id, *symbol);
            }
        }
        for id in other.inhabited_typeclasses.iter() {
            self.inhabited_typeclasses.insert(*id);
        }
        for (tc_id, symbol) in other.inhabited_typeclass_witnesses.iter() {
            if !self.inhabited_typeclass_witnesses.contains_key(tc_id) {
                self.inhabited_typeclass_witnesses.insert(*tc_id, *symbol);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_type_element_tracks_synthetics() {
        let mut table = SymbolTable::new();
        let bool_type = Term::bool_type();

        let synthetic = table.declare_synthetic(ModuleId(0), bool_type.clone());
        assert_eq!(table.get_element_of_type(&bool_type), Some(synthetic));
    }
}

/// Merge entries from `source` into `target`, extending as needed.
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
