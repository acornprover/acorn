use crate::kernel::atom::Atom;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::SymbolTable;
use crate::kernel::term::Term;
use crate::kernel::type_store::TypeStore;
#[cfg(test)]
use crate::module::ModuleId;

/// KernelContext combines the TypeStore and SymbolTable that are needed
/// for working with kernel types and various kernel operations.
#[derive(Clone)]
pub struct KernelContext {
    pub type_store: TypeStore,
    pub symbol_table: SymbolTable,
}

impl KernelContext {
    pub fn new() -> KernelContext {
        KernelContext {
            type_store: TypeStore::new(),
            symbol_table: SymbolTable::new(),
        }
    }

    /// Returns a human-readable string representation of an atom.
    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::Symbol(Symbol::True) => "true".to_string(),
            Atom::Symbol(Symbol::False) => "false".to_string(),
            Atom::Symbol(Symbol::Empty) => "Empty".to_string(),
            Atom::Symbol(Symbol::Bool) => "Bool".to_string(),
            Atom::Symbol(Symbol::Type0) => "Type".to_string(),
            Atom::Symbol(Symbol::GlobalConstant(m, i)) => {
                self.symbol_table.name_for_global_id(*m, *i).to_string()
            }
            Atom::Symbol(Symbol::ScopedConstant(i)) => {
                self.symbol_table.name_for_local_id(*i).to_string()
            }
            Atom::FreeVariable(i) => format!("x{}", i),
            Atom::BoundVariable(i) => format!("b{}", i),
            Atom::Symbol(Symbol::Synthetic(m, i)) => format!("s{}_{}", m.0, i),
            Atom::Symbol(Symbol::Type(t)) => {
                format!("T{}_{}", t.module_id().get(), t.local_id())
            }
            Atom::Symbol(Symbol::Typeclass(tc)) => {
                let typeclass = self.type_store.get_typeclass(*tc);
                typeclass.name.clone()
            }
        }
    }

    /// Returns true if we've proven that the given type has at least one element.
    /// This is a conservative check - it may return false for types that are inhabited
    /// but where we haven't explicitly registered an inhabitant.
    ///
    /// The optional `local_context` parameter is used in polymorphic mode to look up
    /// constraints on type variables (e.g., to determine that P: Pointed is inhabited).
    pub fn provably_inhabited(
        &self,
        var_type: &Term,
        local_context: Option<&LocalContext>,
    ) -> bool {
        // Check for function types first.
        // A function type A -> B is inhabited if:
        // 1. The codomain B is inhabited (we can create a constant function), OR
        // 2. The domain A equals the codomain B (the identity function exists)
        if let Some((domain, codomain)) = var_type.as_ref().split_pi() {
            // For non-dependent function types, check if domain equals codomain.
            // Due to de Bruijn indexing, the codomain is inside the Pi's scope,
            // so we need to shift it down by 1 to compare with the domain.
            // For example, T -> T is represented as Pi(b0, b1) where both refer to
            // the same outer binding, but b1 is shifted because it's inside the Pi.
            let codomain_term = codomain.to_owned();
            let shifted_codomain = codomain_term.shift_bound(0, -1);
            if domain.to_owned() == shifted_codomain {
                // Identity function always exists: T -> T is inhabited for any T
                return true;
            }
            // When recursing on the codomain, use the shifted version so indices
            // align with the context (which doesn't include the Pi's binding)
            return self.provably_inhabited(&shifted_codomain, local_context);
        }

        // In polymorphic mode, check if this is a type variable with a constraint.
        // For example, if var_type is FreeVariable(0) or BoundVariable(0) representing P: Pointed,
        // look up the constraint (Pointed) in the local context.
        let var_type_ref = var_type.as_ref();
        if var_type_ref.is_atomic() {
            let var_id = match var_type_ref.get_head_atom() {
                Atom::FreeVariable(id) => Some(*id),
                Atom::BoundVariable(id) => Some(*id),
                _ => None,
            };
            if let Some(var_id) = var_id {
                if let Some(ctx) = local_context {
                    if let Some(constraint_type) = ctx.get_var_type(var_id as usize) {
                        // If the constraint is TypeSort, this is an unconstrained type variable.
                        // Unconstrained types are NOT provably inhabited (could be empty).
                        if constraint_type.as_ref().is_type0() {
                            return false;
                        }
                        return self.provably_inhabited(constraint_type, local_context);
                    }
                }
            }
        }

        match var_type.as_ref().get_head_atom() {
            // Bool is inhabited (true, false)
            Atom::Symbol(Symbol::Bool) => return true,

            // TypeSort is inhabited (any type can be used as a value of type Type)
            Atom::Symbol(Symbol::Type0) => return true,

            // Check if the type's head is a type constructor known to be inhabited.
            // For example, List[T] is inhabited if we have nil: forall[T]. List[T].
            Atom::Symbol(Symbol::Type(ground_id)) => {
                if self.symbol_table.is_type_constructor_inhabited(*ground_id) {
                    return true;
                }
                // In non-polymorphic mode, check if this ground type is an arbitrary type
                // with a typeclass constraint that makes it inhabited.
                if let Some(tc_id) = self.type_store.get_arbitrary_typeclass(*ground_id) {
                    if self.symbol_table.is_typeclass_inhabited(tc_id) {
                        return true;
                    }
                    // Also check if this typeclass extends a typeclass that provides inhabitants.
                    for base_id in self.type_store.get_typeclass_extends(tc_id) {
                        if self.symbol_table.is_typeclass_inhabited(base_id) {
                            return true;
                        }
                    }
                }
            }

            // Check if this is a typeclass-constrained type variable.
            // For example, P: Pointed is inhabited if Pointed has a constant like point: P.
            Atom::Symbol(Symbol::Typeclass(tc_id)) => {
                if self.symbol_table.is_typeclass_inhabited(*tc_id) {
                    return true;
                }
                // Also check if this typeclass extends a typeclass that provides inhabitants.
                for base_id in self.type_store.get_typeclass_extends(*tc_id) {
                    if self.symbol_table.is_typeclass_inhabited(base_id) {
                        return true;
                    }
                }
            }

            _ => {}
        }

        // Check for an exact type match
        if self.symbol_table.get_element_of_type(var_type).is_some() {
            return true;
        }

        false
    }

    /// Creates a test KernelContext with pre-populated scoped constants (c0, c1, ..., c{n-1})
    /// all with EMPTY type. For use in tests that parse terms like "c0(x0)".
    #[cfg(test)]
    pub fn test_with_scoped_constants(n: usize) -> KernelContext {
        let mut ctx = KernelContext::new();
        for _ in 0..n {
            ctx.symbol_table.add_scoped_constant(Term::empty_type());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants (c0, c1, ..., c{n-1})
    /// all with Bool type. For use in tests that need Bool-typed constants.
    #[cfg(test)]
    pub fn test_with_bool_scoped_constants(n: usize) -> KernelContext {
        let mut ctx = KernelContext::new();
        for _ in 0..n {
            ctx.symbol_table.add_scoped_constant(Term::bool_type());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants with specified types.
    #[cfg(test)]
    pub fn test_with_scoped_constant_types(types: &[Term]) -> KernelContext {
        let mut ctx = KernelContext::new();
        for type_term in types {
            ctx.symbol_table.add_scoped_constant(type_term.clone());
        }
        ctx
    }

    /// Creates a test KernelContext with pre-populated scoped constants, global constants,
    /// and synthetics. All types will be EMPTY.
    /// For use in tests that parse terms like "c0", "g0", "s0".
    #[cfg(test)]
    pub fn test_with_constants(num_scoped: usize, num_global: usize) -> KernelContext {
        let mut ctx = KernelContext::new();
        for _ in 0..num_scoped {
            ctx.symbol_table.add_scoped_constant(Term::empty_type());
        }
        for _ in 0..num_global {
            ctx.symbol_table.add_global_constant(Term::empty_type());
        }
        // Also add synthetics for tests that use "s0_0", "s0_1", etc.
        for _ in 0..10 {
            ctx.symbol_table
                .declare_synthetic(ModuleId(0), Term::empty_type());
        }
        ctx
    }

    /// Creates a test KernelContext with all symbol types populated with specified types.
    /// Arrays are indexed by atom id, e.g., synthetic_types[2] gives type for Synthetic(2).
    #[cfg(test)]
    pub fn test_with_all_types(
        scoped_types: &[Term],
        global_types: &[Term],
        synthetic_types: &[Term],
    ) -> KernelContext {
        let mut ctx = KernelContext::new();
        for type_term in scoped_types {
            ctx.symbol_table.add_scoped_constant(type_term.clone());
        }
        for type_term in global_types {
            ctx.symbol_table.add_global_constant(type_term.clone());
        }
        for type_term in synthetic_types {
            ctx.symbol_table
                .declare_synthetic(ModuleId(0), type_term.clone());
        }
        ctx
    }

    /// Creates a test KernelContext with function types for testing.
    /// Sets up various function types and assigns them to symbols.
    ///
    /// Symbol type assignments:
    /// - g0, c0: (Bool, Bool) -> Bool
    /// - g1, c1: Bool -> Bool
    /// - g2, c2: (Bool, Bool, Bool) -> Bool
    /// - g3, c3: Empty -> Bool (for tests with EMPTY-typed args)
    /// - g4, c4: (Empty, Empty) -> Empty
    /// - g5-g9, c5-c9: Bool
    #[cfg(test)]
    pub fn test_with_function_types() -> KernelContext {
        use crate::elaborator::acorn_type::{AcornType, FunctionType};

        let mut ctx = KernelContext::new();

        // Add function types and get type terms
        let bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let bool2_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let bool3_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Bool, AcornType::Bool, AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        let empty_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Empty],
            return_type: Box::new(AcornType::Bool),
        });
        let empty2_to_empty = AcornType::Function(FunctionType {
            arg_types: vec![AcornType::Empty, AcornType::Empty],
            return_type: Box::new(AcornType::Empty),
        });
        // Higher-order type like true_below: (Bool -> Bool, Bool) -> Bool
        let func_bool_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![bool_to_bool.clone(), AcornType::Bool],
            return_type: Box::new(AcornType::Bool),
        });
        // Type like (Bool -> Bool) -> Bool
        let func_to_bool = AcornType::Function(FunctionType {
            arg_types: vec![bool_to_bool.clone()],
            return_type: Box::new(AcornType::Bool),
        });

        // Register types in the type store first
        ctx.type_store.add_type(&bool_to_bool);
        ctx.type_store.add_type(&bool2_to_bool);
        ctx.type_store.add_type(&bool3_to_bool);
        ctx.type_store.add_type(&empty_to_bool);
        ctx.type_store.add_type(&empty2_to_empty);
        ctx.type_store.add_type(&func_bool_to_bool);
        ctx.type_store.add_type(&func_to_bool);

        let type_bool_to_bool = ctx
            .type_store
            .get_type_term(&bool_to_bool)
            .expect("type should be valid");
        let type_bool2_to_bool = ctx
            .type_store
            .get_type_term(&bool2_to_bool)
            .expect("type should be valid");
        let type_bool3_to_bool = ctx
            .type_store
            .get_type_term(&bool3_to_bool)
            .expect("type should be valid");
        let type_empty_to_bool = ctx
            .type_store
            .get_type_term(&empty_to_bool)
            .expect("type should be valid");
        let type_empty2_to_empty = ctx
            .type_store
            .get_type_term(&empty2_to_empty)
            .expect("type should be valid");
        let type_func_bool_to_bool = ctx
            .type_store
            .get_type_term(&func_bool_to_bool)
            .expect("type should be valid");
        let type_func_to_bool = ctx
            .type_store
            .get_type_term(&func_to_bool)
            .expect("type should be valid");

        // Add global constants with function types
        ctx.symbol_table
            .add_global_constant(type_bool2_to_bool.clone()); // g0
        ctx.symbol_table
            .add_global_constant(type_bool_to_bool.clone()); // g1
        ctx.symbol_table
            .add_global_constant(type_bool3_to_bool.clone()); // g2
        ctx.symbol_table
            .add_global_constant(type_empty_to_bool.clone()); // g3
        ctx.symbol_table
            .add_global_constant(type_empty2_to_empty.clone()); // g4
        for _ in 5..10 {
            ctx.symbol_table.add_global_constant(Term::bool_type());
        }
        // h0: (Bool -> Bool, Bool) -> Bool (like true_below)
        ctx.symbol_table
            .add_global_constant(type_func_bool_to_bool.clone());
        // h1: (Bool -> Bool) -> Bool
        ctx.symbol_table
            .add_global_constant(type_func_to_bool.clone());

        // Add scoped constants with similar types
        ctx.symbol_table
            .add_scoped_constant(type_bool2_to_bool.clone()); // c0
        ctx.symbol_table
            .add_scoped_constant(type_bool_to_bool.clone()); // c1
        ctx.symbol_table
            .add_scoped_constant(type_bool3_to_bool.clone()); // c2
        ctx.symbol_table
            .add_scoped_constant(type_empty_to_bool.clone()); // c3
        ctx.symbol_table
            .add_scoped_constant(type_empty2_to_empty.clone()); // c4
        for _ in 5..10 {
            ctx.symbol_table.add_scoped_constant(Term::bool_type());
        }

        // Add synthetics with BOOL type
        for _ in 0..10 {
            ctx.symbol_table
                .declare_synthetic(ModuleId(0), Term::bool_type());
        }

        ctx
    }

    /// Add a datatype by name for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.parse_datatype("Int")`
    #[cfg(test)]
    pub fn parse_datatype(&mut self, name: &str) -> &mut Self {
        self.parse_type_constructor(name, 0)
    }

    /// Add a type constructor by name with the given arity for testing.
    /// Arity 0 means a simple type like "Int".
    /// Arity 1 means a type constructor like "List" (List[T]).
    /// Arity 2 means a type constructor like "Pair" (Pair[S, T]).
    /// Returns self for chaining.
    ///
    /// Example: `ctx.parse_type_constructor("List", 1)`
    #[cfg(test)]
    pub fn parse_type_constructor(&mut self, name: &str, arity: u8) -> &mut Self {
        use crate::elaborator::acorn_type::{AcornType, Datatype};
        use crate::module::ModuleId;

        let datatype = Datatype {
            module_id: ModuleId(0),
            name: name.to_string(),
        };
        let acorn_type = AcornType::Data(datatype.clone(), vec![]);
        self.type_store.add_type(&acorn_type);
        self.type_store.set_datatype_arity(&datatype, arity);
        self
    }

    /// Add multiple datatypes by name for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.parse_datatypes(&["Int", "Nat", "Real"])`
    #[cfg(test)]
    pub fn parse_datatypes(&mut self, names: &[&str]) -> &mut Self {
        for name in names {
            self.parse_datatype(name);
        }
        self
    }

    /// Add a typeclass by name for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.parse_typeclass("Ring")`
    #[cfg(test)]
    pub fn parse_typeclass(&mut self, name: &str) -> &mut Self {
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let typeclass = Typeclass {
            module_id: ModuleId(0),
            name: name.to_string(),
        };
        self.type_store.add_typeclass(&typeclass);
        self
    }

    /// Register a datatype as an instance of a typeclass.
    /// Automatically registers the datatype if it doesn't exist yet.
    ///
    /// Example: `ctx.parse_instance("Int", "Ring")` makes Int an instance of Ring.
    #[cfg(test)]
    pub fn parse_instance(&mut self, datatype_name: &str, typeclass_name: &str) -> &mut Self {
        use crate::elaborator::acorn_type::{AcornType, Datatype};
        use crate::module::ModuleId;

        // Register the datatype if it doesn't exist
        if self
            .type_store
            .get_ground_id_by_name(datatype_name)
            .is_none()
        {
            self.parse_datatype(datatype_name);
        }

        let datatype = Datatype {
            module_id: ModuleId(0),
            name: datatype_name.to_string(),
        };
        let acorn_type = AcornType::Data(datatype, vec![]);
        let typeclass_id = self
            .type_store
            .get_typeclass_id_by_name(typeclass_name)
            .unwrap_or_else(|| panic!("Unknown typeclass: {}", typeclass_name));
        self.type_store.add_type_instance(&acorn_type, typeclass_id);
        self
    }

    /// Parse a type string like "Bool", "Int", "Int -> Bool", "(Int, Int) -> Bool",
    /// "List[Int]", "Pair[Int, Bool]", or "T0" (type variable).
    /// Looks up datatype names in the TypeStore.
    #[cfg(test)]
    pub fn parse_type(&self, type_str: &str) -> Term {
        use crate::kernel::atom::Atom;

        let s = type_str.trim();

        // Check for arrow type: "A -> B"
        if let Some(arrow_pos) = Self::find_top_level_arrow(s) {
            let input_str = s[..arrow_pos].trim();
            let output_str = s[arrow_pos + 2..].trim();

            let output = self.parse_type(output_str);

            if input_str.starts_with('(') && input_str.ends_with(')') {
                // Multi-argument: "(A, B, C)" -> curried Pi
                let inner = &input_str[1..input_str.len() - 1];
                let args: Vec<&str> = Self::split_by_comma(inner);
                let mut result = output;
                for arg in args.iter().rev() {
                    let arg_type = self.parse_type(arg.trim());
                    result = Term::pi(arg_type, result);
                }
                result
            } else {
                let input = self.parse_type(input_str);
                Term::pi(input, output)
            }
        } else if let Some(bracket_pos) = s.find('[') {
            // Parameterized type: "List[Int]" or "Pair[Int, Bool]"
            let name = s[..bracket_pos].trim();
            let params_str = &s[bracket_pos + 1..s.len() - 1]; // Strip [ and ]
            let params: Vec<&str> = Self::split_by_comma(params_str);

            // Get the ground type for the type constructor
            let ground_id = self
                .type_store
                .get_ground_id_by_name(name)
                .unwrap_or_else(|| panic!("Unknown type constructor: {}", name));

            // Parse type parameters
            let type_args: Vec<Term> = params.iter().map(|p| self.parse_type(p.trim())).collect();

            // Build applied type: TypeConstructor(param1, param2, ...)
            Term::new(Atom::Symbol(Symbol::Type(ground_id)), type_args)
        } else if s.starts_with('T') && s.len() > 1 && s[1..].chars().all(|c| c.is_ascii_digit()) {
            // Type variable: "T0", "T1", etc. - represented as FreeVariable in the term
            let var_id: u16 = s[1..].parse().expect("invalid type variable id");
            Term::atom(Atom::FreeVariable(var_id))
        } else if s.starts_with('x') && s.len() > 1 && s[1..].chars().all(|c| c.is_ascii_digit()) {
            // Variable reference: "x0", "x1", etc. - for dependent types where a value's type
            // is another variable. Same representation as T0, T1 (FreeVariable).
            let var_id: u16 = s[1..].parse().expect("invalid variable id");
            Term::atom(Atom::FreeVariable(var_id))
        } else {
            // Simple type name - try various lookups
            match s {
                "Bool" => Term::bool_type(),
                "Empty" => Term::empty_type(),
                "Type" => Term::type_sort(),
                _ => {
                    // Try typeclass first
                    if let Some(tc_id) = self.type_store.get_typeclass_id_by_name(s) {
                        return Term::typeclass(tc_id);
                    }
                    // Then try ground type in TypeStore
                    self.type_store
                        .get_ground_id_by_name(s)
                        .map(Term::ground_type)
                        .unwrap_or_else(|| panic!("Unknown type name: {}", s))
                }
            }
        }
    }

    /// Find the position of a top-level "->" (not inside parentheses or brackets).
    #[cfg(test)]
    fn find_top_level_arrow(s: &str) -> Option<usize> {
        let mut depth = 0;
        let bytes = s.as_bytes();
        for i in 0..bytes.len().saturating_sub(1) {
            match bytes[i] {
                b'(' | b'[' => depth += 1,
                b')' | b']' => depth -= 1,
                b'-' if depth == 0 && bytes.get(i + 1) == Some(&b'>') => return Some(i),
                _ => {}
            }
        }
        None
    }

    /// Split a string by commas, respecting parentheses and brackets.
    #[cfg(test)]
    fn split_by_comma(s: &str) -> Vec<&str> {
        let mut result = Vec::new();
        let mut depth = 0;
        let mut start = 0;
        for (i, c) in s.char_indices() {
            match c {
                '(' | '[' => depth += 1,
                ')' | ']' => depth -= 1,
                ',' if depth == 0 => {
                    result.push(&s[start..i]);
                    start = i + 1;
                }
                _ => {}
            }
        }
        result.push(&s[start..]);
        result
    }

    /// Parse a Pi type with named binders.
    ///
    /// Example: `ctx.parse_pi("R: Ring", "R -> R -> R")`
    /// produces `Pi(Ring, Pi(b0, Pi(b1, b2)))` representing `Π(R: Ring). R -> R -> R`
    ///
    /// - `binders`: Comma-separated binders like "R: Ring" or "R: Ring, n: Nat"
    /// - `body`: The body type, using binder names to refer to bound variables
    ///
    /// The parser automatically computes de Bruijn indices, accounting for
    /// arrow-induced Pi nesting.
    #[cfg(test)]
    pub fn parse_pi(&self, binders: &str, body: &str) -> Term {
        // Parse binders into (name, type) pairs
        let binder_list = self.parse_binder_list(binders);
        let num_binders = binder_list.len();

        // Build name -> binder_index map
        let name_to_index: std::collections::HashMap<&str, usize> = binder_list
            .iter()
            .enumerate()
            .map(|(i, (name, _))| (*name, i))
            .collect();

        // Parse the body with arrow_depth = 0
        let body_term = self.parse_pi_body(body, num_binders, 0, &name_to_index);

        // Wrap with Pi types from innermost to outermost
        let mut result = body_term;
        for (_, binder_type) in binder_list.into_iter().rev() {
            result = Term::pi(binder_type, result);
        }
        result
    }

    /// Parse a binder list like "R: Ring, n: Nat" into [(name, type_term)] pairs.
    #[cfg(test)]
    fn parse_binder_list<'a>(&self, binders: &'a str) -> Vec<(&'a str, Term)> {
        if binders.trim().is_empty() {
            return vec![];
        }

        let mut result = vec![];
        for part in Self::split_by_comma(binders) {
            let part = part.trim();
            if let Some(colon_pos) = part.find(':') {
                let name = part[..colon_pos].trim();
                let type_str = part[colon_pos + 1..].trim();
                let type_term = self.parse_binder_type(type_str);
                result.push((name, type_term));
            } else {
                panic!("Invalid binder syntax: '{}', expected 'name: Type'", part);
            }
        }
        result
    }

    /// Parse a binder type - tries typeclass first, then falls back to parse_type.
    /// This is for parsing the types in Pi binders like Π(R: Ring).
    #[cfg(test)]
    fn parse_binder_type(&self, type_str: &str) -> Term {
        let s = type_str.trim();
        // Try typeclass first
        if let Some(tc_id) = self.type_store.get_typeclass_id_by_name(s) {
            return Term::typeclass(tc_id);
        }
        // Fall back to regular type parsing
        self.parse_type(s)
    }

    /// Parse the body of a Pi type with named variables.
    ///
    /// - `num_binders`: Total number of Pi binders from parse_pi
    /// - `arrow_depth`: How many arrow-induced Pis we're currently nested under
    /// - `name_to_index`: Maps variable names to their binder index (0 = outermost)
    ///
    /// De Bruijn index = (num_binders - 1 - binder_index) + arrow_depth
    #[cfg(test)]
    fn parse_pi_body(
        &self,
        type_str: &str,
        num_binders: usize,
        arrow_depth: usize,
        name_to_index: &std::collections::HashMap<&str, usize>,
    ) -> Term {
        use crate::kernel::atom::Atom;

        let s = type_str.trim();

        // Check for arrow type: "A -> B"
        if let Some(arrow_pos) = Self::find_top_level_arrow(s) {
            let input_str = s[..arrow_pos].trim();
            let output_str = s[arrow_pos + 2..].trim();

            if input_str.starts_with('(') && input_str.ends_with(')') {
                // Multi-argument: "(A, B, C) -> D" -> curried Pi
                let inner = &input_str[1..input_str.len() - 1];
                let args: Vec<&str> = Self::split_by_comma(inner);
                let num_args = args.len();

                // Output is under all the argument Pis
                let output = self.parse_pi_body(
                    output_str,
                    num_binders,
                    arrow_depth + num_args,
                    name_to_index,
                );

                // Build curried Pis from right to left
                let mut result = output;
                for (i, arg) in args.iter().rev().enumerate() {
                    // The i-th arg from the right is under (num_args - 1 - i) Pis
                    let arg_depth = arrow_depth + (num_args - 1 - i);
                    let arg_type =
                        self.parse_pi_body(arg.trim(), num_binders, arg_depth, name_to_index);
                    result = Term::pi(arg_type, result);
                }
                result
            } else {
                // Simple arrow: "A -> B"
                // Input is at current arrow_depth
                let input = self.parse_pi_body(input_str, num_binders, arrow_depth, name_to_index);
                // Output is under one more Pi
                let output =
                    self.parse_pi_body(output_str, num_binders, arrow_depth + 1, name_to_index);
                Term::pi(input, output)
            }
        } else if let Some(bracket_pos) = s.find('[') {
            // Parameterized type: "List[T]" or "Matrix[R, n, n]"
            let name = s[..bracket_pos].trim();
            let params_str = &s[bracket_pos + 1..s.len() - 1];
            let params: Vec<&str> = Self::split_by_comma(params_str);

            let ground_id = self
                .type_store
                .get_ground_id_by_name(name)
                .unwrap_or_else(|| panic!("Unknown type constructor: {}", name));

            let type_args: Vec<Term> = params
                .iter()
                .map(|p| self.parse_pi_body(p.trim(), num_binders, arrow_depth, name_to_index))
                .collect();

            Term::new(Atom::Symbol(Symbol::Type(ground_id)), type_args)
        } else if let Some(&binder_index) = name_to_index.get(s) {
            // Named bound variable from binders
            // De Bruijn index = (num_binders - 1 - binder_index) + arrow_depth
            let bound_idx = (num_binders - 1 - binder_index + arrow_depth) as u16;
            Term::atom(Atom::BoundVariable(bound_idx))
        } else {
            // Simple type name or other
            match s {
                "Bool" => Term::bool_type(),
                "Empty" => Term::empty_type(),
                "Type" => Term::type_sort(),
                _ => self
                    .type_store
                    .get_ground_id_by_name(s)
                    .map(Term::ground_type)
                    .unwrap_or_else(|| panic!("Unknown type name: {}", s)),
            }
        }
    }

    /// Add a constant with a given name and type string for testing.
    /// The name should be like "c0", "g0", or "s0".
    /// Returns self for chaining.
    ///
    /// Example: `ctx.parse_constant("c0", "Int").parse_constant("g0", "Int -> Bool")`
    #[cfg(test)]
    pub fn parse_constant(&mut self, name: &str, type_str: &str) -> &mut Self {
        let type_term = self.parse_type(type_str);
        let first_char = name.chars().next().expect("empty constant name");
        let id: u32 = name[1..].parse().expect("invalid constant id");

        match first_char {
            'c' => {
                while self.symbol_table.num_scoped_constants() <= id {
                    self.symbol_table.add_scoped_constant(Term::empty_type());
                }
                self.symbol_table.set_scoped_constant_type(id, type_term);
            }
            'g' => {
                while self.symbol_table.num_global_constants() <= id {
                    self.symbol_table.add_global_constant(Term::empty_type());
                }
                self.symbol_table.set_global_constant_type(id, type_term);
            }
            's' => {
                while self.symbol_table.num_synthetics() <= id {
                    self.symbol_table
                        .declare_synthetic(ModuleId(0), Term::empty_type());
                }
                self.symbol_table.set_synthetic_type(id, type_term);
            }
            _ => panic!("Unknown constant prefix: {}", first_char),
        }
        self
    }

    /// Add multiple constants with the same type for testing.
    /// Returns self for chaining.
    ///
    /// Example: `ctx.parse_constants(&["c0", "c1", "c2"], "Int")`
    #[cfg(test)]
    pub fn parse_constants(&mut self, names: &[&str], type_str: &str) -> &mut Self {
        for name in names {
            self.parse_constant(name, type_str);
        }
        self
    }

    /// Add a polymorphic constant with a Pi type.
    ///
    /// Example: `ctx.parse_polymorphic_constant("c0", "R: Ring", "R -> R -> R")`
    /// creates a constant c0 with type `Π(R: Ring). R -> R -> R`
    #[cfg(test)]
    pub fn parse_polymorphic_constant(
        &mut self,
        name: &str,
        binders: &str,
        body: &str,
    ) -> &mut Self {
        let type_term = self.parse_pi(binders, body);
        let first_char = name.chars().next().expect("empty constant name");
        let id: u32 = name[1..].parse().expect("invalid constant id");

        match first_char {
            'c' => {
                while self.symbol_table.num_scoped_constants() <= id {
                    self.symbol_table.add_scoped_constant(Term::empty_type());
                }
                self.symbol_table.set_scoped_constant_type(id, type_term);
            }
            'g' => {
                while self.symbol_table.num_global_constants() <= id {
                    self.symbol_table.add_global_constant(Term::empty_type());
                }
                self.symbol_table.set_global_constant_type(id, type_term);
            }
            _ => panic!("polymorphic constant name must start with 'c' or 'g'"),
        }
        self
    }

    /// Create a LocalContext with variables of the given types.
    /// var_types[i] is the type string for variable x_i.
    ///
    /// Example: `ctx.parse_local(&["Int", "Bool"])` creates context where x0: Int, x1: Bool
    #[cfg(test)]
    pub fn parse_local(&self, var_types: &[&str]) -> crate::kernel::local_context::LocalContext {
        use crate::kernel::local_context::LocalContext;

        let type_terms: Vec<Term> = var_types
            .iter()
            .map(|type_str| self.parse_type(type_str))
            .collect();
        LocalContext::from_types(type_terms)
    }

    /// Parse a term string, resolving type names in the context.
    ///
    /// Supports:
    /// - Variables: x0, x1, ...
    /// - Scoped constants: c0, c1, ...
    /// - Global constants: g0, g1, ...
    /// - Type names: Int, Bool, List, etc. (looked up in TypeStore)
    /// - Applications: f(a, b, c)
    ///
    /// Example: `ctx.parse_term("c0(Int, x0, x1)")` where Int is a registered type
    #[cfg(test)]
    pub fn parse_term(&self, s: &str) -> Term {
        use crate::kernel::atom::Atom;
        use crate::kernel::symbol::Symbol;

        let s = s.trim();

        // Check for application: head(args)
        if let Some(first_paren) = s.find('(') {
            // Find matching close paren and split args
            let mut depth = 0;
            let mut arg_starts = vec![first_paren + 1];
            let mut close_paren = s.len() - 1;

            for (i, c) in s.char_indices() {
                match c {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            close_paren = i;
                            break;
                        }
                    }
                    ',' if depth == 1 => arg_starts.push(i + 1),
                    _ => {}
                }
            }

            let head = self.parse_term(&s[..first_paren]);
            let args_str = &s[first_paren + 1..close_paren];

            if args_str.trim().is_empty() {
                return head;
            }

            // Parse args by splitting on commas at depth 0
            let mut args = Vec::new();
            let mut current_start = 0;
            let mut depth = 0;
            for (i, c) in args_str.char_indices() {
                match c {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    ',' if depth == 0 => {
                        args.push(self.parse_term(&args_str[current_start..i]));
                        current_start = i + 1;
                    }
                    _ => {}
                }
            }
            args.push(self.parse_term(&args_str[current_start..]));

            return head.apply(&args);
        }

        // Try standard atom parsing first (c0, x0, g0, b0, s0)
        if let Some(atom) = Atom::parse(s) {
            return Term::atom(atom);
        }

        // Try type names
        if let Some(ground_id) = self.type_store.get_ground_id_by_name(s) {
            return Term::ground_type(ground_id);
        }

        // Built-in types and constants
        match s {
            "Bool" => Term::bool_type(),
            "Empty" => Term::empty_type(),
            "Type" => Term::type_sort(),
            "true" => Term::atom(Atom::Symbol(Symbol::True)),
            "false" => Term::atom(Atom::Symbol(Symbol::False)),
            _ => {
                // Fall back to Term::parse for anything else
                Term::parse(s)
            }
        }
    }

    /// Parse a literal string, resolving type names in the context.
    ///
    /// Supports:
    /// - Equality: `"a = b"`
    /// - Inequality: `"a != b"`
    /// - Positive predicate: `"P(x)"`
    /// - Negative predicate: `"not P(x)"`
    ///
    /// Example: `ctx.parse_literal("c0(Int, x0) = c0(Int, x1)")`
    #[cfg(test)]
    pub fn parse_literal(&self, s: &str) -> crate::kernel::literal::Literal {
        use crate::kernel::literal::Literal;

        let s = s.trim();

        if s.contains(" != ") {
            let mut parts = s.split(" != ");
            let left = self.parse_term(parts.next().unwrap());
            let right = self.parse_term(parts.next().unwrap());
            Literal::not_equals(left, right)
        } else if s.contains(" = ") {
            let mut parts = s.split(" = ");
            let left = self.parse_term(parts.next().unwrap());
            let right = self.parse_term(parts.next().unwrap());
            Literal::equals(left, right)
        } else if let Some(rest) = s.strip_prefix("not ") {
            let term = self.parse_term(rest);
            Literal::negative(term)
        } else {
            let term = self.parse_term(s);
            Literal::positive(term)
        }
    }

    /// Parse a clause string with the given variable types.
    /// var_types[i] is the type string for variable x_i.
    ///
    /// Example: `ctx.parse_clause("x0 = c0", &["Int"])` parses clause with x0: Int
    #[cfg(test)]
    pub fn parse_clause(
        &self,
        clause_str: &str,
        var_types: &[&str],
    ) -> crate::kernel::clause::Clause {
        use crate::kernel::clause::Clause;

        let local = self.parse_local(var_types);
        let literals: Vec<_> = clause_str
            .split(" or ")
            .map(|part| self.parse_literal(part.trim()))
            .collect();
        let clause = Clause::new(literals, &local);
        clause.validate(self);
        clause
    }

    /// Create a LocalContext with `count` variables all of type Bool.
    /// Useful for tests that need multiple boolean variables.
    #[cfg(test)]
    pub fn bool_local(&self, count: usize) -> crate::kernel::local_context::LocalContext {
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        LocalContext::from_types(vec![Term::bool_type(); count])
    }

    /// Merges another KernelContext into this one.
    pub fn merge(&mut self, other: &KernelContext) {
        self.type_store.merge(&other.type_store);
        self.symbol_table.merge(&other.symbol_table);
    }

    /// Merges another KernelContext into this one, excluding scoped constants.
    /// This is intended for merging import state only.
    pub fn merge_imports(&mut self, other: &KernelContext) {
        self.type_store.merge(&other.type_store);
        self.symbol_table.merge_imports(&other.symbol_table);
    }
}

impl Default for KernelContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::symbol::Symbol;
    use crate::module::ModuleId;

    #[test]
    fn test_test_with_constants_works() {
        let ctx = KernelContext::test_with_constants(10, 10);
        // Verify we can look up the types for scoped constants c0-c9
        for i in 0..10 {
            let symbol = Symbol::ScopedConstant(i);
            let type_term = ctx.symbol_table.get_type(symbol);
            assert_eq!(*type_term, Term::empty_type());
        }
        // Verify we can look up the types for global constants g0_0-g0_9
        for i in 0..10 {
            let symbol = Symbol::GlobalConstant(ModuleId(0), i);
            let type_term = ctx.symbol_table.get_type(symbol);
            assert_eq!(*type_term, Term::empty_type());
        }
    }

    #[test]
    fn test_add_datatype_and_constant() {
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Int")
            .parse_constant("c0", "Int")
            .parse_constant("c1", "Int -> Bool")
            .parse_constant("c2", "(Int, Int) -> Bool");

        // Verify c0 has type Int
        let c0_type = ctx.symbol_table.get_type(Symbol::ScopedConstant(0));
        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();
        assert_eq!(*c0_type, Term::ground_type(int_id));

        // Verify c1 has type Int -> Bool
        let c1_type = ctx.symbol_table.get_type(Symbol::ScopedConstant(1));
        assert!(c1_type.as_ref().split_pi().is_some());

        // Verify c2 has type (Int, Int) -> Bool (curried as Int -> Int -> Bool)
        let c2_type = ctx.symbol_table.get_type(Symbol::ScopedConstant(2));
        let (_, inner) = c2_type.as_ref().split_pi().unwrap();
        assert!(inner.split_pi().is_some()); // Should be another arrow type
    }

    #[test]
    fn test_parameterized_type_parsing() {
        use crate::kernel::atom::Atom;

        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Int")
            .parse_type_constructor("List", 1)
            .parse_type_constructor("Pair", 2)
            .parse_constant("c0", "List[Int]")
            .parse_constant("c1", "Pair[Int, Bool]")
            .parse_constant("c2", "List[Int] -> Bool");

        // Verify List has arity 1
        let list_id = ctx.type_store.get_ground_id_by_name("List").unwrap();
        assert_eq!(ctx.type_store.get_arity(list_id), 1);

        // Verify Pair has arity 2
        let pair_id = ctx.type_store.get_ground_id_by_name("Pair").unwrap();
        assert_eq!(ctx.type_store.get_arity(pair_id), 2);

        // Verify c0 has type List[Int] (an application of List to Int)
        let c0_type = ctx.symbol_table.get_type(Symbol::ScopedConstant(0));
        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();
        let expected_list_int = Term::new(
            Atom::Symbol(Symbol::Type(list_id)),
            vec![Term::ground_type(int_id)],
        );
        assert_eq!(*c0_type, expected_list_int);

        // Verify c1 has type Pair[Int, Bool]
        let c1_type = ctx.symbol_table.get_type(Symbol::ScopedConstant(1));
        let expected_pair = Term::new(
            Atom::Symbol(Symbol::Type(pair_id)),
            vec![Term::ground_type(int_id), Term::bool_type()],
        );
        assert_eq!(*c1_type, expected_pair);

        // Verify c2 has type List[Int] -> Bool
        let c2_type = ctx.symbol_table.get_type(Symbol::ScopedConstant(2));
        let (input, output) = c2_type.as_ref().split_pi().unwrap();
        assert_eq!(input.to_owned(), expected_list_int);
        assert_eq!(output.to_owned(), Term::bool_type());
    }

    #[test]
    fn test_type_variable_parsing() {
        use crate::kernel::atom::Atom;

        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("List", 1);

        // Test parsing T0, T1 as type variables
        let t0 = ctx.parse_type("T0");
        assert_eq!(t0, Term::atom(Atom::FreeVariable(0)));

        let t1 = ctx.parse_type("T1");
        assert_eq!(t1, Term::atom(Atom::FreeVariable(1)));

        // Test parsing List[T0] - a generic list type
        let list_id = ctx.type_store.get_ground_id_by_name("List").unwrap();
        let list_t0 = ctx.parse_type("List[T0]");
        let expected = Term::new(
            Atom::Symbol(Symbol::Type(list_id)),
            vec![Term::atom(Atom::FreeVariable(0))],
        );
        assert_eq!(list_t0, expected);
    }

    #[test]
    fn test_parse_pi_simple() {
        use crate::kernel::atom::Atom;

        let mut ctx = KernelContext::new();
        ctx.parse_typeclass("Ring");

        // Π(R: Ring). R -> R -> R
        // R appears at arrow depths 0, 1, 2 -> de Bruijn indices 0, 1, 2
        let add_type = ctx.parse_pi("R: Ring", "R -> R -> R");

        let ring_id = ctx.type_store.get_typeclass_id_by_name("Ring").unwrap();
        let ring = Term::typeclass(ring_id);
        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));
        let b2 = Term::atom(Atom::BoundVariable(2));

        // Expected: Pi(Ring, Pi(b0, Pi(b1, b2)))
        let expected = Term::pi(ring, Term::pi(b0, Term::pi(b1, b2)));

        assert_eq!(add_type, expected);
    }

    #[test]
    fn test_parse_pi_with_concrete_types() {
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Nat");

        // Π(n: Nat). Nat -> Nat
        // The body doesn't use n, just concrete Nat types
        let fn_type = ctx.parse_pi("n: Nat", "Nat -> Nat");

        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat = Term::ground_type(nat_id);

        // Expected: Pi(Nat, Pi(Nat, Nat))
        let expected = Term::pi(nat.clone(), Term::pi(nat.clone(), nat));

        assert_eq!(fn_type, expected);
    }

    #[test]
    fn test_parse_pi_with_typeclass() {
        use crate::kernel::atom::Atom;

        let mut ctx = KernelContext::new();
        ctx.parse_typeclass("CommRing");

        // Π(R: CommRing). R -> R -> R
        let add_type = ctx.parse_pi("R: CommRing", "R -> R -> R");

        let comm_ring_id = ctx.type_store.get_typeclass_id_by_name("CommRing").unwrap();
        let comm_ring_type = Term::typeclass(comm_ring_id);
        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));
        let b2 = Term::atom(Atom::BoundVariable(2));

        // Expected: Pi(CommRing, Pi(b0, Pi(b1, b2)))
        let expected = Term::pi(comm_ring_type, Term::pi(b0, Term::pi(b1, b2)));

        assert_eq!(add_type, expected);
    }

    #[test]
    fn test_provably_inhabited_identity_function() {
        use crate::kernel::atom::Atom;
        use crate::kernel::local_context::LocalContext;

        let ctx = KernelContext::new();

        // Test T -> T type (identity function)
        // In de Bruijn notation, T -> T (where T is a type parameter at index 0) is Pi(b0, b1):
        // - b0: the domain type T (from outside the Pi)
        // - b1: the codomain type T (from inside the Pi, so shifted by 1)
        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));
        let t_to_t = Term::pi(b0.clone(), b1.clone());

        // Create a local context where type variable 0 has kind TypeSort
        let mut local_ctx = LocalContext::empty();
        local_ctx.push_type(Term::type_sort());

        // T -> T should be provably inhabited (identity function exists)
        assert!(
            ctx.provably_inhabited(&t_to_t, Some(&local_ctx)),
            "T -> T should be provably inhabited"
        );
    }
}
