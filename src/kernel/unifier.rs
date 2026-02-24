use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term, TermRef};
use crate::kernel::variable_map::VariableMap;
use std::fmt;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Scope(usize);

impl Scope {
    pub const OUTPUT: Scope = Scope(0);
    pub const LEFT: Scope = Scope(1);
    pub const RIGHT: Scope = Scope(2);

    pub fn get(&self) -> usize {
        self.0
    }
}

// A Unifier combines terms whose variables exist in different scopes.
// There are normally two input scopes, the "left" and the "right".
// For each scope we create a mapping from variable id to the term in the output scope.
// We leave the mapping as "None" when we haven't had to map it to anything yet.
//
// The output scope is the scope of the final term.
// Algorithmically, the output scope is treated slightly differently from the input scopes,
// but any input scopes are treated the same way.
// We do need a mapping for the output because we may have two complex terms in the output
// scope that we need to unify, and during this unification we may discover that previously
// unrelated variables now need to relate to each other.
pub struct Unifier<'a> {
    maps: Vec<VariableMap>,

    // Shared kernel context for symbol table access
    kernel_context: &'a KernelContext,

    // One LocalContext per input scope (borrowed from source clauses)
    // Index 0 is unused (that's the output scope), indices 1+ correspond to input scopes
    input_contexts: Vec<Option<&'a LocalContext>>,

    // Owned output context, built during unification as new variables are created
    output_context: LocalContext,
}

impl<'a> Unifier<'a> {
    /// Creates a new unifier with the given number of scopes.
    pub fn new(num_scopes: usize, kernel_context: &'a KernelContext) -> Unifier<'a> {
        let mut maps = Vec::with_capacity(num_scopes);
        for _ in 0..num_scopes {
            maps.push(VariableMap::new());
        }
        // Initialize input_contexts with None for each scope (including output at index 0)
        let mut input_contexts = Vec::with_capacity(num_scopes);
        for _ in 0..num_scopes {
            input_contexts.push(None);
        }
        Unifier {
            maps,
            kernel_context,
            input_contexts,
            output_context: LocalContext::empty(),
        }
    }

    /// Sets the input context for a specific scope.
    /// Should be called for LEFT and RIGHT scopes before unification.
    pub fn set_input_context(&mut self, scope: Scope, context: &'a LocalContext) {
        self.input_contexts[scope.get()] = Some(context);
    }

    /// Returns a reference to the output context.
    pub fn output_context(&self) -> &LocalContext {
        &self.output_context
    }

    /// Consumes the unifier and returns the output context.
    pub fn take_output_context(self) -> LocalContext {
        self.output_context
    }

    /// Returns the kernel context.
    pub fn kernel_context(&self) -> &KernelContext {
        self.kernel_context
    }

    /// Pre-populates the output context with variable types for testing.
    /// This allows tests to directly use output variables without going through unification.
    #[cfg(test)]
    fn set_output_var_types(&mut self, types: Vec<Term>) {
        self.output_context = LocalContext::from_types(types);
    }

    /// Returns the LocalContext for a given scope.
    /// For OUTPUT scope, returns the output_context.
    /// For input scopes (LEFT, RIGHT, etc.), returns the stored input context.
    fn get_local_context(&self, scope: Scope) -> &LocalContext {
        if scope == Scope::OUTPUT {
            &self.output_context
        } else {
            self.input_contexts[scope.get()].expect("Input context not set for scope")
        }
    }

    /// Creates a unifier with an initial VariableMap and explicit output context.
    /// The output_context provides the types for variables in the output scope.
    pub fn with_map(
        map: VariableMap,
        kernel_context: &'a KernelContext,
        output_context: LocalContext,
    ) -> (Unifier<'a>, Scope) {
        // Initialize the output map with enough blank entries for any variables in the initial map
        let mut output_map = VariableMap::new();
        if let Some(max_var) = map.max_output_variable() {
            for _ in 0..=max_var {
                output_map.push_none();
            }
        }

        let unifier = Unifier {
            maps: vec![output_map, map],
            kernel_context,
            input_contexts: vec![None, None], // Output scope and one input scope
            output_context,
        };
        (unifier, Scope(1))
    }

    fn mut_map(&mut self, scope: Scope) -> &mut VariableMap {
        &mut self.maps[scope.get()]
    }

    fn map(&self, scope: Scope) -> &VariableMap {
        &self.maps[scope.get()]
    }

    pub fn into_maps(self) -> impl Iterator<Item = (Scope, VariableMap)> {
        self.maps
            .into_iter()
            .enumerate()
            .map(|(i, var_map)| (Scope(i), var_map))
    }

    /// Like into_maps, but also returns the output context.
    /// This is needed because VariableMap replacement terms reference
    /// variables in the unifier's output context.
    pub fn into_maps_with_context(self) -> (Vec<(Scope, VariableMap)>, LocalContext) {
        let maps: Vec<_> = self
            .maps
            .into_iter()
            .enumerate()
            .map(|(i, var_map)| (Scope(i), var_map))
            .collect();
        (maps, self.output_context)
    }

    pub fn add_scope(&mut self) -> Scope {
        let scope = Scope(self.maps.len());
        self.maps.push(VariableMap::new());
        self.input_contexts.push(None);
        scope
    }

    fn has_mapping(&self, scope: Scope, i: AtomId) -> bool {
        self.map(scope).has_mapping(i)
    }

    fn set_mapping(&mut self, scope: Scope, i: AtomId, term: Term) {
        self.mut_map(scope).set(i, term);
    }

    fn get_mapping(&self, scope: Scope, i: AtomId) -> Option<&Term> {
        self.map(scope).get_mapping(i)
    }

    pub fn print_scope(&self, scope: Scope) -> i32 {
        let map = self.map(scope);
        let mut count = 0;
        for (i, t) in map.iter() {
            if count == 0 {
                println!("{:?} scope:", scope);
            }
            println!("x{} -> {}", i, t);
            count += 1;
        }
        count
    }

    pub fn print(&self) {
        let mut count = 0;
        count += self.print_scope(Scope::LEFT);
        count += self.print_scope(Scope::RIGHT);
        count += self.print_scope(Scope::OUTPUT);
        if count == 0 {
            println!("empty unifier");
        }
    }

    /// Applies the unifier substitution to a term.
    /// Variables are replaced with their mapped values, and unmapped variables
    /// in non-output scopes get fresh output variables created for them.
    pub fn apply(&mut self, scope: Scope, term: &Term) -> Term {
        self.apply_internal(scope, term.as_ref())
    }

    fn apply_internal(&mut self, scope: Scope, term: TermRef) -> Term {
        match term.decompose() {
            Decomposition::Atom(Atom::FreeVariable(i)) => {
                // Handle variable: either use existing mapping or create fresh output variable
                if !self.has_mapping(scope, *i) && scope != Scope::OUTPUT {
                    // Create a new output variable for this unmapped input variable
                    let var_id = self.maps[Scope::OUTPUT.get()].len() as AtomId;
                    self.maps[Scope::OUTPUT.get()].push_none();
                    let new_var = Term::new_variable(var_id);
                    // Set the mapping BEFORE applying to the type, so if the type
                    // contains this same variable, we don't recurse infinitely
                    self.set_mapping(scope, *i, new_var);
                    let var_type = self
                        .get_local_context(scope)
                        .get_var_type(*i as usize)
                        .cloned()
                        .expect("Variable should have type in LocalContext");
                    // Apply the unifier to the type to translate FreeVariable references
                    // from input variable IDs to output variable IDs
                    let translated_type = self.apply(scope, &var_type);
                    // Use set_type at var_id position, not push_type, because recursion
                    // may have already added entries to output_context
                    self.output_context
                        .set_type(var_id as usize, translated_type);
                }

                match self.get_mapping(scope, *i) {
                    Some(mapped) => mapped.clone(),
                    None => {
                        // Output variable with no mapping - leave as is
                        assert!(scope == Scope::OUTPUT);
                        term.to_owned()
                    }
                }
            }
            Decomposition::Atom(_) => {
                // Non-variable atom: return as-is
                term.to_owned()
            }
            Decomposition::Application(func, arg) => {
                // Recursively apply to both function and argument
                let applied_func = self.apply_internal(scope, func);
                let applied_arg = self.apply_internal(scope, arg);
                applied_func.apply(&[applied_arg])
            }
            Decomposition::Pi(input, output) => {
                // Recursively apply to both input and output types
                let applied_input = self.apply_internal(scope, input);
                let applied_output = self.apply_internal(scope, output);
                Term::pi(applied_input, applied_output)
            }
            Decomposition::Lambda(input, body) => {
                // Recursively apply to lambda input type and body
                let applied_input = self.apply_internal(scope, input);
                let applied_body = self.apply_internal(scope, body);
                Term::lambda(applied_input, applied_body)
            }
        }
    }

    /// Returns the resulting literal, and whether it was flipped.
    pub fn apply_to_literal(&mut self, scope: Scope, literal: &Literal) -> (Literal, bool) {
        let apply_left = self.apply(scope, &literal.left);
        let apply_right = self.apply(scope, &literal.right);
        Literal::new_with_flip(literal.positive, apply_left, apply_right)
    }

    // Replace variable i in the output scope with the given term (which is also in the output scope).
    // If they're both variables, keep the one with the lower id.
    // Returns whether this succeeded.
    // It fails if this would require making a variable self-nesting.
    fn remap(&mut self, id: AtomId, term: &Term) -> bool {
        if let Some(other_id) = term.atomic_variable() {
            if other_id > id {
                // Let's keep this id and remap the other one instead.
                // Since term is an atomic variable, create a new variable term with the lower id.
                let new_term = Term::new_variable(id);
                return self.unify_variable(Scope::OUTPUT, other_id, Scope::OUTPUT, &new_term);
            }
        }
        let term = self.apply(Scope::OUTPUT, term);
        if term.has_variable(id) {
            // We can't remap this variable to a term that contains it.
            // This represents an un-unifiable condition like x0 = c0(x0).
            return false;
        }

        for i in 0..self.maps.len() {
            self.maps[i].apply_to_all(|t| t.replace_variable(id, &term));
        }

        // Handle the case where remapping would create a self-referential type.
        // When we replace x_id with term in all types, if term contains some variable x_j,
        // and x_j's type contained x_id, then x_j's type would now contain x_j (via term).
        // To fix this, before replacing, we substitute x_id with x_id's TYPE (not term)
        // in x_j's type.
        //
        // Example: x0's type is x1, x1's type is TypeSort. We remap x1 -> Pi(x0, Bool).
        // Without fix: x0's type becomes Pi(x0, Bool) - self-referential!
        // With fix: first set x0's type to TypeSort (x1's type), then do replacement.
        if let Some(id_type) = self.output_context.get_var_type(id as usize).cloned() {
            // For each variable that term references, check if its type would become self-referential
            for var_in_term in term.iter_atoms() {
                if let Atom::FreeVariable(var_id) = var_in_term {
                    if let Some(var_type) = self.output_context.get_var_type(*var_id as usize) {
                        if var_type.has_variable(id) {
                            // var_id's type references id. After replacement, it would contain var_id.
                            // Substitute id with id's TYPE instead of with term.
                            let new_var_type = var_type.replace_variable(id, &id_type);
                            self.output_context.set_type(*var_id as usize, new_var_type);
                        }
                    }
                }
            }
        }

        // Now safe to replace the variable in all other types
        self.output_context.replace_variable(id, &term);
        self.maps[Scope::OUTPUT.get()].set(id, term);
        true
    }

    // Returns whether they can be unified.
    fn unify_variable(
        &mut self,
        var_scope: Scope,
        var_id: AtomId,
        term_scope: Scope,
        term: &Term,
    ) -> bool {
        if term_scope != Scope::OUTPUT {
            // Convert our term to the output scope and then unify.
            let term = self.apply(term_scope, term);
            return self.unify_variable(var_scope, var_id, Scope::OUTPUT, &term);
        }

        if self.has_mapping(var_scope, var_id) {
            // We already have a mapping for this variable.
            // Unify the existing mapping with the term.
            let existing = self.get_mapping(var_scope, var_id).unwrap().clone();
            return self.unify_internal(
                Scope::OUTPUT,
                existing.as_ref(),
                Scope::OUTPUT,
                term.as_ref(),
            );
        }

        if var_scope == Scope::OUTPUT {
            if term.atomic_variable() == Some(var_id) {
                // We're unifying a variable with itself.
                return true;
            }

            if term.has_variable(var_id) {
                // We can't unify a variable with a term that contains it.
                return false;
            }

            if term.has_escaping_bound_variable() {
                // BoundVariables only match structurally with identical BoundVariables.
                // They cannot unify with FreeVariables. This can happen during Pi type
                // unification when the output of one Pi contains a BoundVariable.
                // However, Pi types with properly scoped bound variables are allowed.
                return false;
            }

            // Type check for OUTPUT variables: verify types are compatible before remapping.
            // This catches cases like trying to unify a function variable (type A -> B)
            // with a polymorphic constant (type Type -> T) that have incompatible signatures.
            if let Some(var_type) = self.output_context.get_var_type(var_id as usize).cloned() {
                let term_type =
                    term.get_type_with_context(&self.output_context, self.kernel_context);
                if !self.unify_internal(
                    Scope::OUTPUT,
                    var_type.as_ref(),
                    Scope::OUTPUT,
                    term_type.as_ref(),
                ) {
                    return false;
                }
            }

            return self.remap(var_id, term);
        }

        // We don't have a mapping for this variable, so we can just map it now.
        // But first, we need to check that the types are compatible.
        let var_type = self
            .get_local_context(var_scope)
            .get_var_type(var_id as usize)
            .cloned()
            .expect("Variable should have type in LocalContext");

        if term.has_escaping_bound_variable() {
            // BoundVariables only match structurally with identical BoundVariables.
            // They cannot unify with FreeVariables. This can happen during Pi type
            // unification when the output of one Pi contains a BoundVariable.
            // However, Pi types with properly scoped bound variables are allowed.
            return false;
        }

        // Universe level check: when var_type is TypeSort (meaning this is a type variable
        // that should be bound to types like Foo, Nat), we should only accept proper types,
        // not value-level expressions that happen to return Type.
        //
        // Valid: Type symbols (Foo, Bool, Empty), type variables (FreeVariable)
        // Invalid: TypeSort itself, function applications (GlobalConstant, ScopedConstant)
        if matches!(
            var_type.as_ref().decompose(),
            Decomposition::Atom(Atom::Symbol(Symbol::Type0))
        ) {
            match term.as_ref().get_head_atom() {
                // Accept: proper types and type variables
                Atom::Symbol(Symbol::Type(_))
                | Atom::Symbol(Symbol::Bool)
                | Atom::Symbol(Symbol::Empty)
                | Atom::FreeVariable(_) => {
                    // OK - these are proper types
                }
                Atom::Symbol(Symbol::Type0) => {
                    // Reject: TypeSort itself shouldn't match a type variable
                    return false;
                }
                _ => {
                    // Reject: value-level expressions (GlobalConstant, ScopedConstant, etc.)
                    return false;
                }
            }
        }

        // Check if this variable has a typeclass constraint.
        // If its type is a typeclass (e.g., Bar), the term must be a TYPE that
        // is an instance of that typeclass.
        if let Some(typeclass_id) = var_type.as_ref().as_typeclass() {
            // The variable represents a TYPE that must implement the typeclass.
            // First, reject TypeSort itself - it's not a type, it's a kind.
            if term.as_ref().is_type0() {
                return false;
            }
            // Reject Pi types (function kinds like Type -> Type).
            // These are higher kinds, not types that can implement typeclasses.
            if matches!(
                term.as_ref().decompose(),
                Decomposition::Pi(_, _) | Decomposition::Lambda(_, _)
            ) {
                return false;
            }
            // Check if the term itself is a ground type symbol (like MyType)
            if let Some(ground_id) = term.as_ref().as_type_atom() {
                // term IS a type (like MyType) - check if it implements the typeclass
                if !self
                    .kernel_context
                    .type_store
                    .is_instance_of(ground_id, typeclass_id)
                {
                    return false; // Type doesn't implement the required typeclass
                }
            } else if let Some(out_var_id) = term.as_ref().atomic_variable() {
                // term is a type variable - check if we need to propagate constraints
                let term_type =
                    term.get_type_with_context(&self.output_context, self.kernel_context);
                if let Some(other_tc) = term_type.as_ref().as_typeclass() {
                    // Output variable also has a typeclass constraint - check compatibility
                    if typeclass_id != other_tc {
                        let other_extends_var = self
                            .kernel_context
                            .type_store
                            .typeclass_extends(other_tc, typeclass_id);
                        let var_extends_other = self
                            .kernel_context
                            .type_store
                            .typeclass_extends(typeclass_id, other_tc);

                        if !other_extends_var && !var_extends_other {
                            // Incompatible typeclasses
                            return false;
                        }

                        // If var's typeclass is more specific (extends other), update
                        // the output variable's type to use the more specific constraint.
                        if var_extends_other && !other_extends_var {
                            self.output_context
                                .set_type(out_var_id as usize, var_type.clone());
                        }
                    }
                }
                // If term_type is TypeSort or something else, allow it (constraint
                // propagation would be needed for full checking)
            } else if matches!(
                term.as_ref().decompose(),
                Decomposition::Atom(Atom::Symbol(Symbol::Bool))
                    | Decomposition::Atom(Atom::Symbol(Symbol::Empty))
            ) {
                // Built-in types (Bool, Empty) don't implement any typeclasses
                return false;
            } else {
                // term is not a simple type - check its type
                let term_type =
                    term.get_type_with_context(&self.output_context, self.kernel_context);
                if let Some(other_tc) = term_type.as_ref().as_typeclass() {
                    // term has a typeclass type - check compatibility
                    // Either other_tc extends typeclass_id (term is more specific), or
                    // typeclass_id extends other_tc (var is more specific).
                    if typeclass_id != other_tc {
                        let other_extends_var = self
                            .kernel_context
                            .type_store
                            .typeclass_extends(other_tc, typeclass_id);
                        let var_extends_other = self
                            .kernel_context
                            .type_store
                            .typeclass_extends(typeclass_id, other_tc);

                        if !other_extends_var && !var_extends_other {
                            // Incompatible typeclasses
                            return false;
                        }

                        // If var's typeclass is more specific (extends other), update
                        // the output variable's type to use the more specific constraint.
                        if var_extends_other && !other_extends_var {
                            if let Some(out_var_id) = term.atomic_variable() {
                                self.output_context
                                    .set_type(out_var_id as usize, var_type.clone());
                            }
                        }
                    }
                } else if !term_type.as_ref().is_type0() {
                    // term's type is not TypeSort or a typeclass - reject
                    return false;
                }
                // If term_type is TypeSort, we can't verify the constraint statically
                // (would need to check at runtime or add constraint propagation)
            }
        } else {
            // Normal type unification (no typeclass constraint)
            let term_type = term.get_type_with_context(&self.output_context, self.kernel_context);
            if !self.unify_internal(
                var_scope,
                var_type.as_ref(),
                Scope::OUTPUT,
                term_type.as_ref(),
            ) {
                return false;
            }
        }

        // After type unification, apply any output substitutions to get the final term.
        // Type unification may have called remap() which substitutes output variables,
        // but those substitutions aren't reflected in our local `term` variable.
        let final_term = self.apply(Scope::OUTPUT, term);
        self.set_mapping(var_scope, var_id, final_term);
        true
    }

    // Returns whether they can be unified.
    fn unify_atoms(&mut self, scope1: Scope, atom1: &Atom, scope2: Scope, atom2: &Atom) -> bool {
        // Free variables can be unified with anything
        if let Atom::FreeVariable(i) = atom1 {
            return self.unify_variable(scope1, *i, scope2, &Term::atom(*atom2));
        }
        if let Atom::FreeVariable(i) = atom2 {
            return self.unify_variable(scope2, *i, scope1, &Term::atom(*atom1));
        }
        // Bound variables are structurally matched - they unify only if identical
        // (same index). They do NOT participate in variable substitution.
        if atom1 == atom2 {
            return true;
        }
        // Special case: Typeclass is compatible with TypeSort
        // A Typeclass constraint is a refinement of TypeSort, not a different type.
        // When unifying types, Typeclass(X) should match TypeSort.
        if matches!(atom1, Atom::Symbol(Symbol::Typeclass(_)))
            && matches!(atom2, Atom::Symbol(Symbol::Type0))
        {
            return true;
        }
        if matches!(atom2, Atom::Symbol(Symbol::Typeclass(_)))
            && matches!(atom1, Atom::Symbol(Symbol::Type0))
        {
            return true;
        }
        false
    }

    // Public interface for unification
    // Does not allow unification with the output scope - callers should not directly
    // provide terms in the output scope as the unifier manages output variables internally
    pub fn unify(&mut self, scope1: Scope, term1: &Term, scope2: Scope, term2: &Term) -> bool {
        if scope1 == Scope::OUTPUT || scope2 == Scope::OUTPUT {
            panic!("Cannot call unify with output scope - the unifier manages output variables internally");
        }
        self.unify_internal(scope1, term1.as_ref(), scope2, term2.as_ref())
    }

    // Internal unification implementation
    fn unify_internal(
        &mut self,
        scope1: Scope,
        term1: TermRef,
        scope2: Scope,
        term2: TermRef,
    ) -> bool {
        // Handle the case where we're unifying something with an atomic variable
        if let Some(i) = term1.atomic_variable() {
            return self.unify_variable(scope1, i, scope2, &term2.to_owned());
        }
        if let Some(i) = term2.atomic_variable() {
            return self.unify_variable(scope2, i, scope1, &term1.to_owned());
        }

        match (term1.decompose(), term2.decompose()) {
            (Decomposition::Atom(a1), Decomposition::Atom(a2)) => {
                // This case is now only for variables, handled by unify_atoms
                self.unify_atoms(scope1, a1, scope2, a2)
            }
            (Decomposition::Application(f1, a1), Decomposition::Application(f2, a2)) => {
                self.unify_internal(scope1, f1, scope2, f2)
                    && self.unify_internal(scope1, a1, scope2, a2)
            }
            (Decomposition::Pi(i1, o1), Decomposition::Pi(i2, o2)) => {
                self.unify_internal(scope1, i1, scope2, i2)
                    && self.unify_internal(scope1, o1, scope2, o2)
            }
            (Decomposition::Lambda(i1, b1), Decomposition::Lambda(i2, b2)) => {
                self.unify_internal(scope1, i1, scope2, i2)
                    && self.unify_internal(scope1, b1, scope2, b2)
            }
            // Structural mismatch (e.g., Atom vs Application, Application vs Pi)
            _ => false,
        }
    }

    /// Doesn't worry about literal sign.
    pub fn unify_literals(
        &mut self,
        scope1: Scope,
        literal1: &Literal,
        scope2: Scope,
        literal2: &Literal,
        flipped: bool,
    ) -> bool {
        if flipped {
            // If we're flipped, swap the literals.
            self.unify_internal(
                scope1,
                literal1.right.as_ref(),
                scope2,
                literal2.left.as_ref(),
            ) && self.unify_internal(
                scope1,
                literal1.left.as_ref(),
                scope2,
                literal2.right.as_ref(),
            )
        } else {
            // If we're not flipped, keep the literals as they are.
            self.unify_internal(
                scope1,
                literal1.left.as_ref(),
                scope2,
                literal2.left.as_ref(),
            ) && self.unify_internal(
                scope1,
                literal1.right.as_ref(),
                scope2,
                literal2.right.as_ref(),
            )
        }
    }

    /// Tries to unify a left clause and a right clause.
    /// Does not reorder anything.
    pub fn unify_clauses(left: &Clause, right: &Clause, kernel_context: &KernelContext) -> bool {
        if left.literals.len() != right.literals.len() {
            return false;
        }
        let mut unifier = Unifier::new(3, kernel_context);
        unifier.set_input_context(Scope::LEFT, left.get_local_context());
        unifier.set_input_context(Scope::RIGHT, right.get_local_context());
        for (lit1, lit2) in left.literals.iter().zip(right.literals.iter()) {
            if !unifier.unify_literals(Scope::LEFT, lit1, Scope::RIGHT, lit2, false) {
                return false;
            }
        }
        true
    }

    pub fn assert_unify(&mut self, scope1: Scope, term1: &Term, scope2: Scope, term2: &Term) {
        assert!(
            self.unify(scope1, term1, scope2, term2),
            "Failed to unify {} and {}",
            term1,
            term2
        );

        let out1 = self.apply(scope1, term1);
        let out2 = self.apply(scope2, term2);
        assert_eq!(
            out1, out2,
            "Unification of {} and {} produced different results: {} and {}",
            term1, term2, out1, out2
        );
    }

    pub fn into_one_map(self, scope: Scope) -> VariableMap {
        self.maps.into_iter().nth(scope.get()).unwrap()
    }

    /// Like into_one_map, but also returns the output context.
    /// This is needed because VariableMap replacement terms reference
    /// variables in the unifier's output context.
    pub fn into_one_map_with_context(self, scope: Scope) -> (VariableMap, LocalContext) {
        let map = self.maps.into_iter().nth(scope.get()).unwrap();
        (map, self.output_context)
    }
}

impl fmt::Display for Unifier<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Unifier:")?;
        for (scope, map) in self.maps.iter().enumerate() {
            write!(f, "  {:?}: {}", Scope(scope), map)?;
            if scope < self.maps.len() - 1 {
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::ModuleId;
    use std::sync::LazyLock;

    fn bool_fn(head: Atom, args: Vec<Term>) -> Term {
        Term::new(head, args)
    }

    /// Creates a test KernelContext with proper function types for testing.
    /// g0: (Bool, Bool) -> Bool
    /// g1: Bool -> Bool
    /// g2: (Bool, Bool, Bool) -> Bool
    fn test_ctx() -> KernelContext {
        KernelContext::test_with_function_types()
    }

    /// Returns a static LocalContext with 10 Bool types for tests.
    fn bool_context() -> &'static LocalContext {
        static BOOL_CONTEXT: LazyLock<LocalContext> =
            LazyLock::new(|| LocalContext::from_types(vec![Term::bool_type(); 10]));
        &BOOL_CONTEXT
    }

    /// Creates a test unifier with BOOL types for variables.
    /// Use this for tests that explicitly construct terms with BOOL types.
    fn test_unifier_bool<'a>(kernel_context: &'a KernelContext) -> Unifier<'a> {
        let mut u = Unifier::new(3, kernel_context);
        u.set_input_context(Scope::LEFT, bool_context());
        u.set_input_context(Scope::RIGHT, bool_context());
        u.set_output_var_types(vec![Term::bool_type(); 10]);
        u
    }

    #[test]
    fn test_unifying_variables() {
        let ctx = test_ctx();
        let bool0 = Term::atom(Atom::FreeVariable(0));
        let bool1 = Term::atom(Atom::FreeVariable(1));
        let bool2 = Term::atom(Atom::FreeVariable(2));
        let fterm = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![bool0.clone(), bool1.clone()],
        );
        let mut u = test_unifier_bool(&ctx);

        // Replace x0 with x1 and x1 with x2.
        assert!(u.unify_variable(Scope::LEFT, 0, Scope::OUTPUT, &bool1));
        assert!(u.unify_variable(Scope::LEFT, 1, Scope::OUTPUT, &bool2));
        let term = u.apply(Scope::LEFT, &fterm);
        assert_eq!(format!("{}", term), "g0_0(x1, x2)");
    }

    #[test]
    fn test_same_scope() {
        let ctx = test_ctx();
        let bool0 = Term::atom(Atom::FreeVariable(0));
        let bool1 = Term::atom(Atom::FreeVariable(1));
        let bool2 = Term::atom(Atom::FreeVariable(2));
        let term1 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![bool0.clone(), bool1.clone()],
        );
        let term2 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![bool1.clone(), bool2.clone()],
        );
        let mut u = test_unifier_bool(&ctx);

        u.assert_unify(Scope::LEFT, &term1, Scope::LEFT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0_0(x0, x0)");
        let new2 = u.apply(Scope::LEFT, &term2);
        assert_eq!(format!("{}", new2), "g0_0(x0, x0)");
    }

    #[test]
    fn test_different_scope() {
        let ctx = test_ctx();
        let bool0 = Term::atom(Atom::FreeVariable(0));
        let bool1 = Term::atom(Atom::FreeVariable(1));
        let bool2 = Term::atom(Atom::FreeVariable(2));
        let term1 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![bool0.clone(), bool1.clone()],
        );
        let term2 = bool_fn(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![bool1.clone(), bool2.clone()],
        );
        let mut u = test_unifier_bool(&ctx);

        u.assert_unify(Scope::LEFT, &term1, Scope::RIGHT, &term2);
        let new1 = u.apply(Scope::LEFT, &term1);
        assert_eq!(format!("{}", new1), "g0_0(x0, x1)");
        let new2 = u.apply(Scope::RIGHT, &term2);
        assert_eq!(format!("{}", new2), "g0_0(x0, x1)");
    }

    #[test]
    fn test_unifying_functional_variable() {
        // This test checks that a variable can unify with a constant in functional position.
        // Variable(1) should unify with GlobalConstant(3), both with type Empty -> Bool.
        let ctx = test_ctx();
        // g3 has type Empty -> Bool
        let empty_to_bool = ctx
            .symbol_table
            .get_type(Symbol::GlobalConstant(ModuleId(0), 3))
            .clone();

        let empty0 = Term::atom(Atom::FreeVariable(0));
        let const_f_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 3)),
            vec![empty0.clone()],
        );
        let var_f_term = Term::new(Atom::FreeVariable(1), vec![empty0.clone()]);

        // Set up a unifier where Variable(0) has EMPTY type and Variable(1) has Empty -> Bool type
        let mut u = Unifier::new(3, &ctx);
        // x0: EMPTY, x1: Empty -> Bool
        let local_ctx = LocalContext::from_types(vec![Term::empty_type(), empty_to_bool]);
        let local_ctx_ref: &'static LocalContext = Box::leak(Box::new(local_ctx));
        u.set_input_context(Scope::LEFT, local_ctx_ref);
        u.set_input_context(Scope::RIGHT, local_ctx_ref);
        u.set_output_var_types(vec![Term::empty_type(); 10]);
        u.assert_unify(Scope::LEFT, &const_f_term, Scope::RIGHT, &var_f_term);
    }

    #[test]
    fn test_nested_functional_unify() {
        use crate::kernel::local_context::LocalContext;

        // Test: unify x0(x0(c5)) with c1(x0(x1))
        // x0 should map to c1, x1 should map to c5
        // x0 has type Bool -> Bool, x1 has type Bool
        // c1 is Bool -> Bool, c5 is Bool
        let ctx = test_ctx();
        let bool_to_bool = ctx.symbol_table.get_type(Symbol::ScopedConstant(1)).clone();

        // Create local context where x0: Bool -> Bool, x1: Bool
        let local_ctx = LocalContext::from_types(vec![bool_to_bool.clone(), Term::bool_type()]);
        let local_ctx_ref: &'static LocalContext = Box::leak(Box::new(local_ctx));

        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));
        let x1_var = Term::atom(Atom::FreeVariable(1));

        // left_term = x0(x0(c5)) where x0 has type Bool -> Bool
        let inner = Term::new(Atom::FreeVariable(0), vec![c5.clone()]);
        let left_term = Term::new(Atom::FreeVariable(0), vec![inner]);

        // right_term = c1(x0(x1)) where c1: Bool -> Bool
        let x0_x1 = Term::new(Atom::FreeVariable(0), vec![x1_var.clone()]);
        let right_term = Term::new(Atom::Symbol(Symbol::ScopedConstant(1)), vec![x0_x1]);

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, local_ctx_ref);
        u.set_input_context(Scope::RIGHT, local_ctx_ref);
        u.set_output_var_types(vec![
            bool_to_bool,
            Term::bool_type(),
            Term::bool_type(),
            Term::bool_type(),
            Term::bool_type(),
        ]);

        u.assert_unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);
        u.print();
        assert!(u.get_mapping(Scope::LEFT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 0).unwrap().to_string() == "c1");
        assert!(u.get_mapping(Scope::RIGHT, 1).unwrap().to_string() == "c5");
    }

    // Tests that nested functional terms with function-typed variables can be unified.
    // Uses test_with_function_types where g1: Bool -> Bool.
    // We construct terms where x0 has type Bool -> Bool so x0(x0(x1)) is valid.
    #[test]
    fn test_nested_functional_superpose() {
        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_type(Symbol::GlobalConstant(ModuleId(0), 1))
            .clone(); // g1: Bool -> Bool

        // Create local context where x0 has type Bool -> Bool, x1 has type Bool
        let lctx = LocalContext::from_types(vec![bool_to_bool.clone(), Term::bool_type()]);

        // Build terms: s = x0(x0(x1)) where x0: Bool -> Bool, x1: Bool
        // x0(x1) : Bool, x0(x0(x1)) : Bool
        let x1 = Term::atom(Atom::FreeVariable(1));
        let x0_x1 = Term::new(Atom::FreeVariable(0), vec![x1.clone()]);
        let s = Term::new(Atom::FreeVariable(0), vec![x0_x1.clone()]);

        // u_subterm = g1(x0(x1))
        let u_subterm = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1)),
            vec![x0_x1.clone()],
        );

        // Test that s = x0(x0(x1)) unifies with u_subterm = g1(x0(x1))
        // This should succeed with x0 mapping to g1
        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(lctx.clone())));
        u.set_output_var_types(vec![
            bool_to_bool,
            Term::bool_type(),
            Term::bool_type(),
            Term::bool_type(),
        ]);

        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();

        // Check that x0 in LEFT maps to g1
        let x0_mapping = u.get_mapping(Scope::LEFT, 0);
        assert!(x0_mapping.is_some(), "x0 should have a mapping");
        assert_eq!(
            x0_mapping.unwrap().to_string(),
            "g0_1",
            "x0 should map to g1"
        );
    }

    // Tests higher-order partial application unification.
    // Uses test_with_function_types where:
    // - g0, c0: (Bool, Bool) -> Bool
    // - g1, c1: Bool -> Bool
    // - c5-c9: Bool
    #[test]
    fn test_higher_order_partial_application_unification() {
        // We want to test unifying terms where a function variable gets bound to a partial application.
        // Using test_with_function_types:
        // - g0: (Bool, Bool) -> Bool
        // - Partial application g0(c5) gives Bool -> Bool
        //
        // We'll unify: x0(c6) with g0(c5, c6)
        // where x0 should map to g0(c5) (a partial application)

        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_type(Symbol::GlobalConstant(ModuleId(0), 1))
            .clone(); // g1: Bool -> Bool

        // c5, c6 are Bool constants
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));
        let c6 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(6)));

        // Left side: x0(c6) where x0: Bool -> Bool
        let left_local = LocalContext::from_types(vec![bool_to_bool.clone()]);
        let left_term = Term::new(Atom::FreeVariable(0), vec![c6.clone()]);

        // Right side: g0(c5, c6) : Bool
        // This is the full application
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![c5.clone(), c6.clone()],
        );

        // Right side has no variables
        let right_local = LocalContext::empty();

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(left_local)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(right_local)));
        u.set_output_var_types(vec![bool_to_bool, Term::bool_type(), Term::bool_type()]);

        let result = u.unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);

        // This should succeed, with x0 mapping to g0(c5)
        assert!(result, "Should be able to unify x0(c6) with g0(c5, c6)");

        // Check that x0 maps to g0(c5)
        if result {
            let x0_mapping = u.get_mapping(Scope::LEFT, 0);
            assert!(x0_mapping.is_some(), "x0 should have a mapping");
            let mapping_str = x0_mapping.unwrap().to_string();
            assert_eq!(mapping_str, "g0_0(c5)", "x0 should map to g0(c5)");
        }
    }

    // Tests unification of terms that would be used in superposition.
    // This is a simplified version of the original test, focusing on unification correctness.
    // Uses test_with_function_types where g1: Bool -> Bool.
    #[test]
    fn test_original_superpose() {
        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_type(Symbol::GlobalConstant(ModuleId(0), 1))
            .clone(); // g1: Bool -> Bool

        // Create local context where x0 has type Bool -> Bool, x1 has type Bool
        let lctx = LocalContext::from_types(vec![bool_to_bool.clone(), Term::bool_type()]);

        // Build terms: s = x0(x0(x1)) where x0: Bool -> Bool, x1: Bool
        let x0_x1 = Term::new(
            Atom::FreeVariable(0),
            vec![Term::atom(Atom::FreeVariable(1))],
        );
        let s = Term::new(Atom::FreeVariable(0), vec![x0_x1.clone()]);

        // u_subterm = g1(x0(x1))
        let u_subterm = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1)),
            vec![x0_x1.clone()],
        );

        // Test that s = x0(x0(x1)) unifies with u_subterm = g1(x0(x1))
        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(lctx.clone())));
        u.set_output_var_types(vec![
            bool_to_bool,
            Term::bool_type(),
            Term::bool_type(),
            Term::bool_type(),
        ]);

        u.assert_unify(Scope::LEFT, &s, Scope::RIGHT, &u_subterm);
        u.print();

        // Now test that we can apply the unification to create a result
        let applied_s = u.apply(Scope::LEFT, &s);
        let applied_u = u.apply(Scope::RIGHT, &u_subterm);

        // After unification, both should have the same result
        // x0 -> g1, so s becomes g1(g1(x1)) and u_subterm becomes g1(g1(x1))
        assert_eq!(
            applied_s.to_string(),
            applied_u.to_string(),
            "After unification, both terms should apply to the same result"
        );
    }

    #[test]
    fn test_mutual_containment_invalid_1() {
        // Test: c0(x0, c0(x1, c1(x2))) should not unify with c0(c0(x2, x1), x0)
        // Using g0 which has type (Bool, Bool) -> Bool for c0-like behavior
        // Using g1 which has type Bool -> Bool for c1-like behavior
        let ctx = test_ctx();

        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        let x2 = Term::atom(Atom::FreeVariable(2));

        // c1(x2) -> g1(x2)
        let g1_x2 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1)),
            vec![x2.clone()],
        );
        // c0(x1, c1(x2)) -> g0(x1, g1(x2))
        let inner = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x1.clone(), g1_x2],
        );
        // c0(x0, c0(x1, c1(x2))) -> g0(x0, g0(x1, g1(x2)))
        let left_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x0.clone(), inner],
        );

        // c0(x2, x1) -> g0(x2, x1)
        let g0_x2_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x2.clone(), x1.clone()],
        );
        // c0(c0(x2, x1), x0) -> g0(g0(x2, x1), x0)
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![g0_x2_x1, x0.clone()],
        );

        let mut u = test_unifier_bool(&ctx);
        let result = u.unify(Scope::LEFT, &left_term, Scope::LEFT, &right_term);
        assert!(!result, "Mutual containment should not unify");
    }

    #[test]
    fn test_mutual_containment_invalid_2() {
        // Test: c0(c0(x0, c1(x1)), x2) should not unify with c0(x2, c0(x1, x0))
        let ctx = test_ctx();

        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        let x2 = Term::atom(Atom::FreeVariable(2));

        // c1(x1) -> g1(x1)
        let g1_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1)),
            vec![x1.clone()],
        );
        // c0(x0, c1(x1)) -> g0(x0, g1(x1))
        let inner_left = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x0.clone(), g1_x1],
        );
        // c0(c0(x0, c1(x1)), x2) -> g0(g0(x0, g1(x1)), x2)
        let left_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![inner_left, x2.clone()],
        );

        // c0(x1, x0) -> g0(x1, x0)
        let inner_right = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x1.clone(), x0.clone()],
        );
        // c0(x2, c0(x1, x0)) -> g0(x2, g0(x1, x0))
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x2.clone(), inner_right],
        );

        let mut u = test_unifier_bool(&ctx);
        let result = u.unify(Scope::LEFT, &left_term, Scope::LEFT, &right_term);
        assert!(!result, "Mutual containment should not unify");
    }

    #[test]
    fn test_recursive_reference_in_output() {
        // Test: g2(x0, x0) should not unify with g2(g2(g1(c0, x0), x0), g2(x1, x1))
        // g2 has type (Bool, Bool, Bool) -> Bool, but we need (Bool, Bool) -> Bool
        // So we use g0 instead
        let ctx = test_ctx();

        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5))); // c5 is Bool

        // Left: g0(x0, x0)
        let left_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x0.clone(), x0.clone()],
        );

        // g1(c5) -> this doesn't fit since g1 has Bool -> Bool but we need a different structure
        // Original was g2(g2(g1(c0, x0), x0), g2(x1, x1)) which uses g1 with 2 args
        // Let's simplify: g0(g0(g0(c5, x0), x0), g0(x1, x1))
        let g0_c5_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![c5.clone(), x0.clone()],
        );
        let g0_inner_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![g0_c5_x0, x0.clone()],
        );
        let g0_x1_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x1.clone(), x1.clone()],
        );
        let right_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![g0_inner_x0, g0_x1_x1],
        );

        let mut u = test_unifier_bool(&ctx);
        let result = u.unify(Scope::LEFT, &left_term, Scope::RIGHT, &right_term);
        assert!(!result, "Recursive reference should not unify");
    }

    #[test]
    fn test_parameterized_type_unification() {
        // Test unifying a constant of type List[Int] with a variable of type List[x0]
        // where x0 is a type variable. This tests that polymorphic types work in unification.
        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("List", 1).parse_datatype("Int");

        let list_id = ctx.type_store.get_ground_id_by_name("List").unwrap();
        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();

        // c0 has type List[Int]
        let list_int = Term::new(
            Atom::Symbol(Symbol::Type(list_id)),
            vec![Term::ground_type(int_id)],
        );
        ctx.symbol_table.add_scoped_constant(list_int.clone());

        // Create LocalContext where:
        // x0 : Type (a type variable)
        // x1 : List[x0] (a list parameterized by x0)
        let type_type = Term::type_sort();
        let list_x0 = Term::new(
            Atom::Symbol(Symbol::Type(list_id)),
            vec![Term::atom(Atom::FreeVariable(0))],
        );
        let local_ctx = LocalContext::from_types(vec![type_type.clone(), list_x0.clone()]);

        // c0 : List[Int]
        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        // x1 : List[x0]
        let x1 = Term::atom(Atom::FreeVariable(1));

        // Try to unify c0 with x1
        // c0 has type List[Int], x1 has type List[x0]
        // These should unify with x0 -> Int
        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(local_ctx.clone())));
        u.set_output_var_types(vec![type_type.clone(), list_int.clone()]);

        let result = u.unify(Scope::LEFT, &c0, Scope::RIGHT, &x1);
        assert!(
            result,
            "Should unify c0 : List[Int] with x1 : List[x0], binding x0 to Int"
        );

        // After unification, x1 should map to c0
        let x1_mapping = u.get_mapping(Scope::RIGHT, 1);
        assert!(x1_mapping.is_some(), "x1 should have a mapping");
    }

    #[test]
    fn test_type_variable_inconsistency_bug() {
        // This test checks for a bug where type variables in different scopes
        // get bound to different concrete types, but the raw types still compare equal.
        //
        // Scenario:
        // - LEFT and RIGHT both have x0: Type, x1: List[x0]
        // - We bind x0 in LEFT to Int (by unifying x0 with Int)
        // - We bind x0 in RIGHT to Nat (by unifying x0 with Nat)
        // - Now x1 in LEFT has effective type List[Int]
        // - And x1 in RIGHT has effective type List[Nat]
        // - Unifying x1 (LEFT) with x1 (RIGHT) should FAIL because the types differ
        // - But if we only compare raw types (List[x0] == List[x0]), it would wrongly succeed
        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("List", 1)
            .parse_datatype("Int")
            .parse_datatype("Nat");

        let list_id = ctx.type_store.get_ground_id_by_name("List").unwrap();
        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();
        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();

        let type_type = Term::type_sort();
        let int_type = Term::ground_type(int_id);
        let nat_type = Term::ground_type(nat_id);

        // List[x0] - a list parameterized by type variable x0
        let list_x0 = Term::new(
            Atom::Symbol(Symbol::Type(list_id)),
            vec![Term::atom(Atom::FreeVariable(0))],
        );

        // LocalContext: x0: Type, x1: List[x0]
        let local_ctx = LocalContext::from_types(vec![type_type.clone(), list_x0.clone()]);

        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(local_ctx.clone())));
        u.set_output_var_types(vec![type_type.clone(), type_type.clone()]);

        // Bind x0 in LEFT to Int
        assert!(
            u.unify(Scope::LEFT, &x0, Scope::LEFT, &int_type),
            "Should unify x0 with Int in LEFT"
        );

        // Bind x0 in RIGHT to Nat
        assert!(
            u.unify(Scope::RIGHT, &x0, Scope::RIGHT, &nat_type),
            "Should unify x0 with Nat in RIGHT"
        );

        // Now x1 in LEFT has effective type List[Int]
        // And x1 in RIGHT has effective type List[Nat]
        // These should NOT unify!
        let result = u.unify(Scope::LEFT, &x1, Scope::RIGHT, &x1);
        assert!(
            !result,
            "Should NOT unify x1:List[Int] (LEFT) with x1:List[Nat] (RIGHT) - types differ after substitution"
        );
    }

    #[test]
    fn test_type_mismatch_prevents_unification() {
        // Test that a variable of type Int cannot unify with a constant of type Nat.
        // This verifies that type checking is working correctly in unification.
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Int").parse_datatype("Nat");

        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();
        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();

        let int_type = Term::ground_type(int_id);
        let nat_type = Term::ground_type(nat_id);

        // c0 has type Nat
        ctx.symbol_table.add_scoped_constant(nat_type.clone());

        // x0 has type Int
        let local_ctx = LocalContext::from_types(vec![int_type.clone()]);

        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        let x0 = Term::atom(Atom::FreeVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(local_ctx.clone())));
        u.set_output_var_types(vec![int_type.clone()]);

        // x0: Int should NOT unify with c0: Nat
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &c0);
        assert!(
            !result,
            "Should NOT unify x0:Int with c0:Nat - types differ"
        );
    }

    #[test]
    fn test_initializing_with_variables_in_map() {
        // Test initializing a unifier with pre-existing variable mappings
        let ctx = test_ctx();

        // Create a term for the initial mapping using only atomic synthetics
        // Use g2(x0, x1, s4) instead of s0(x0, x1, s4) since g2 has proper function type
        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        let s4 = Term::atom(Atom::Symbol(Symbol::Synthetic(ModuleId(0), 4))); // BOOL type
        let g2_term = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 2)),
            vec![x0.clone(), x1.clone(), s4.clone()],
        );

        let mut initial_map = VariableMap::new();
        initial_map.set(0, g2_term);

        let output_context = initial_map.build_output_context(bool_context());
        let (mut unifier, scope1) = Unifier::with_map(initial_map, &ctx, output_context);
        unifier.set_input_context(scope1, bool_context());
        let scope2 = unifier.add_scope();
        unifier.set_input_context(scope2, bool_context());
        let scope3 = unifier.add_scope();
        unifier.set_input_context(scope3, bool_context());
        unifier.set_output_var_types(vec![Term::bool_type(); 10]);

        // Unify g0(x0, x1) with g0(c5, x0)
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));
        let g0_x0_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x0.clone(), x1.clone()],
        );
        let g0_c5_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![c5.clone(), x0.clone()],
        );
        assert!(unifier.unify(scope2, &g0_x0_x1, scope3, &g0_c5_x0));

        // Unify g0(x2, x1) with g0(s4, x0)
        let x2 = Term::atom(Atom::FreeVariable(2));
        let g0_x2_x1 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![x2.clone(), x1.clone()],
        );
        let g0_s4_x0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![s4.clone(), x0.clone()],
        );
        assert!(unifier.unify(scope2, &g0_x2_x1, scope1, &g0_s4_x0));
    }

    #[test]
    fn test_unify_typeclass_variable_with_instance() {
        // Test: x0 with type Monoid unifies with Int (the type) when Int is an instance of Monoid
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Int");

        let int_id = ctx.type_store.get_ground_id_by_name("Int").unwrap();
        let int_type = Term::ground_type(int_id);

        // Register a Monoid typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = ctx.type_store.add_typeclass(&monoid);

        // Make Int an instance of Monoid
        use crate::elaborator::acorn_type::{AcornType, Datatype};
        let int_acorn = AcornType::Data(
            Datatype {
                module_id: ModuleId(0),
                name: "Int".to_string(),
            },
            vec![],
        );
        ctx.type_store.add_type_instance(&int_acorn, monoid_id);

        // x0 has typeclass constraint Monoid (its "type" is the typeclass)
        let typeclass_type = Term::typeclass(monoid_id);
        let local_ctx = LocalContext::from_types(vec![typeclass_type.clone()]);

        let x0 = Term::atom(Atom::FreeVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![int_type.clone()]);

        // x0: Monoid should unify with Int (the type), since Int is a Monoid instance
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &int_type);
        assert!(
            result,
            "x0: Monoid should unify with Int (type) when Int is an instance of Monoid"
        );
    }

    #[test]
    fn test_unify_typeclass_variable_with_non_instance() {
        // Test: x0 with type Monoid should NOT unify with String (the type) when String is not an instance
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut ctx = KernelContext::new();
        ctx.parse_datatype("String");

        let string_id = ctx.type_store.get_ground_id_by_name("String").unwrap();
        let string_type = Term::ground_type(string_id);

        // Register a Monoid typeclass but don't add String as an instance
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = ctx.type_store.add_typeclass(&monoid);

        // x0 has typeclass constraint Monoid
        let typeclass_type = Term::typeclass(monoid_id);
        let local_ctx = LocalContext::from_types(vec![typeclass_type.clone()]);

        let x0 = Term::atom(Atom::FreeVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![string_type.clone()]);

        // x0: Monoid should NOT unify with String (the type), since String is not a Monoid instance
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &string_type);
        assert!(
            !result,
            "x0: Monoid should NOT unify with String (type) when String is not an instance of Monoid"
        );
    }

    #[test]
    fn test_unify_typeclass_variable_rejects_typesort() {
        // Test: x0 with type Monoid should NOT unify with TypeSort
        // TypeSort is the "type of types" (a kind), not a type that implements any typeclass.
        // This was a bug where backwards rewriting produced ill-typed terms like g1(g1(Type)).
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut ctx = KernelContext::new();

        // Register a Monoid typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = ctx.type_store.add_typeclass(&monoid);

        // x0 has typeclass constraint Monoid (its "type" is the typeclass)
        let typeclass_type = Term::typeclass(monoid_id);
        let local_ctx = LocalContext::from_types(vec![typeclass_type.clone()]);

        let x0 = Term::atom(Atom::FreeVariable(0));
        let type_sort = Term::type_sort();

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![type_sort.clone()]);

        // x0: Monoid should NOT unify with TypeSort
        // TypeSort is not a type - it's a kind (the type of types)
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &type_sort);
        assert!(
            !result,
            "x0: Monoid should NOT unify with TypeSort - TypeSort is a kind, not a type"
        );
    }

    #[test]
    fn test_unify_type_variable_rejects_typesort() {
        // Test: x0 with type TypeSort (a type variable) should NOT unify with TypeSort itself
        // x0: TypeSort means x0 can be any type like Nat, Bool, etc.
        // TypeSort is NOT a type - it's the kind of types.
        // This prevents universe-level confusion.
        let ctx = KernelContext::new();

        // x0 has type TypeSort (i.e., x0 is a type variable)
        let local_ctx = LocalContext::from_types(vec![Term::type_sort()]);

        let x0 = Term::atom(Atom::FreeVariable(0));
        let type_sort = Term::type_sort();

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![type_sort.clone()]);

        // x0: TypeSort should NOT unify with TypeSort
        // TypeSort is a kind, not a type, so it can't be bound to a type variable
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &type_sort);
        assert!(
            !result,
            "x0: TypeSort should NOT unify with TypeSort - TypeSort is a kind, not a type"
        );
    }

    #[test]
    fn test_unify_typeclass_variables_compatible() {
        // Test: two variables with the same typeclass constraint can unify
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut ctx = KernelContext::new();

        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = ctx.type_store.add_typeclass(&monoid);
        let typeclass_type = Term::typeclass(monoid_id);

        // Both x0 and x1 have typeclass constraint Monoid
        let left_ctx = LocalContext::from_types(vec![typeclass_type.clone()]);
        let right_ctx = LocalContext::from_types(vec![typeclass_type.clone()]);

        let x0_left = Term::atom(Atom::FreeVariable(0));
        let x0_right = Term::atom(Atom::FreeVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(left_ctx)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(right_ctx)));
        u.set_output_var_types(vec![typeclass_type.clone()]);

        // x0: Monoid (LEFT) should unify with x0: Monoid (RIGHT)
        let result = u.unify(Scope::LEFT, &x0_left, Scope::RIGHT, &x0_right);
        assert!(
            result,
            "Two variables with the same typeclass constraint should unify"
        );
    }

    #[test]
    fn test_unify_dependent_type_fin() {
        // Test: Fin[x0] where x0: Nat unifies with Fin[c0] where c0: Nat
        // This tests dependent types where the type parameter is a value, not a type

        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("Fin", 1); // Fin takes 1 parameter
        ctx.parse_datatype("Nat");

        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);
        let fin_id = ctx.type_store.get_ground_id_by_name("Fin").unwrap();

        // c0 has type Nat (a value, not a type)
        ctx.symbol_table.add_scoped_constant(nat_type.clone());

        // Create Fin[x0] where x0: Nat
        let x0 = Term::atom(Atom::FreeVariable(0));
        let fin_x0 = Term::new(Atom::Symbol(Symbol::Type(fin_id)), vec![x0.clone()]);

        // Create Fin[c0] where c0: Nat
        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        let fin_c0 = Term::new(Atom::Symbol(Symbol::Type(fin_id)), vec![c0.clone()]);

        // LocalContext: x0 has type Nat
        let lctx = LocalContext::from_types(vec![nat_type.clone()]);

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![nat_type.clone()]);

        // Fin[x0] should unify with Fin[c0]
        assert!(
            u.unify(Scope::LEFT, &fin_x0, Scope::RIGHT, &fin_c0),
            "Fin[x0] should unify with Fin[c0] when both x0 and c0 have type Nat"
        );

        // Check the mapping: x0 should map to c0
        let mapping = u.get_mapping(Scope::LEFT, 0);
        assert!(mapping.is_some(), "x0 should have a mapping");
        assert_eq!(
            mapping.unwrap().as_ref().get_head_atom(),
            c0.as_ref().get_head_atom(),
            "x0 should map to c0"
        );
    }

    #[test]
    fn test_unify_dependent_type_same_structure() {
        // Test: Fin[c0] unifies with Fin[c0] (same value parameter)

        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("Fin", 1);
        ctx.parse_datatype("Nat");

        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);
        let fin_id = ctx.type_store.get_ground_id_by_name("Fin").unwrap();

        // c0 has type Nat
        ctx.symbol_table.add_scoped_constant(nat_type.clone());

        // Create Fin[c0] twice
        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        let fin_c0_left = Term::new(Atom::Symbol(Symbol::Type(fin_id)), vec![c0.clone()]);
        let fin_c0_right = Term::new(Atom::Symbol(Symbol::Type(fin_id)), vec![c0.clone()]);

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Fin[c0] should unify with Fin[c0]
        assert!(
            u.unify(Scope::LEFT, &fin_c0_left, Scope::RIGHT, &fin_c0_right),
            "Fin[c0] should unify with Fin[c0]"
        );
    }

    #[test]
    fn test_unify_dependent_type_different_values() {
        // Test: Fin[c0] does NOT unify with Fin[c1] (different value parameters)

        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("Fin", 1);
        ctx.parse_datatype("Nat");

        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);
        let fin_id = ctx.type_store.get_ground_id_by_name("Fin").unwrap();

        // c0 and c1 both have type Nat
        ctx.symbol_table.add_scoped_constant(nat_type.clone());
        ctx.symbol_table.add_scoped_constant(nat_type.clone());

        // Create Fin[c0] and Fin[c1]
        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        let c1 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(1)));
        let fin_c0 = Term::new(Atom::Symbol(Symbol::Type(fin_id)), vec![c0.clone()]);
        let fin_c1 = Term::new(Atom::Symbol(Symbol::Type(fin_id)), vec![c1.clone()]);

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Fin[c0] should NOT unify with Fin[c1]
        assert!(
            !u.unify(Scope::LEFT, &fin_c0, Scope::RIGHT, &fin_c1),
            "Fin[c0] should NOT unify with Fin[c1] when c0 != c1"
        );
    }

    #[test]
    fn test_unify_bound_variables() {
        // Test that bound variables unify only when they have the same index
        let ctx = KernelContext::new();

        // b0 should unify with b0
        let b0_left = Term::atom(Atom::BoundVariable(0));
        let b0_right = Term::atom(Atom::BoundVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        assert!(
            u.unify(Scope::LEFT, &b0_left, Scope::RIGHT, &b0_right),
            "b0 should unify with b0"
        );
    }

    #[test]
    fn test_unify_different_bound_variables() {
        // Test that bound variables with different indices do NOT unify
        let ctx = KernelContext::new();

        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        assert!(
            !u.unify(Scope::LEFT, &b0, Scope::RIGHT, &b1),
            "b0 should NOT unify with b1"
        );
    }

    #[test]
    fn test_unify_pi_with_bound_variables() {
        // Test that Pi types with bound variables unify correctly
        // Pi(Nat, b0) should unify with Pi(Nat, b0)
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Nat");

        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);

        // Create Pi(Nat, b0) - a dependent function type where output references the input
        let b0 = Term::atom(Atom::BoundVariable(0));
        let pi_left = Term::pi(nat_type.clone(), b0.clone());
        let pi_right = Term::pi(nat_type.clone(), b0.clone());

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        assert!(
            u.unify(Scope::LEFT, &pi_left, Scope::RIGHT, &pi_right),
            "Pi(Nat, b0) should unify with Pi(Nat, b0)"
        );
    }

    #[test]
    fn test_unify_pi_different_bound_indices_fail() {
        // Test that Pi types with different bound variable indices don't unify
        // Pi(Nat, b0) should NOT unify with Pi(Nat, b1)
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Nat");

        let nat_id = ctx.type_store.get_ground_id_by_name("Nat").unwrap();
        let nat_type = Term::ground_type(nat_id);

        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));
        let pi_b0 = Term::pi(nat_type.clone(), b0);
        let pi_b1 = Term::pi(nat_type.clone(), b1);

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        assert!(
            !u.unify(Scope::LEFT, &pi_b0, Scope::RIGHT, &pi_b1),
            "Pi(Nat, b0) should NOT unify with Pi(Nat, b1)"
        );
    }

    #[test]
    fn test_unify_dependent_pi_type() {
        // Test unifying two identical dependent Pi types:
        // Π (R : Ring), R -> R -> R
        // This should unify with itself
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Ring");

        let ring_id = ctx.type_store.get_ground_id_by_name("Ring").unwrap();
        let ring_type = Term::ground_type(ring_id);

        // Build: Pi(Ring, Pi(b0, Pi(b0, b0)))
        let b0 = Term::atom(Atom::BoundVariable(0));
        let inner = Term::pi(b0.clone(), Term::pi(b0.clone(), b0.clone()));
        let add_type = Term::pi(ring_type.clone(), inner.clone());

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Same dependent type should unify with itself
        assert!(
            u.unify(Scope::LEFT, &add_type, Scope::RIGHT, &add_type.clone()),
            "Dependent Pi type should unify with itself"
        );
    }

    #[test]
    fn test_apply_preserves_bound_variables() {
        // Test that applying a substitution to a Pi type preserves bound variables
        // If we have Pi(Ring, Pi(b0, b0)) and apply the unifier,
        // the b0's should be preserved (not substituted)
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Ring");

        let ring_id = ctx.type_store.get_ground_id_by_name("Ring").unwrap();
        let ring_type = Term::ground_type(ring_id);

        // Build: Pi(Ring, Pi(b0, b0))
        let b0 = Term::atom(Atom::BoundVariable(0));
        let identity_type = Term::pi(ring_type.clone(), Term::pi(b0.clone(), b0.clone()));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Apply to the dependent type (with no free variables to substitute)
        let applied = u.apply(Scope::LEFT, &identity_type);

        // Should be unchanged since there are no free variables
        assert_eq!(
            applied, identity_type,
            "Applying to a type with only bound variables should preserve it"
        );
    }

    #[test]
    fn test_unify_dependent_pi_with_free_variable() {
        // Test that a free variable of type Type can unify with a dependent Pi type
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Ring");

        let ring_id = ctx.type_store.get_ground_id_by_name("Ring").unwrap();
        let ring_type = Term::ground_type(ring_id);

        // Build: Pi(Ring, Pi(b0, b0)) - identity function type
        let b0 = Term::atom(Atom::BoundVariable(0));
        let identity_type = Term::pi(ring_type.clone(), Term::pi(b0.clone(), b0.clone()));

        // x0 is a type variable (has type Type)
        let type_sort = Term::type_sort();
        let lctx = LocalContext::from_types(vec![type_sort.clone()]);

        let x0 = Term::atom(Atom::FreeVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![type_sort]);

        // x0 should unify with the dependent Pi type
        assert!(
            u.unify(Scope::LEFT, &x0, Scope::RIGHT, &identity_type),
            "Type variable should unify with dependent Pi type"
        );

        // Check that x0 maps to the identity_type
        let x0_mapping = u.get_mapping(Scope::LEFT, 0);
        assert!(x0_mapping.is_some(), "x0 should have a mapping");
        assert_eq!(
            x0_mapping.unwrap().to_string(),
            identity_type.to_string(),
            "x0 should map to the dependent Pi type"
        );
    }

    #[test]
    fn test_unify_nested_dependent_pi() {
        // Test unifying nested dependent Pi types:
        // Π (R : Ring), Π (S : Ring), R -> S -> R
        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Ring");

        let ring_id = ctx.type_store.get_ground_id_by_name("Ring").unwrap();
        let ring_type = Term::ground_type(ring_id);

        // b0 = S (innermost), b1 = R (outermost)
        let b0 = Term::atom(Atom::BoundVariable(0));
        let b1 = Term::atom(Atom::BoundVariable(1));

        // Build: Pi(Ring, Pi(Ring, Pi(b1, Pi(b0, b1))))
        // This is: Π(R: Ring), Π(S: Ring), R -> S -> R
        let body = Term::pi(b1.clone(), Term::pi(b0.clone(), b1.clone()));
        let inner_pi = Term::pi(ring_type.clone(), body);
        let nested_type = Term::pi(ring_type.clone(), inner_pi.clone());

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Same nested type should unify with itself
        assert!(
            u.unify(
                Scope::LEFT,
                &nested_type,
                Scope::RIGHT,
                &nested_type.clone()
            ),
            "Nested dependent Pi type should unify with itself"
        );
    }

    #[test]
    fn test_type_variable_should_not_unify_with_value_returning_type() {
        // Test that a type variable (x0: TypeSort) should NOT unify with a value-level
        // expression that returns Type.
        //
        // This is the bug in polymorphic backwards rewriting: when a pattern has a type
        // variable like x0: TypeSort, it should only be bound to proper types (like Foo, Nat),
        // not to value-level expressions that happen to return Type.
        //
        // Example of the bug:
        // - Pattern: f(x0, a) where x0: TypeSort
        // - Target: f(getType(c0), a) where getType: Foo -> Type
        // - x0 gets bound to getType(c0), which is WRONG
        // - x0 should only bind to proper type symbols, not function applications

        let mut ctx = KernelContext::new();
        ctx.parse_datatype("Foo");

        let foo_id = ctx.type_store.get_ground_id_by_name("Foo").unwrap();
        let foo_type = Term::ground_type(foo_id);
        let type_sort = Term::type_sort();

        // Create a function getType: Foo -> Type
        // This is a value-level function that returns a type
        let foo_to_type = Term::pi(foo_type.clone(), type_sort.clone());
        ctx.symbol_table.add_global_constant(foo_to_type);

        // Create c0: Foo
        ctx.symbol_table.add_scoped_constant(foo_type.clone());

        // getType(c0) is a value-level expression that returns Type
        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));
        let get_type_c0 = Term::new(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)),
            vec![c0.clone()],
        );

        // x0 is a type variable (x0: TypeSort)
        let lctx = LocalContext::from_types(vec![type_sort.clone()]);
        let x0 = Term::atom(Atom::FreeVariable(0));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(lctx)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));
        u.set_output_var_types(vec![type_sort.clone()]);

        // x0: TypeSort should NOT unify with getType(c0)
        // Even though getType(c0) has type Type (= TypeSort), it's a value-level expression,
        // not a proper type like Foo or Nat.
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &get_type_c0);
        assert!(
            !result,
            "Type variable x0: TypeSort should NOT unify with value-level expression getType(c0)"
        );
    }

    #[test]
    fn test_unify_typeclass_variable_rejects_bool() {
        // Test: x0 with type Monoid should NOT unify with Bool
        // Bool is a built-in type that doesn't implement any typeclasses.
        // This was a bug where Bool (represented as Symbol::Bool, not Symbol::Type(...))
        // was not being checked against typeclass constraints.
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut ctx = KernelContext::new();

        // Register a Monoid typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = ctx.type_store.add_typeclass(&monoid);

        // x0 has typeclass constraint Monoid
        let typeclass_type = Term::typeclass(monoid_id);
        let local_ctx = LocalContext::from_types(vec![typeclass_type.clone()]);

        let x0 = Term::atom(Atom::FreeVariable(0));
        let bool_type = Term::atom(Atom::Symbol(Symbol::Bool));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // x0: Monoid should NOT unify with Bool
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &bool_type);
        assert!(
            !result,
            "x0: Monoid should NOT unify with Bool - Bool doesn't implement any typeclass"
        );
    }

    #[test]
    fn test_type_variable_substitution_in_mapping() {
        // This test verifies that when type unification remaps a type variable,
        // the mapping for term variables is properly updated.
        //
        // Scenario:
        // - x0: TypeSort (a type variable)
        // - x1: List[x0] (a term whose type depends on x0)
        // - c0: List[Bool] (a concrete term)
        // - Unify x1 with c0
        // - This should map x0 -> Bool and x1 -> c0
        // - After apply, we should get c0, not something with unresolved type variables
        //
        // The bug was: after type unification mapped x0 -> Bool, the mapping for x1
        // still contained references to the output type variable instead of Bool.
        let mut ctx = KernelContext::new();
        ctx.parse_type_constructor("List", 1);

        let list_id = ctx.type_store.get_ground_id_by_name("List").unwrap();

        // List[Bool]
        let list_bool = Term::new(Atom::Symbol(Symbol::Type(list_id)), vec![Term::bool_type()]);

        // c0: List[Bool]
        ctx.symbol_table.add_scoped_constant(list_bool.clone());
        let c0 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(0)));

        // x0: TypeSort, x1: List[x0]
        let list_x0 = Term::new(
            Atom::Symbol(Symbol::Type(list_id)),
            vec![Term::atom(Atom::FreeVariable(0))],
        );
        let local_ctx = LocalContext::from_types(vec![Term::type_sort(), list_x0]);

        let x1 = Term::atom(Atom::FreeVariable(1));

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Unify x1: List[x0] with c0: List[Bool]
        assert!(u.unify(Scope::LEFT, &x1, Scope::RIGHT, &c0));

        // After unification, applying to x1 should give c0
        let result = u.apply(Scope::LEFT, &x1);
        assert_eq!(
            result, c0,
            "After unifying x1: List[x0] with c0: List[Bool], apply(x1) should give c0"
        );

        // The result should have type List[Bool], not List[x0]
        let result_type = result.get_type_with_context(&u.output_context, &ctx);
        assert_eq!(
            result_type, list_bool,
            "Result type should be List[Bool], not contain unresolved type variables"
        );
    }

    #[test]
    fn test_remap_avoids_self_referential_types() {
        // This test verifies that remap() correctly handles the case where
        // remapping would create a self-referential type.
        //
        // Scenario:
        // - output x0 has type x1 (its type IS whatever type x1 represents)
        // - output x1 has type TypeSort (x1 is a type variable)
        // - We remap x1 -> x0
        // - Without the fix: x0's type becomes x0 (self-referential!)
        // - With the fix: x0's type becomes TypeSort (x1's type propagated)
        //
        // This bug caused "Cycle in type dependencies" panics in polymorphic mode.
        let ctx = KernelContext::new();

        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(LocalContext::empty())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Manually set up output context to simulate the problematic state:
        // x0: x1 (x0's type is "the type that x1 represents")
        // x1: TypeSort (x1 is a type variable)
        u.output_context
            .set_type(0, Term::atom(Atom::FreeVariable(1)));
        u.output_context.set_type(1, Term::type_sort());

        // Also set up the OUTPUT map so x1 has no mapping yet
        u.maps[Scope::OUTPUT.get()].push_none(); // x0
        u.maps[Scope::OUTPUT.get()].push_none(); // x1

        // Now simulate what happens when we unify output x1 with output x0
        // This calls remap(1, x0)
        let x0 = Term::atom(Atom::FreeVariable(0));
        let result = u.unify_variable(Scope::OUTPUT, 1, Scope::OUTPUT, &x0);
        assert!(result, "Unification should succeed");

        // After remap, x0's type should be TypeSort, not x0
        let x0_type = u.output_context.get_var_type(0).unwrap();
        assert_eq!(
            *x0_type,
            Term::type_sort(),
            "x0's type should be TypeSort after remap, not self-referential"
        );
        assert!(
            !x0_type.has_variable(0),
            "x0's type should not contain x0 (would be self-referential)"
        );
    }

    #[test]
    fn test_output_variable_type_check_before_remap() {
        // Test that OUTPUT variables are type-checked before being remapped.
        // This bug was causing resolution to produce ill-typed clauses.
        //
        // Scenario: OUTPUT variable x0 has type (Bool -> Bool), but we try to
        // remap it to a term of type Bool. This should FAIL because the types
        // are incompatible.
        let ctx = test_ctx();
        let bool_to_bool = ctx
            .symbol_table
            .get_type(Symbol::GlobalConstant(ModuleId(0), 1))
            .clone(); // g1: Bool -> Bool

        let mut u = Unifier::new(3, &ctx);
        // Set up LEFT context: x0: Bool -> Bool
        let left_ctx = LocalContext::from_types(vec![bool_to_bool.clone()]);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(left_ctx)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(LocalContext::empty())));

        // Set up OUTPUT context: x0: Bool -> Bool
        u.set_output_var_types(vec![bool_to_bool.clone()]);

        // First, map x0 from LEFT to OUTPUT (so x0 in OUTPUT has a function type)
        let x0 = Term::atom(Atom::FreeVariable(0));
        let result = u.unify_variable(Scope::LEFT, 0, Scope::OUTPUT, &x0);
        assert!(result, "Initial mapping should succeed");

        // c5 is a Bool constant (not a function)
        let c5 = Term::atom(Atom::Symbol(Symbol::ScopedConstant(5)));

        // Now try to unify OUTPUT x0 with c5 (Bool).
        // This should FAIL because x0: (Bool -> Bool) is incompatible with c5: Bool
        let result = u.unify_variable(Scope::OUTPUT, 0, Scope::OUTPUT, &c5);
        assert!(
            !result,
            "OUTPUT x0: (Bool -> Bool) should NOT unify with c5: Bool - types are incompatible"
        );
    }

    /// Test that Pi types (function kinds like Type -> Type) are rejected
    /// when unifying with a variable that has a typeclass constraint.
    /// This prevents higher-kinded type constructors from being used where
    /// a type implementing a typeclass is expected.
    #[test]
    fn test_typeclass_rejects_pi_types() {
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("MyClass");

        // x0 has type MyClass (typeclass constraint)
        let local = kctx.parse_local(&["MyClass"]);
        let empty_local = LocalContext::empty();

        // Type -> Type is a Pi type (kind of type constructors like List)
        let type_to_type = Term::pi(Term::type_sort(), Term::type_sort());

        let mut u = Unifier::new(3, &kctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local)));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(empty_local)));

        // Try to unify x0 (typeclass constraint) with Type -> Type (Pi type)
        // This should FAIL because Pi types are not types that can implement typeclasses
        let x0 = Term::atom(Atom::FreeVariable(0));
        let result = u.unify(Scope::LEFT, &x0, Scope::RIGHT, &type_to_type);
        assert!(
            !result,
            "Variable with typeclass constraint should NOT unify with Pi type (Type -> Type)"
        );
    }

    #[test]
    fn test_unify_with_prior_mapping_and_bound_variable() {
        // Regression test for panic during type unification when Pi types are involved.
        //
        // When unifying Pi types like `(x: T) -> x` and `(y: U) -> U`, we recursively
        // unify the outputs. The first has BoundVariable(0), the second has a FreeVariable.
        // If the FreeVariable already has a mapping to an OUTPUT variable, we end up calling
        // unify_variable(OUTPUT, var_id, OUTPUT, BoundVariable), which tries to get the
        // type of the BoundVariable and panics.
        //
        // This is a legitimate code path that should fail gracefully, not panic.
        let ctx = test_ctx();

        // Set up: x0 and x1 in LEFT both have type Type (they're type variables)
        let local_ctx = LocalContext::from_types(vec![Term::type_sort(), Term::type_sort()]);
        let mut u = Unifier::new(3, &ctx);
        u.set_input_context(Scope::LEFT, Box::leak(Box::new(local_ctx.clone())));
        u.set_input_context(Scope::RIGHT, Box::leak(Box::new(local_ctx)));
        u.set_output_var_types(vec![Term::type_sort(), Term::type_sort()]);

        // First, create a mapping: unify x0 (LEFT) with x1 (LEFT)
        // This creates output variable x0 and maps both input variables to it.
        // This simulates what happens during type unification when two type variables
        // are unified.
        let x0 = Term::atom(Atom::FreeVariable(0));
        let x1 = Term::atom(Atom::FreeVariable(1));
        assert!(u.unify(Scope::LEFT, &x0, Scope::LEFT, &x1));

        // Now simulate what happens when unifying outputs of Pi types:
        // - One Pi type has output BoundVariable(0) (refers to its input parameter)
        // - The other has output x0 which is already mapped to an OUTPUT variable
        //
        // The unification path:
        // 1. We try to unify x0 with BoundVariable(0)
        // 2. x0 has a prior mapping to output variable
        // 3. unify_internal(OUTPUT, output_var, OUTPUT, BoundVariable) is called
        // 4. This calls unify_variable(OUTPUT, var_id, OUTPUT, BoundVariable)
        // 5. BUG: tries to get_type_with_context on BoundVariable, which panics
        let bound_var = Term::atom(Atom::BoundVariable(0));
        let result = u.unify(Scope::LEFT, &x0, Scope::LEFT, &bound_var);

        // Should fail gracefully (BoundVariables can't unify with FreeVariables),
        // not panic.
        assert!(
            !result,
            "Unifying mapped variable with BoundVariable should fail, not panic"
        );
    }
}
