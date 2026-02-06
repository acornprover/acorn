use serde::{Deserialize, Serialize};
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::types::{GroundTypeId, TypeclassId};
use crate::module::ModuleId;

/// A step in a path through a term.
/// Treats applications in curried form: f(a, b) becomes ((f a) b).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PathStep {
    /// Go to the function part of an application
    Function,
    /// Go to the argument part of an application
    Argument,
}

/// A component of a Term in its flattened representation.
/// This is private to the term module - external code should use decomposition methods.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
enum TermComponent {
    /// Indicates a function application.
    /// - Left child (function): always at index + 1
    /// - Right child (argument): at index + right_offset
    /// The right_offset is the offset from this marker to the start of the right child.
    /// For f(a): [Application{2}, f, a] - right_offset=2 means arg is at position 2 from marker.
    Application { right_offset: u16 },

    /// A Pi type (dependent function type).
    /// - Left child (input type): always at index + 1
    /// - Right child (output type): at index + right_offset
    /// Pi always has exactly 2 sub-elements: input type and output type.
    /// Used when Term represents types like `(T : Type<CommRing>) -> T -> T -> T`.
    /// A non-dependent arrow `A -> B` is represented as `Pi(A, B)` where B doesn't use Var(0).
    Pi { right_offset: u16 },

    /// A leaf atom in the term tree.
    Atom(Atom),
}

/// Decomposition of a term into its lambda-calculus structure.
/// This provides a cleaner way to pattern match on terms without dealing with
/// "head + N arguments" representations.
#[derive(Clone, Copy, Debug)]
pub enum Decomposition<'a> {
    /// An atomic term with no arguments.
    Atom(&'a Atom),

    /// A curried application: (func arg).
    /// For f(a, b, c), decomposes into (f(a, b), c).
    /// Both func and arg are borrowed slices from the original term - no allocation.
    Application(TermRef<'a>, TermRef<'a>),

    /// A Pi type (dependent function type): (x : input) -> output.
    /// For non-dependent arrow types, output doesn't reference the bound variable.
    /// Both input and output are borrowed slices - no allocation.
    Pi(TermRef<'a>, TermRef<'a>),
}

/// A borrowed reference to a term - wraps a slice of components.
/// This is the borrowed equivalent of Term, similar to how &str relates to String.
/// Most operations work on TermRef to avoid unnecessary allocations.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct TermRef<'a> {
    components: &'a [TermComponent],
}

impl<'a> TermRef<'a> {
    /// Create a TermRef from a slice of components.
    fn new(components: &'a [TermComponent]) -> TermRef<'a> {
        TermRef { components }
    }

    /// Convert this borrowed TermRef to an owned Term.
    pub fn to_owned(&self) -> Term {
        if self.components.is_empty() {
            panic!("Cannot convert empty TermRef to Term");
        }

        // Verify format is correct
        if self.components.len() > 1 {
            match self.components[0] {
                TermComponent::Application { right_offset }
                | TermComponent::Pi { right_offset } => {
                    debug_assert!(
                        right_offset >= 2 && (right_offset as usize) < self.components.len(),
                        "to_owned: invalid right_offset {} for len {}",
                        right_offset,
                        self.components.len()
                    );
                }
                _ => panic!(
                    "to_owned: non-atomic term should start with Application or Pi, got: {:?}",
                    self.components
                ),
            }
        }

        Term {
            components: self.components.to_vec(),
        }
    }

    /// Get the head atom of this term.
    /// The head is always the first component (or first after Application marker).
    pub fn get_head_atom(&self) -> &Atom {
        // Find the head atom by skipping through nested Application markers
        let mut pos = 0;
        loop {
            match &self.components[pos] {
                TermComponent::Atom(atom) => return atom,
                TermComponent::Application { .. } => {
                    // Skip to the func part (position after the Application marker)
                    pos += 1;
                }
                TermComponent::Pi { .. } => {
                    // For Pi types, the head atom is the input type's head atom
                    pos += 1;
                }
            }
        }
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.components.len() == 1
    }

    /// Decompose this term into its fundamental lambda-calculus structure.
    ///
    /// Returns either:
    /// - `Decomposition::Atom(&atom)` if the term is atomic
    /// - `Decomposition::Application(func, arg)` if the term is an application
    /// - `Decomposition::Pi(input, output)` if the term is a Pi type
    ///
    /// All returned references are borrowed slices - no allocation needed.
    /// This provides a cleaner way to write recursive algorithms on terms
    /// by pattern matching on the structure rather than checking multiple conditions.
    pub fn decompose(&self) -> Decomposition<'a> {
        // Handle atomic terms (single Atom, no Application/Pi wrapper)
        if self.components.len() == 1 {
            let atom = match &self.components[0] {
                TermComponent::Atom(atom) => atom,
                _ => panic!("atomic term should have Atom component"),
            };
            return Decomposition::Atom(atom);
        }

        // Non-atomic terms start with Application or Pi
        match self.components[0] {
            TermComponent::Application { right_offset } => {
                // Left child (func) starts at position 1, ends at right_offset
                let func = TermRef::new(&self.components[1..right_offset as usize]);

                // Right child (arg) starts at right_offset, extends to end of slice
                let arg = TermRef::new(&self.components[right_offset as usize..]);

                Decomposition::Application(func, arg)
            }
            TermComponent::Pi { right_offset } => {
                // Left child (input type) starts at position 1, ends at right_offset
                let input = TermRef::new(&self.components[1..right_offset as usize]);

                // Right child (output type) starts at right_offset, extends to end of slice
                let output = TermRef::new(&self.components[right_offset as usize..]);

                Decomposition::Pi(input, output)
            }
            TermComponent::Atom(_) => panic!(
                "non-atomic term should start with Application or Pi, got: {:?}",
                self.components
            ),
        }
    }

    /// Split an application into (function, argument) in curried form.
    /// For f(a, b, c), returns (f(a, b), c).
    /// Returns None if the term is atomic or a Pi type.
    ///
    /// Both returned TermRefs are slices of the original - no allocation needed.
    pub fn split_application(&self) -> Option<(TermRef<'a>, TermRef<'a>)> {
        match self.decompose() {
            Decomposition::Application(func, arg) => Some((func, arg)),
            _ => None,
        }
    }

    /// Check if this term is a Pi type (dependent function type).
    pub fn is_pi(&self) -> bool {
        matches!(self.components.first(), Some(TermComponent::Pi { .. }))
    }

    /// Split a Pi type into (input_type, output_type).
    /// Returns None if the term is not a Pi type.
    ///
    /// Both returned TermRefs are slices of the original - no allocation needed.
    pub fn split_pi(&self) -> Option<(TermRef<'a>, TermRef<'a>)> {
        match self.decompose() {
            Decomposition::Pi(input, output) => Some((input, output)),
            _ => None,
        }
    }

    /// Check if this term starts with an Application marker.
    /// This is different from has_args() which checks for any application structure.
    /// is_application() specifically checks for the top-level Application{right_offset} marker.
    pub fn is_application(&self) -> bool {
        matches!(
            self.components.first(),
            Some(TermComponent::Application { .. })
        )
    }

    /// Split a curried application into (head, args).
    /// Returns None if the term is not an application.
    /// For `((f a) b)`, returns (f, [a, b]).
    pub fn split_application_multi(&self) -> Option<(Term, Vec<Term>)> {
        if !self.is_application() {
            return None;
        }

        // Collect args by recursively splitting curried applications
        let mut args = Vec::new();
        let mut current = *self;

        while let Some((func, arg)) = current.split_application() {
            args.push(arg.to_owned());
            current = func;
        }

        // Reverse args since we collected from right to left
        args.reverse();

        Some((current.to_owned(), args))
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        matches!(self.get_head_atom(), Atom::Symbol(Symbol::True))
    }

    /// Check if this term is a variable (atomic and head is a variable).
    pub fn is_variable(&self) -> bool {
        self.is_atomic() && self.get_head_atom().is_variable()
    }

    /// If this is an atomic variable, return its index.
    pub fn atomic_variable(&self) -> Option<AtomId> {
        if !self.is_atomic() {
            return None;
        }
        match self.get_head_atom() {
            Atom::FreeVariable(i) => Some(*i),
            _ => None,
        }
    }

    /// If this is an atomic Type symbol, return its GroundTypeId.
    /// This is used for ground types when Term represents a type.
    pub fn as_type_atom(&self) -> Option<GroundTypeId> {
        if !self.is_atomic() {
            return None;
        }
        match self.get_head_atom() {
            Atom::Symbol(Symbol::Type(t)) => Some(*t),
            _ => None,
        }
    }

    /// If this is an atomic Typeclass, return its TypeclassId.
    /// This is used when a type variable is constrained to a typeclass.
    pub fn as_typeclass(&self) -> Option<TypeclassId> {
        if !self.is_atomic() {
            return None;
        }
        match self.get_head_atom() {
            Atom::Symbol(Symbol::Typeclass(tc)) => Some(*tc),
            _ => None,
        }
    }

    /// Returns true if this is a Typeclass kind.
    pub fn is_typeclass(&self) -> bool {
        self.as_typeclass().is_some()
    }

    /// Returns true if this represents a type parameter kind (either Type0 or a Typeclass).
    /// Type parameters with these kinds are not value arguments.
    pub fn is_type_param_kind(&self) -> bool {
        self.is_type0() || self.is_typeclass()
    }

    /// Counts the number of leading Pi types where the input is a type parameter kind.
    /// This is used to detect polymorphic functions/synthetics.
    /// For example: Pi(TypeSort, Pi(Typeclass, X)) has 2 type parameters.
    pub fn count_type_params(&self) -> usize {
        match self.split_pi() {
            Some((input, output)) => {
                if input.is_type_param_kind() {
                    1 + output.count_type_params()
                } else {
                    0
                }
            }
            None => 0,
        }
    }

    /// Returns true if this is the Bool type.
    pub fn is_bool_type(&self) -> bool {
        self.is_atomic() && matches!(self.get_head_atom(), Atom::Symbol(Symbol::Bool))
    }

    /// Returns true if this is the Empty type.
    pub fn is_empty_type(&self) -> bool {
        self.is_atomic() && matches!(self.get_head_atom(), Atom::Symbol(Symbol::Empty))
    }

    /// Returns true if this is Type0 (the type of types, aka kind *).
    pub fn is_type0(&self) -> bool {
        self.is_atomic() && matches!(self.get_head_atom(), Atom::Symbol(Symbol::Type0))
    }

    /// Get the term's type as a Term with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, recursively gets the function's type and applies it.
    pub fn get_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        let result = match self.decompose() {
            Decomposition::Atom(atom) => match atom {
                Atom::FreeVariable(i) => local_context
                    .get_var_type(*i as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "Variable x{} not found in LocalContext (size={}). TermRef components: {:?}",
                            i,
                            local_context.len(),
                            self.components
                        )
                    }),
                Atom::BoundVariable(_) => {
                    // BoundVariables get their type from the enclosing Pi binder.
                    // This case should not be reached during normal type computation.
                    panic!("BoundVariable should not appear as standalone term in get_type_with_context")
                }
                Atom::Symbol(symbol) => kernel_context
                    .symbol_table
                    .get_symbol_type(*symbol, &kernel_context.type_store),
            },
            Decomposition::Application(func, arg) => {
                // The function has type A -> B, so the application has type B
                let func_type = func.get_type_with_context(local_context, kernel_context);
                // For dependent types, we need to substitute the argument into the output type
                let arg_term = arg.to_owned();
                let result = func_type.type_apply_with_arg(&arg_term).unwrap_or_else(|| {
                    panic!(
                        "Function type expected but not found during type application.\n\
                         func = {}\n\
                         func_type = {}\n\
                         arg = {}\n\
                         self = {}",
                        func, func_type, arg, self
                    )
                });
                result
            }
            Decomposition::Pi(_, _) => {
                // Pi types are themselves types - this is used when the term IS a type
                // Return the Type kind
                Term::type_sort()
            }
        };
        result.validate();
        result
    }

    /// Check if this term contains a variable with the given index anywhere.
    pub fn has_variable(&self, index: AtomId) -> bool {
        for component in self.components {
            if let TermComponent::Atom(Atom::FreeVariable(i)) = component {
                if *i == index {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any variables.
    pub fn has_any_variable(&self) -> bool {
        for component in self.components {
            if let TermComponent::Atom(atom) = component {
                if atom.is_variable() {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        for component in self.components {
            if let TermComponent::Atom(atom) = component {
                if atom.is_scoped_constant() {
                    return true;
                }
            }
        }
        false
    }

    /// Check if this term contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        for component in self.components {
            if let TermComponent::Atom(Atom::Symbol(Symbol::Synthetic(..))) = component {
                return true;
            }
        }
        false
    }

    /// Count the number of atom components (excluding Application markers).
    pub fn atom_count(&self) -> u32 {
        let mut count = 0;
        for component in self.components {
            // True and False count as 0
            if matches!(
                component,
                TermComponent::Atom(Atom::Symbol(Symbol::True))
                    | TermComponent::Atom(Atom::Symbol(Symbol::False))
            ) {
                continue;
            }
            if matches!(component, TermComponent::Atom(_)) {
                count += 1;
            }
        }
        count
    }

    /// Returns true if this term has any arguments.
    /// This is O(1) unlike num_args() which must iterate.
    pub fn has_args(&self) -> bool {
        // A term has args if it starts with Application (non-atomic terms always start with Application)
        matches!(self.components[0], TermComponent::Application { .. })
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        let mut count = 0;
        let mut current = *self;
        while !current.is_atomic() {
            count += 1;
            match current.split_application() {
                Some((func, _arg)) => current = func,
                None => break,
            }
        }
        count
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a TermRef.
    /// For f(a, b), this yields [a, b] in order.
    pub fn iter_args(&self) -> TermRefArgsIterator<'a> {
        // For nested format [Application{5}, Application{3}, f, a, b]:
        // Collect args by walking the nested applications via split_application.
        // This collects innermost first, so we reverse at the end.

        if self.is_atomic() {
            return TermRefArgsIterator {
                components: self.components,
                arg_positions: Vec::new(),
                current_index: 0,
            };
        }

        let mut arg_positions = Vec::new();
        let mut current = *self;

        while !current.is_atomic() {
            match current.split_application() {
                Some((func, arg)) => {
                    // Record arg bounds relative to original term
                    let arg_offset =
                        arg.components.as_ptr() as usize - self.components.as_ptr() as usize;
                    let arg_start = arg_offset / std::mem::size_of::<TermComponent>();
                    arg_positions.push((arg_start, arg_start + arg.components.len()));
                    current = func;
                }
                None => break,
            }
        }

        // Reverse since we collected innermost first
        arg_positions.reverse();

        TermRefArgsIterator {
            components: self.components,
            arg_positions,
            current_index: 0,
        }
    }

    /// Iterate over all atoms in the term.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + 'a {
        self.components.iter().filter_map(|component| {
            if let TermComponent::Atom(atom) = component {
                Some(atom)
            } else {
                None
            }
        })
    }

    /// Get the maximum variable index in this term, or None if there are no variables.
    pub fn max_variable(&self) -> Option<AtomId> {
        let mut max: Option<AtomId> = None;
        for atom in self.iter_atoms() {
            if let Atom::FreeVariable(i) = atom {
                max = Some(match max {
                    None => *i,
                    Some(current_max) => current_max.max(*i),
                });
            }
        }
        max
    }

    /// Get the lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        match self.max_variable() {
            Some(max) => max + 1,
            None => 0,
        }
    }

    /// Calculate multi-weight for KBO ordering.
    /// Returns (weight1, weight2) and populates refcounts with variable usage.
    fn multi_weight(&self, refcounts: &mut Vec<u8>) -> (u32, u32) {
        let mut weight1: u32 = 0;
        let mut weight2: u32 = 0;

        for component in self.components {
            match component {
                TermComponent::Application { .. } => {
                    // Application markers don't contribute to weight
                }
                TermComponent::Pi { .. } => {
                    // Pi types contribute to weight like Application
                    weight1 += 1;
                }
                TermComponent::Atom(Atom::Symbol(Symbol::True))
                | TermComponent::Atom(Atom::Symbol(Symbol::False)) => {
                    // True/False don't contribute to weight
                }
                TermComponent::Atom(Atom::Symbol(Symbol::Empty))
                | TermComponent::Atom(Atom::Symbol(Symbol::Bool))
                | TermComponent::Atom(Atom::Symbol(Symbol::Type0)) => {
                    // Built-in type symbols contribute to weight
                    weight1 += 1;
                }
                TermComponent::Atom(Atom::FreeVariable(i)) => {
                    while refcounts.len() <= *i as usize {
                        refcounts.push(0);
                    }
                    refcounts[*i as usize] += 1;
                }
                TermComponent::Atom(Atom::BoundVariable(_)) => {
                    // Bound variables contribute weight but don't use refcounts
                    weight1 += 1;
                }
                TermComponent::Atom(Atom::Symbol(Symbol::GlobalConstant(m, i))) => {
                    weight1 += 1;
                    let symbol_weight =
                        (m.get() as u32).wrapping_mul(65536).wrapping_add(*i as u32);
                    weight2 = weight2.wrapping_add(4u32.wrapping_mul(symbol_weight));
                }
                TermComponent::Atom(Atom::Symbol(Symbol::ScopedConstant(i))) => {
                    weight1 += 1;
                    weight2 = weight2.wrapping_add(1u32.wrapping_add(4u32.wrapping_mul(*i as u32)));
                }
                TermComponent::Atom(Atom::Symbol(Symbol::Synthetic(m, i))) => {
                    weight1 += 1;
                    // Use wrapping arithmetic to avoid overflow for INVALID_SYNTHETIC_MODULE
                    weight2 = weight2.wrapping_add(3u32.wrapping_add(4u32.wrapping_mul(
                        (m.get() as u32).wrapping_mul(65536).wrapping_add(*i as u32),
                    )));
                }
                TermComponent::Atom(Atom::Symbol(Symbol::Type(t))) => {
                    // Type atoms contribute to weight
                    weight1 += 1;
                    let symbol_weight = (t.module_id().get() as u32)
                        .wrapping_mul(65536)
                        .wrapping_add(t.local_id() as u32);
                    weight2 = weight2.wrapping_add(4u32.wrapping_mul(symbol_weight));
                }
                TermComponent::Atom(Atom::Symbol(Symbol::Typeclass(tc))) => {
                    // Typeclass atoms contribute to weight similarly to types
                    weight1 += 1;
                    let symbol_weight = (tc.module_id().get() as u32)
                        .wrapping_mul(65536)
                        .wrapping_add(tc.local_id() as u32);
                    weight2 = weight2.wrapping_add(4u32.wrapping_mul(symbol_weight));
                }
            }
        }

        (weight1, weight2)
    }

    /// KBO helper that can skip the domination check.
    fn kbo_helper(&self, other: &TermRef, check_domination: bool) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let mut self_refcounts = vec![];
        let (self_weight1, self_weight2) = self.multi_weight(&mut self_refcounts);

        let mut other_refcounts = vec![];
        let (other_weight1, other_weight2) = other.multi_weight(&mut other_refcounts);

        if self_weight1 > other_weight1
            || self_weight1 == other_weight1 && self_weight2 > other_weight2
        {
            if !check_domination || dominates(&self_refcounts, &other_refcounts) {
                return Ordering::Greater;
            }
            return Ordering::Equal;
        }

        if self_weight1 < other_weight1
            || self_weight1 == other_weight1 && self_weight2 < other_weight2
        {
            if !check_domination || dominates(&other_refcounts, &self_refcounts) {
                return Ordering::Less;
            }
            return Ordering::Equal;
        }

        Ordering::Equal
    }

    /// Partial tiebreak for KBO - stable under variable renaming.
    fn partial_tiebreak(&self, other: &TermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let head_cmp = self
            .get_head_atom()
            .stable_partial_order(other.get_head_atom());
        if head_cmp != Ordering::Equal {
            return head_cmp;
        }

        // More arguments means simpler (less nested)
        let len_cmp = other.num_args().cmp(&self.num_args());
        if len_cmp != Ordering::Equal {
            return len_cmp;
        }

        // Compare arguments lexicographically
        for (arg1, arg2) in self.iter_args().zip(other.iter_args()) {
            let arg_cmp = arg1.partial_tiebreak(&arg2);
            if arg_cmp != Ordering::Equal {
                return arg_cmp;
            }
        }

        Ordering::Equal
    }

    /// Total tiebreak for KBO - not stable under variable renaming.
    fn total_tiebreak(&self, other: &TermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let head_cmp = other.get_head_atom().cmp(self.get_head_atom());
        if head_cmp != Ordering::Equal {
            return head_cmp;
        }

        // The partial tiebreak should have caught this
        debug_assert!(self.num_args() == other.num_args());

        // Compare arguments lexicographically
        for (arg1, arg2) in self.iter_args().zip(other.iter_args()) {
            let arg_cmp = arg1.extended_kbo_cmp(&arg2);
            if arg_cmp != Ordering::Equal {
                return arg_cmp;
            }
        }

        Ordering::Equal
    }

    /// Knuth-Bendix partial reduction ordering.
    /// Returns Greater if self > other, Less if other > self.
    /// Returns Equal if they cannot be ordered (not equality in the usual sense).
    pub fn kbo_cmp(&self, other: &TermRef) -> std::cmp::Ordering {
        self.kbo_helper(other, true)
    }

    /// Extended KBO comparison - total ordering where only identical terms are equal.
    pub fn extended_kbo_cmp(&self, other: &TermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let kbo_cmp = self.kbo_helper(other, false);
        if kbo_cmp != Ordering::Equal {
            return kbo_cmp;
        }

        let tiebreak = self.partial_tiebreak(other);
        if tiebreak != Ordering::Equal {
            return tiebreak;
        }

        self.total_tiebreak(other)
    }

    /// Comparison that is stable under variable renaming (alpha-equivalence).
    /// Two terms that differ only in variable naming will compare as Equal.
    /// Uses KBO with partial_tiebreak internally, but stops before total_tiebreak
    /// which would distinguish between specific variable IDs.
    pub fn stable_cmp(&self, other: &TermRef) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let kbo_cmp = self.kbo_helper(other, false);
        if kbo_cmp != Ordering::Equal {
            return kbo_cmp;
        }

        self.partial_tiebreak(other)
    }

    /// Navigate to a subterm using a path.
    /// Returns None if the path doesn't exist or we hit an atomic term.
    pub fn get_term_at_path(&self, path: &[PathStep]) -> Option<TermRef<'a>> {
        if path.is_empty() {
            return Some(*self);
        }

        // Try to split the application
        let (func, arg) = self.split_application()?;

        match path[0] {
            PathStep::Argument => arg.get_term_at_path(&path[1..]),
            PathStep::Function => func.get_term_at_path(&path[1..]),
        }
    }
}

impl fmt::Display for TermRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Format the term by walking through components
        format_term_at(f, self.components, 0)
    }
}

/// Helper function to format a term starting at the given position.
/// Returns the position after the formatted term.
fn format_term_at(f: &mut fmt::Formatter, components: &[TermComponent], pos: usize) -> fmt::Result {
    if pos >= components.len() {
        return Ok(());
    }

    match &components[pos] {
        TermComponent::Application { .. } => {
            // Non-atomic term: format the contents (skip the Application marker)
            let end = find_subterm_end_at(components, pos);
            format_application_contents(f, components, pos + 1, end)
        }
        TermComponent::Atom(atom) => {
            // Atomic term - just format the atom
            match atom {
                Atom::FreeVariable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            Ok(())
        }
        TermComponent::Pi { .. } => {
            // Pi type: format as (input -> output)
            let end = find_subterm_end_at(components, pos);
            format_pi_contents(f, components, pos + 1, end)
        }
    }
}

/// Format the contents of an application (func + arg) from start to end.
/// Terms use nested Application markers:
///   - f(a, b): [App{right_offset:3}, App{right_offset:2}, f, a, b] - func is another App, arg is last
///   - f(g(x)): [App{right_offset:2}, f, App{right_offset:2}, g, x] - func is atomic, arg is compound
/// We collect all args by walking the curried structure.
fn format_application_contents(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // Collect all arguments by walking down the curried structure
    let mut args: Vec<(usize, usize)> = Vec::new(); // (start, end) of each arg
    let mut current_start = start;
    let mut current_end = end;

    // Walk down through the structure to find the head and collect args
    loop {
        match &components[current_start] {
            TermComponent::Atom(atom) => {
                // Found the head atom - write it
                match atom {
                    Atom::FreeVariable(i) => write!(f, "x{}", i)?,
                    _ => write!(f, "{}", atom)?,
                }
                // If there's anything after this atom (within our bounds), it's an argument
                let arg_start = current_start + 1;
                if arg_start < current_end {
                    // Collect the remaining content as an argument
                    // For atomic head with compound arg: [head, App{n}, ...]
                    // We need to find where the arg ends
                    let arg_end = find_subterm_end_at(components, arg_start);
                    args.push((arg_start, arg_end));
                }
                break;
            }
            TermComponent::Application { right_offset } => {
                // This is a nested application within our current bounds.
                // The nested App represents the "func" part of our current level.
                // We need to find where the nested App term ends (= where our arg starts).
                //
                // Example: format_application_contents for [App{ro:4}, App{ro:2}, f, a, b]
                // Called with start=1, end=5
                //   at position 1: App{ro:2} (the inner App representing f(a))
                //   - The inner App term ends at position 4 (after 'a')
                //   - The outer arg 'b' is at positions [4, 5)

                // Find where this nested App term ends
                let nested_app_end = find_subterm_end_at(components, current_start);

                // The outer arg (at our current level) is from nested_app_end to current_end
                let arg_start = nested_app_end;
                let arg_end = current_end;

                if arg_start < arg_end {
                    // Add this arg to our list (collecting from outermost to innermost)
                    args.push((arg_start, arg_end));
                }

                // Now process the contents of this nested App
                // right_offset tells us where the inner right child starts
                let inner_func_start = current_start + 1;
                let inner_arg_start = current_start + *right_offset as usize;

                // Check if there's an inner arg (within this nested App)
                if inner_arg_start < nested_app_end {
                    // There's an arg inside this nested application
                    args.push((inner_arg_start, nested_app_end));
                }

                // Continue with the inner func
                current_start = inner_func_start;
                current_end = inner_arg_start;
            }
            TermComponent::Pi { .. } => {
                return Err(fmt::Error);
            }
        }
    }

    // Now write all the arguments in order
    if !args.is_empty() {
        write!(f, "(")?;
        // args are in reverse order (outermost first collected), so reverse them
        for (i, (arg_start, arg_end)) in args.iter().rev().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            format_term_slice(f, components, *arg_start, *arg_end)?;
        }
        write!(f, ")")?;
    }

    Ok(())
}

/// Format the contents of a Pi type (input -> output) from start to end.
fn format_pi_contents(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    // Find where the input type ends
    let input_end = find_subterm_end_at(components, start);
    let output_start = input_end;

    write!(f, "(")?;
    format_term_slice(f, components, start, input_end)?;
    write!(f, " -> ")?;
    format_term_slice(f, components, output_start, end)?;
    write!(f, ")")
}

/// Find the end position of a subterm starting at `start` in a components slice.
fn find_subterm_end_at(components: &[TermComponent], start: usize) -> usize {
    match components[start] {
        TermComponent::Pi { right_offset } | TermComponent::Application { right_offset } => {
            // Right child starts at start + right_offset, recursively find its end
            find_subterm_end_at(components, start + right_offset as usize)
        }
        TermComponent::Atom(_) => start + 1,
    }
}

/// Format a slice of components as a term.
fn format_term_slice(
    f: &mut fmt::Formatter,
    components: &[TermComponent],
    start: usize,
    end: usize,
) -> fmt::Result {
    if start >= end {
        return Ok(());
    }

    match &components[start] {
        TermComponent::Application { .. } => {
            format_application_contents(f, components, start + 1, end)
        }
        TermComponent::Atom(atom) => {
            match atom {
                Atom::FreeVariable(i) => write!(f, "x{}", i)?,
                _ => write!(f, "{}", atom)?,
            }
            Ok(())
        }
        TermComponent::Pi { .. } => format_pi_contents(f, components, start + 1, end),
    }
}

/// A Term stores term structure without embedding type information.
/// Type information is stored separately in the TypeStore and SymbolTable.
/// The term is represented as a flat vector of components in pre-order traversal.
/// The first element is always the head atom, followed by the arguments.
///
/// Examples:
/// - Simple atom "a": [Atom(a)]
/// - Application "f(a)": [Atom(f), Atom(a)]
/// - Nested "f(a, g(b))": [Atom(f), Atom(a), Application{right_offset: 2}, Atom(g), Atom(b)]
///                                            ^--- right_offset=2 means the arg (b) is 2 positions after this marker
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize, Deserialize)]
pub struct Term {
    components: Vec<TermComponent>,
}

impl Term {
    /// Create a new Term with the given head atom and arguments.
    /// If args is empty, returns an atomic term [Atom(head)].
    /// If args is non-empty, builds nested Application structure for curried form:
    ///   f(a, b) becomes [App{5}, App{3}, f, a, b]
    /// where the inner App{3} represents f(a), and the outer applies that to b.
    pub fn new(head: Atom, args: Vec<Term>) -> Term {
        if args.is_empty() {
            return Term {
                components: vec![TermComponent::Atom(head)],
            };
        }

        // Build nested applications from left to right (curried form)
        // f(a, b, c) = ((f a) b) c
        // Start with the head atom
        let mut func_components: Vec<TermComponent> = vec![TermComponent::Atom(head)];

        for (i, arg) in args.iter().enumerate() {
            if arg.components.is_empty() {
                panic!("Term::new: arg {} is empty", i);
            }

            // Calculate sizes
            let func_len = func_components.len();
            let arg_len = arg.components.len();

            // Build new application: [Application{right_offset}, func_components..., arg_components...]
            // But we need to handle the func_components - if it's just an atom, no wrapper needed inside
            // If it already has components > 1, we need to wrap it in Application
            let mut new_components = Vec::with_capacity(1 + func_len + arg_len + 1);

            // right_offset = 1 + func_len (marker + left child = position of right child)
            let right_offset = (1 + func_len) as u16;

            // Outer Application for the whole thing
            new_components.push(TermComponent::Application { right_offset });

            // Add the func part (left child)
            if func_len == 1 {
                // Atomic func - just add it directly
                new_components.extend(func_components.iter().copied());
            } else {
                // Non-atomic func - must be a compound term (Application or Pi)
                match func_components[0] {
                    TermComponent::Application { .. } | TermComponent::Pi { .. } => {
                        new_components.extend(func_components.iter().copied());
                    }
                    _ => panic!(
                        "Term::new: non-atomic func should start with Application or Pi: {:?}",
                        func_components
                    ),
                }
            }

            // Add the argument (right child)
            if arg_len == 1 {
                // Atomic argument
                new_components.push(arg.components[0]);
            } else {
                // Compound argument - must be a compound term (Application or Pi)
                match arg.components[0] {
                    TermComponent::Application { .. } | TermComponent::Pi { .. } => {
                        new_components.extend(arg.components.iter().copied());
                    }
                    _ => panic!(
                        "Term::new: non-atomic arg {} should start with Application or Pi: {:?}",
                        i, arg.components
                    ),
                }
            }

            func_components = new_components;
        }

        Term {
            components: func_components,
        }
    }

    /// Create a new Term from a vector of components.
    /// Atomic terms have a single Atom component.
    /// Non-atomic terms start with an Application or Pi marker containing right_offset.
    fn from_components(components: Vec<TermComponent>) -> Term {
        if components.is_empty() {
            panic!("from_components: empty components");
        }
        // Basic validation: check first component
        match components[0] {
            TermComponent::Application { right_offset } => {
                // Non-atomic term: position 1 can be Atom, Application, or Pi
                if components.len() < 2 {
                    panic!(
                        "from_components: Application at start but no content. Components: {:?}",
                        components
                    );
                }
                // right_offset must be valid: at least 2 (marker + at least one left child component)
                // and less than total length (right child must exist)
                if right_offset < 2 || right_offset as usize >= components.len() {
                    panic!(
                        "from_components: outer Application has invalid right_offset {} for len {}. Components: {:?}",
                        right_offset, components.len(), components
                    );
                }
            }
            TermComponent::Pi { right_offset } => {
                // Pi type: must have at least input and output
                if components.len() < 3 {
                    panic!(
                        "from_components: Pi at start but not enough content. Components: {:?}",
                        components
                    );
                }
                if right_offset < 2 || right_offset as usize >= components.len() {
                    panic!(
                        "from_components: outer Pi has invalid right_offset {} for len {}. Components: {:?}",
                        right_offset, components.len(), components
                    );
                }
            }
            TermComponent::Atom(_) => {
                // Atomic term (len must be 1)
                if components.len() != 1 {
                    panic!(
                        "from_components: non-atomic term should start with Application or Pi, got: {:?}",
                        components
                    );
                }
            }
        }
        // Debug check to catch bad right_offsets
        #[cfg(debug_assertions)]
        {
            fn check_subterm(components: &[TermComponent], start: usize) -> usize {
                match components[start] {
                    TermComponent::Application { right_offset }
                    | TermComponent::Pi { right_offset } => {
                        let right_start = start + right_offset as usize;
                        if right_start >= components.len() {
                            panic!(
                                "from_components: right_offset at {} is {} but only {} components total. Components: {:?}",
                                start, right_offset, components.len(), components
                            );
                        }
                        // Check left child
                        let left_end = check_subterm(components, start + 1);
                        if left_end != right_start {
                            panic!(
                                "from_components: left child at {} ends at {} but right_offset says {}. Components: {:?}",
                                start + 1, left_end, right_start, components
                            );
                        }
                        // Check right child
                        check_subterm(components, right_start)
                    }
                    TermComponent::Atom(_) => start + 1,
                }
            }
            check_subterm(&components, 0);
        }
        Term { components }
    }

    /// Create a Term representing a single atom with no arguments.
    pub fn atom(atom: Atom) -> Term {
        Term {
            components: vec![TermComponent::Atom(atom)],
        }
    }

    /// Create a Pi type `(x : input) -> output`.
    /// For non-dependent arrow types, output simply doesn't reference `Atom::FreeVariable(0)`.
    pub fn pi(input: Term, output: Term) -> Term {
        // right_offset points to where the output type starts (after the marker and input)
        let right_offset = (1 + input.components.len()) as u16;
        let mut components = vec![TermComponent::Pi { right_offset }];
        components.extend(input.components);
        components.extend(output.components);
        Term { components }
    }

    /// Create an Application term with a head and multiple arguments.
    /// This creates proper curried form: f(a, b) becomes ((f a) b).
    pub fn application_multi(head: Term, args: Vec<Term>) -> Term {
        debug_assert!(
            !args.is_empty(),
            "application_multi requires at least one argument"
        );
        head.apply(&args)
    }

    // ========== Type-related methods ==========
    // These methods are for when Term is used to represent a type.

    /// Create a Term representing a ground type.
    pub fn ground_type(type_id: GroundTypeId) -> Term {
        Term::atom(Atom::Symbol(Symbol::Type(type_id)))
    }

    /// Create a Term representing a typeclass (used as a type constraint).
    pub fn typeclass(typeclass_id: TypeclassId) -> Term {
        Term::atom(Atom::Symbol(Symbol::Typeclass(typeclass_id)))
    }

    /// Returns a Term for the Bool type.
    pub fn bool_type() -> Term {
        Term::atom(Atom::Symbol(Symbol::Bool))
    }

    /// Returns a static reference to the Bool type.
    pub fn bool_type_ref() -> &'static Term {
        use std::sync::LazyLock;
        static BOOL_TYPE: LazyLock<Term> = LazyLock::new(Term::bool_type);
        &BOOL_TYPE
    }

    /// Returns a Term for the Empty type.
    pub fn empty_type() -> Term {
        Term::atom(Atom::Symbol(Symbol::Empty))
    }

    /// Returns a static reference to the Empty type.
    pub fn empty_type_ref() -> &'static Term {
        use std::sync::LazyLock;
        static EMPTY_TYPE: LazyLock<Term> = LazyLock::new(Term::empty_type);
        &EMPTY_TYPE
    }

    /// Returns a Term for the Type kind (the type of proper types).
    pub fn type_sort() -> Term {
        Term::atom(Atom::Symbol(Symbol::Type0))
    }

    /// Returns a static reference to the Type kind.
    pub fn type_sort_ref() -> &'static Term {
        use std::sync::LazyLock;
        static TYPE_KIND: LazyLock<Term> = LazyLock::new(Term::type_sort);
        &TYPE_KIND
    }

    /// Create a type application like `List[Int]` or `Map[String, Int]`.
    /// `head` is the type constructor, `args` are the type parameters.
    pub fn type_application(head: Term, args: Vec<Term>) -> Term {
        debug_assert!(
            !args.is_empty(),
            "type_application requires at least one argument"
        );
        Term::application_multi(head, args)
    }

    /// Apply a function type to get its codomain.
    /// Returns None if this is not a Pi type.
    pub fn type_apply(&self) -> Option<Term> {
        self.as_ref()
            .split_pi()
            .map(|(_, output)| output.to_owned())
    }

    /// Apply a dependent Pi type to an argument, performing substitution.
    /// For non-dependent types like `A -> B`, this just returns B.
    /// For dependent types like `Pi(Type, b0 -> b0)`, applying `Int` gives `Int -> Int`.
    /// Returns None if this is not a Pi type.
    pub fn type_apply_with_arg(&self, arg: &Term) -> Option<Term> {
        self.as_ref().split_pi().map(|(_input, output)| {
            let output = output.to_owned();
            let result = if output.has_bound_variable() {
                // Dependent type: substitute and shift
                let substituted = output.substitute_bound(0, arg);
                substituted.shift_bound(0, -1)
            } else {
                // Non-dependent type: just return output
                output
            };
            result
        })
    }

    /// Validates that this term has correct structure.
    /// Panics with detailed information if the term is malformed.
    /// Only runs in test builds or when the "validate" feature is enabled.
    pub fn validate(&self) {
        #[cfg(not(any(test, feature = "validate")))]
        {
            return;
        }

        #[cfg(any(test, feature = "validate"))]
        {
            if !self.validate_structure_impl() {
                panic!(
                    "Malformed term detected: {:?}\nLength: {}\nFirst component: {:?}",
                    self.components,
                    self.components.len(),
                    self.components.first()
                );
            }
        }
    }

    /// Validates that all right_offsets in this term are correct.
    /// Returns true if valid, false otherwise.
    /// This is primarily for debug assertions.
    #[cfg(debug_assertions)]
    pub fn validate_structure(&self) -> bool {
        self.validate_structure_impl()
    }

    /// Returns true if this term has valid structure, false otherwise.
    /// Use validate() for a version that panics with details on failure.
    pub fn validate_structure_impl(&self) -> bool {
        fn check_subterm(components: &[TermComponent], start: usize) -> Option<usize> {
            if start >= components.len() {
                return None;
            }
            match components[start] {
                TermComponent::Application { right_offset }
                | TermComponent::Pi { right_offset } => {
                    let right_start = start + right_offset as usize;
                    if right_start >= components.len() {
                        return None;
                    }
                    // Check left child ends where right child starts
                    let left_end = check_subterm(components, start + 1)?;
                    if left_end != right_start {
                        return None;
                    }
                    // Return end of right child
                    check_subterm(components, right_start)
                }
                TermComponent::Atom(_) => Some(start + 1),
            }
        }

        // Check that the first component is valid for non-atomic terms
        if self.components.len() > 1 {
            match self.components[0] {
                TermComponent::Application { right_offset }
                | TermComponent::Pi { right_offset } => {
                    if right_offset < 2 || right_offset as usize >= self.components.len() {
                        return false;
                    }
                }
                TermComponent::Atom(_) => return false, // Non-atomic must start with marker
            }
        }

        // Recursively validate the structure
        match check_subterm(&self.components, 0) {
            Some(end) => end == self.components.len(),
            None => false,
        }
    }

    /// Parse a Term from a string representation.
    /// Format: "f(a, g(b))" or just "x0" for atoms.
    /// Variables are written as x0, x1, etc.
    /// Constants are written as c0, c1, etc.
    pub fn parse(s: &str) -> Term {
        let s = s.trim();

        if s == "true" {
            return Term::atom(Atom::Symbol(Symbol::True));
        }
        if s == "false" {
            return Term::atom(Atom::Symbol(Symbol::False));
        }

        let first_paren = match s.find('(') {
            Some(i) => i,
            None => return Term::atom(Atom::new(s)),
        };

        // Figure out which commas are inside precisely one level of parentheses.
        let mut terminator_indices = vec![];
        let mut num_parens = 0;
        for (i, c) in s.chars().enumerate() {
            match c {
                '(' => num_parens += 1,
                ')' => {
                    num_parens -= 1;
                    if num_parens == 0 {
                        terminator_indices.push(i);
                    }
                }
                ',' => {
                    if num_parens == 1 {
                        terminator_indices.push(i);
                    }
                }
                _ => (),
            }
        }

        // Split the string into the head and the args.
        let head = &s[0..first_paren];
        let mut args = vec![];
        for (i, terminator_index) in terminator_indices.iter().enumerate() {
            let start = if i == 0 {
                first_paren + 1
            } else {
                terminator_indices[i - 1] + 1
            };
            args.push(Term::parse(&s[start..*terminator_index]));
        }

        // Build the component vector using Term::new
        Term::new(Atom::new(head), args)
    }

    /// Get the components of this term.
    /// Used in tests and debug assertions.
    #[cfg(test)]
    fn components(&self) -> &[TermComponent] {
        &self.components
    }

    /// Get a borrowed reference to this term.
    pub fn as_ref(&self) -> TermRef<'_> {
        // Debug validation
        #[cfg(debug_assertions)]
        if let TermComponent::Application { right_offset } = self.components[0] {
            if right_offset < 2 || right_offset as usize >= self.components.len() {
                panic!(
                    "as_ref: Term has Application at start with invalid right_offset {} for len {}. Components: {:?}",
                    right_offset, self.components.len(), self.components
                );
            }
        }
        TermRef::new(&self.components)
    }

    /// Get the head atom of this term.
    pub fn get_head_atom(&self) -> &Atom {
        // Find the head atom by skipping through nested Application markers
        let mut pos = 0;
        loop {
            match &self.components[pos] {
                TermComponent::Atom(atom) => return atom,
                TermComponent::Application { .. } => {
                    // Skip to the func part (position after the Application marker)
                    pos += 1;
                }
                TermComponent::Pi { .. } => {
                    // For Pi types, the head atom is the input type's head atom
                    pos += 1;
                }
            }
        }
    }

    /// Get the term's type as a Term with context.
    /// Uses LocalContext for variable types and KernelContext for symbol types.
    /// For function applications, applies the function type once per argument.
    pub fn get_type_with_context(
        &self,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        self.as_ref()
            .get_type_with_context(local_context, kernel_context)
    }

    /// Check if this term is atomic (no arguments).
    pub fn is_atomic(&self) -> bool {
        self.as_ref().is_atomic()
    }

    /// Check if this term is the boolean constant "true".
    pub fn is_true(&self) -> bool {
        self.as_ref().is_true()
    }

    /// Create a new Term representing the boolean constant "true".
    pub fn new_true() -> Term {
        Term::atom(Atom::Symbol(Symbol::True))
    }

    /// Create a new Term representing the boolean constant "false".
    pub fn new_false() -> Term {
        Term::atom(Atom::Symbol(Symbol::False))
    }

    /// Create a new Term representing a variable with the given index.
    pub fn new_variable(index: AtomId) -> Term {
        Term {
            components: vec![TermComponent::Atom(Atom::FreeVariable(index))],
        }
    }

    /// Check if this term is a variable (atomic and head is a variable).
    pub fn is_variable(&self) -> bool {
        self.as_ref().is_variable()
    }

    /// If this is an atomic variable, return its index.
    pub fn atomic_variable(&self) -> Option<AtomId> {
        self.as_ref().atomic_variable()
    }

    /// Check if this term contains a variable with the given index anywhere.
    pub fn has_variable(&self, index: AtomId) -> bool {
        self.as_ref().has_variable(index)
    }

    /// Check if this term contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.as_ref().has_any_variable()
    }

    /// Check if this term contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        self.as_ref().has_scoped_constant()
    }

    /// Check if this term contains any synthetic atoms.
    pub fn has_synthetic(&self) -> bool {
        self.as_ref().has_synthetic()
    }

    /// Count the number of atom components (excluding Application markers).
    pub fn atom_count(&self) -> u32 {
        self.as_ref().atom_count()
    }

    /// Returns true if this term has any arguments.
    /// This is O(1) unlike num_args() which must iterate.
    pub fn has_args(&self) -> bool {
        self.as_ref().has_args()
    }

    /// Get the number of arguments this term has.
    pub fn num_args(&self) -> usize {
        self.as_ref().num_args()
    }

    /// Iterate over the arguments of this term without allocating.
    /// Each argument is returned as a TermRef.
    pub fn iter_args(&self) -> TermRefArgsIterator<'_> {
        self.as_ref().iter_args()
    }

    /// Get the arguments of this term as owned Terms.
    /// This allocates a new vector, unlike iter_args() which borrows.
    pub fn args(&self) -> Vec<Term> {
        self.iter_args().map(|arg| arg.to_owned()).collect()
    }

    /// Iterate over all atoms in the term.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.components.iter().filter_map(|component| {
            if let TermComponent::Atom(atom) = component {
                Some(atom)
            } else {
                None
            }
        })
    }

    /// Returns the head of this term as a Term with no arguments.
    pub fn get_head_term(&self) -> Term {
        Term {
            components: vec![TermComponent::Atom(*self.get_head_atom())],
        }
    }

    /// Collects all variables in the term (recursively through arguments).
    /// Returns (AtomId, Term) pairs for each variable found (where Term is the variable's type).
    /// Uses the local_context to look up variable types.
    pub fn collect_vars(&self, local_context: &LocalContext) -> Vec<(AtomId, Term)> {
        let mut result = Vec::new();
        for atom in self.iter_atoms() {
            if let Atom::FreeVariable(id) = atom {
                let var_type = local_context
                    .get_var_type(*id as usize)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "Variable x{} not found in local context (context has {} types). Term: {}",
                            id,
                            local_context.len(),
                            self
                        )
                    });
                result.push((*id, var_type));
            }
        }
        result
    }

    /// Get the maximum variable index in this term, or None if there are no variables.
    pub fn max_variable(&self) -> Option<AtomId> {
        self.as_ref().max_variable()
    }

    /// Get the lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        self.as_ref().least_unused_variable()
    }

    /// Replace all occurrences of a variable with a term.
    /// This handles the complexity of updating Application right_offset markers when
    /// the replacement term has a different size than the variable (1 component).
    pub fn replace_variable(&self, id: AtomId, value: &Term) -> Term {
        // Special case: if this term IS the variable being replaced, just return the value
        if self.components.len() == 1 {
            if let TermComponent::Atom(Atom::FreeVariable(var_id)) = self.components[0] {
                if var_id == id {
                    return value.clone();
                }
            }
        }

        // Use a recursive approach based on decomposition
        self.replace_variable_impl(id, value)
    }

    /// Helper for replace_variable using decomposition.
    fn replace_variable_impl(&self, id: AtomId, value: &Term) -> Term {
        match self.as_ref().decompose() {
            Decomposition::Atom(atom) => {
                if let Atom::FreeVariable(var_id) = atom {
                    if *var_id == id {
                        return value.clone();
                    }
                }
                // Not the variable we're replacing, return as-is
                self.clone()
            }
            Decomposition::Application(func_ref, arg_ref) => {
                // Recursively replace in both func and arg parts
                let func = func_ref.to_owned();
                let arg = arg_ref.to_owned();

                let new_func = func.replace_variable_impl(id, value);
                let new_arg = arg.replace_variable_impl(id, value);

                // Rebuild the application
                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input_ref, output_ref) => {
                // Recursively replace in both input and output types
                let input = input_ref.to_owned();
                let output = output_ref.to_owned();

                let new_input = input.replace_variable_impl(id, value);
                let new_output = output.replace_variable_impl(id, value);

                // Rebuild the Pi type
                Term::pi(new_input, new_output)
            }
        }
    }

    /// Replace multiple variables at once.
    pub fn replace_variables(&self, var_ids: &[AtomId], replacement_terms: &[&Term]) -> Term {
        if var_ids.is_empty() {
            return self.clone();
        }

        // Apply replacements one at a time
        // This could be optimized to do all at once, but this is simpler
        let mut result = self.clone();
        for (id, term) in var_ids.iter().zip(replacement_terms.iter()) {
            result = result.replace_variable(*id, term);
        }
        result
    }

    /// Replace an atom with another atom throughout the term.
    pub fn replace_atom(&self, old_atom: &Atom, new_atom: &Atom) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                TermComponent::Atom(atom) if atom == old_atom => TermComponent::Atom(*new_atom),
                c => *c,
            })
            .collect();
        Term::from_components(new_components)
    }

    /// Renumber FreeVariables according to var_ids.
    /// var_ids[new_pos] = old_id, so each FreeVariable(old_id) becomes FreeVariable(new_pos).
    pub fn renumber_variables(&self, var_ids: &[AtomId]) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|c| match c {
                TermComponent::Atom(Atom::FreeVariable(old_id)) => {
                    let new_id = var_ids
                        .iter()
                        .position(|&x| x == *old_id)
                        .unwrap_or_else(|| panic!("Variable x{} not in var_ids", old_id));
                    TermComponent::Atom(Atom::FreeVariable(new_id as AtomId))
                }
                _ => *c,
            })
            .collect();
        Term::from_components(new_components)
    }

    /// Renumbers synthetic atoms from the provided list into the invalid range.
    pub fn invalidate_synthetics(&self, from: &[(ModuleId, AtomId)]) -> Term {
        let new_components = self
            .components
            .iter()
            .map(|component| match component {
                TermComponent::Atom(atom) => TermComponent::Atom(atom.invalidate_synthetics(from)),
                c => *c,
            })
            .collect();
        Term::from_components(new_components)
    }

    /// Replace the first `num_to_replace` variables with invalid synthetic atoms, adjusting
    /// the subsequent variable ids accordingly.
    pub fn instantiate_invalid_synthetics(&self, num_to_replace: usize) -> Term {
        self.instantiate_invalid_synthetics_with_skip(num_to_replace, 0)
    }

    /// Replace `num_to_replace` free variables (starting after `skip` variables) with invalid
    /// synthetic atoms. Variables before `skip` are preserved (they're type variables in
    /// polymorphic mode). In polymorphic mode, synthetics are applied to the type variables.
    pub fn instantiate_invalid_synthetics_with_skip(
        &self,
        num_to_replace: usize,
        skip: usize,
    ) -> Term {
        use crate::kernel::atom::INVALID_SYNTHETIC_MODULE;

        match self.as_ref().decompose() {
            Decomposition::Atom(atom) => match atom {
                Atom::FreeVariable(i) => {
                    let idx = *i as usize;
                    if idx < skip {
                        // Before skip range: preserve type variables unchanged
                        self.clone()
                    } else if idx < skip + num_to_replace {
                        // In replacement range: convert to invalid synthetic
                        // The synthetic is applied to all type variables (first `skip` vars)
                        let synthetic_id = (idx - skip) as AtomId;
                        let synthetic_atom =
                            Atom::Symbol(Symbol::Synthetic(INVALID_SYNTHETIC_MODULE, synthetic_id));
                        if skip == 0 {
                            Term::atom(synthetic_atom)
                        } else {
                            // Apply the synthetic to all type variables
                            let type_var_args: Vec<Term> = (0..skip as AtomId)
                                .map(|var_id| Term::new_variable(var_id))
                                .collect();
                            Term::new(synthetic_atom, type_var_args)
                        }
                    } else {
                        // After replacement range: shift down by num_to_replace
                        Term::new_variable((idx - num_to_replace) as AtomId)
                    }
                }
                _ => self.clone(),
            },
            Decomposition::Application(func, arg) => {
                let new_func = func
                    .to_owned()
                    .instantiate_invalid_synthetics_with_skip(num_to_replace, skip);
                let new_arg = arg
                    .to_owned()
                    .instantiate_invalid_synthetics_with_skip(num_to_replace, skip);
                Term::new(*new_func.get_head_atom(), {
                    let mut args = new_func.args();
                    args.push(new_arg);
                    args
                })
            }
            Decomposition::Pi(input, output) => {
                let new_input = input
                    .to_owned()
                    .instantiate_invalid_synthetics_with_skip(num_to_replace, skip);
                let new_output = output
                    .to_owned()
                    .instantiate_invalid_synthetics_with_skip(num_to_replace, skip);
                Term::pi(new_input, new_output)
            }
        }
    }

    /// Normalize variable IDs in place, ensuring type dependencies come first.
    /// When a variable is encountered for the first time, any variables in its type
    /// are added before the variable itself.
    pub fn normalize_var_ids_with_context(
        &mut self,
        var_ids: &mut Vec<AtomId>,
        context: &crate::kernel::local_context::LocalContext,
    ) {
        // Recursive helper to add a variable with its type dependencies first.
        // in_progress tracks variables we're currently processing to detect cycles.
        fn add_var(
            var_id: AtomId,
            var_ids: &mut Vec<AtomId>,
            context: &crate::kernel::local_context::LocalContext,
            in_progress: &mut Vec<AtomId>,
        ) {
            // Already done
            if var_ids.contains(&var_id) {
                return;
            }
            // Cycle detected
            if in_progress.contains(&var_id) {
                panic!(
                    "Cycle in type dependencies: x{} appears in its own type chain",
                    var_id
                );
            }

            in_progress.push(var_id);

            // Process type dependencies first
            if let Some(var_type) = context.get_var_type(var_id as usize) {
                for atom in var_type.iter_atoms() {
                    if let Atom::FreeVariable(dep_id) = atom {
                        add_var(*dep_id, var_ids, context, in_progress);
                    }
                }
            }

            in_progress.pop();
            var_ids.push(var_id);
        }

        let mut in_progress: Vec<AtomId> = Vec::new();

        // Renumber variables in place
        for component in &mut self.components {
            if let TermComponent::Atom(Atom::FreeVariable(i)) = component {
                let original_id = *i;
                // Add this variable (and its dependencies) if not already added
                add_var(original_id, var_ids, context, &mut in_progress);
                // Renumber to the new position
                *i = var_ids.iter().position(|&x| x == original_id).unwrap() as AtomId;
            }
        }
    }

    /// Collect variable IDs from this term in structural order.
    ///
    /// Variables are numbered by first structural occurrence. This is used for
    /// generalization matching where the PDT matching algorithm expects the first
    /// structurally-occurring variable to be Variable(0).
    ///
    /// The `var_ids` accumulates all variables encountered in structural order.
    /// Variables that only appear in type annotations (not in terms) are handled
    /// separately at the clause level.
    pub fn collect_structural_var_ids(&self, var_ids: &mut Vec<AtomId>) {
        for component in &self.components {
            if let TermComponent::Atom(Atom::FreeVariable(i)) = component {
                let original_id = *i;
                if !var_ids.contains(&original_id) {
                    var_ids.push(original_id);
                }
            }
        }
    }

    /// Second pass of normalize_var_ids_types_last: actually renumber the variables.
    /// Call this after processing all terms with normalize_var_ids_types_last.
    pub fn apply_var_renumbering(&mut self, var_ids: &[AtomId], type_var_ids: &[AtomId]) {
        for component in &mut self.components {
            if let TermComponent::Atom(Atom::FreeVariable(i)) = component {
                let original_id = *i;
                // Look up in non-type vars first, then type vars (which get higher IDs)
                if let Some(pos) = var_ids.iter().position(|&x| x == original_id) {
                    *i = pos as AtomId;
                } else if let Some(pos) = type_var_ids.iter().position(|&x| x == original_id) {
                    *i = (var_ids.len() + pos) as AtomId;
                }
            }
        }
    }

    /// Apply additional arguments to this term.
    /// Apply this term to a slice of arguments.
    pub fn apply(&self, args: &[Term]) -> Term {
        if args.is_empty() {
            return self.clone();
        }

        // Get existing args and combine with new args
        let existing_args = self.args();
        let mut all_args = existing_args;
        all_args.extend(args.iter().cloned());

        // Use Term::new to build the result with proper Application wrapper
        Term::new(*self.get_head_atom(), all_args)
    }

    /// Build a term from a spine (function + arguments).
    /// If the spine has one element, returns just that element.
    /// Otherwise, treats the first element as the function and the rest as arguments.
    pub fn from_spine(mut spine: Vec<Term>) -> Term {
        if spine.is_empty() {
            panic!("from_spine called with empty spine");
        }

        if spine.len() == 1 {
            spine.pop().unwrap()
        } else {
            let func = spine.remove(0);
            let func_args = func.args();
            let mut all_args = func_args;
            all_args.extend(spine);

            // Use Term::new to build the result with proper Application wrapper
            Term::new(*func.get_head_atom(), all_args)
        }
    }

    /// Knuth-Bendix partial reduction ordering.
    /// Returns Greater if self > other, Less if other > self.
    /// Returns Equal if they cannot be ordered (not equality in the usual sense).
    pub fn kbo_cmp(&self, other: &Term) -> std::cmp::Ordering {
        self.as_ref().kbo_cmp(&other.as_ref())
    }

    /// Extended KBO comparison - total ordering where only identical terms are equal.
    pub fn extended_kbo_cmp(&self, other: &Term) -> std::cmp::Ordering {
        self.as_ref().extended_kbo_cmp(&other.as_ref())
    }

    /// Comparison that is stable under variable renaming (alpha-equivalence).
    /// Two terms that differ only in variable naming will compare as Equal.
    pub fn stable_cmp(&self, other: &Term) -> std::cmp::Ordering {
        self.as_ref().stable_cmp(&other.as_ref())
    }

    /// Get the subterm at the given path.
    /// A path uses PathStep::Function/Argument to navigate the curried term structure.
    /// An empty path returns the whole term.
    pub fn get_term_at_path(&self, path: &[PathStep]) -> Option<Term> {
        self.as_ref().get_term_at_path(path).map(|r| r.to_owned())
    }

    /// Replace the subterm at the given path with a replacement.
    /// A path uses PathStep::Function/Argument to navigate the curried term structure.
    /// An empty path replaces the whole term.
    pub fn replace_at_path(&self, path: &[PathStep], replacement: Term) -> Term {
        if path.is_empty() {
            return replacement;
        }

        match path[0] {
            PathStep::Argument => {
                // Replace in the last argument
                match self.as_ref().split_application() {
                    Some((func, arg)) => {
                        let new_arg = arg.to_owned().replace_at_path(&path[1..], replacement);
                        func.to_owned().apply(&[new_arg])
                    }
                    None => panic!("Cannot follow Argument path on atomic term"),
                }
            }
            PathStep::Function => {
                // Replace in the function part (all but last arg)
                match self.as_ref().split_application() {
                    Some((func, arg)) => {
                        let new_func = func.to_owned().replace_at_path(&path[1..], replacement);
                        new_func.apply(&[arg.to_owned()])
                    }
                    None => panic!("Cannot follow Function path on atomic term"),
                }
            }
        }
    }

    /// Find all rewritable subterms with their paths.
    /// A path uses Vec<PathStep> to navigate the curried term structure.
    /// It is an error to call this on any variables.
    /// Any term is rewritable except for "true".
    pub fn rewritable_subterms_with_paths(&self) -> Vec<(Vec<PathStep>, Term)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        self.push_rewritable_subterms_with_paths(&mut prefix, &mut answer);
        answer
    }

    /// Helper for rewritable_subterms_with_paths.
    fn push_rewritable_subterms_with_paths(
        &self,
        prefix: &mut Vec<PathStep>,
        answer: &mut Vec<(Vec<PathStep>, Term)>,
    ) {
        if self.is_true() {
            return;
        }
        if self.is_variable() {
            panic!("expected no variables");
        }

        // In the curried view, we navigate using Function/Argument.
        // For a term f(a, b, c) = ((f a) b) c:
        // - Argument goes to c
        // - Function, Argument goes to b
        // - Function, Function, Argument goes to a
        // - Function, Function, Function goes to f
        //
        // We want to enumerate all subterms, so we recursively process:
        // 1. The function part (if this is an application)
        // 2. The argument part (if this is an application)
        // 3. This term itself

        if let Some((func, arg)) = self.as_ref().split_application() {
            // Process function part
            prefix.push(PathStep::Function);
            func.to_owned()
                .push_rewritable_subterms_with_paths(prefix, answer);
            prefix.pop();

            // Process argument part
            prefix.push(PathStep::Argument);
            arg.to_owned()
                .push_rewritable_subterms_with_paths(prefix, answer);
            prefix.pop();
        }

        // Add this term itself
        answer.push((prefix.clone(), self.clone()));
    }

    /// Check if this term contains any free variables.
    pub fn has_free_variable(&self) -> bool {
        for component in &self.components {
            if let TermComponent::Atom(Atom::FreeVariable(_)) = component {
                return true;
            }
        }
        false
    }

    /// Check if this term contains any bound variables.
    pub fn has_bound_variable(&self) -> bool {
        for component in &self.components {
            if let TermComponent::Atom(Atom::BoundVariable(_)) = component {
                return true;
            }
        }
        false
    }

    /// Check if this term has any bound variables that escape their enclosing Pi type.
    /// A bound variable "escapes" if it references a binding outside the current term.
    /// For example, in `Pi(A, b0)`, b0 is properly bound (refers to the Pi's parameter).
    /// But at top level, any BoundVariable would be escaping.
    pub fn has_escaping_bound_variable(&self) -> bool {
        self.has_escaping_bound_variable_at_depth(0)
    }

    fn has_escaping_bound_variable_at_depth(&self, depth: u16) -> bool {
        match self.as_ref().decompose() {
            Decomposition::Atom(Atom::BoundVariable(i)) => *i >= depth,
            Decomposition::Atom(_) => false,
            Decomposition::Application(f, a) => {
                f.to_owned().has_escaping_bound_variable_at_depth(depth)
                    || a.to_owned().has_escaping_bound_variable_at_depth(depth)
            }
            Decomposition::Pi(input, output) => {
                input.to_owned().has_escaping_bound_variable_at_depth(depth)
                    || output
                        .to_owned()
                        .has_escaping_bound_variable_at_depth(depth + 1)
            }
        }
    }

    /// Substitute a bound variable with a replacement term.
    /// Replaces BoundVariable(index) with the given replacement term.
    /// This is the core operation for applying a Pi type to an argument.
    pub fn substitute_bound(&self, index: u16, replacement: &Term) -> Term {
        // Special case: if this term IS the bound variable being replaced
        if self.components.len() == 1 {
            if let TermComponent::Atom(Atom::BoundVariable(i)) = self.components[0] {
                if i == index {
                    return replacement.clone();
                }
            }
        }

        self.substitute_bound_impl(index, replacement)
    }

    /// Helper for substitute_bound using decomposition.
    fn substitute_bound_impl(&self, index: u16, replacement: &Term) -> Term {
        match self.as_ref().decompose() {
            Decomposition::Atom(atom) => {
                if let Atom::BoundVariable(i) = atom {
                    if *i == index {
                        return replacement.clone();
                    }
                }
                // Not the variable we're replacing
                self.clone()
            }
            Decomposition::Application(func_ref, arg_ref) => {
                let func = func_ref.to_owned();
                let arg = arg_ref.to_owned();

                let new_func = func.substitute_bound_impl(index, replacement);
                let new_arg = arg.substitute_bound_impl(index, replacement);

                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input_ref, output_ref) => {
                let input = input_ref.to_owned();
                let output = output_ref.to_owned();

                // Substitute in input type
                let new_input = input.substitute_bound_impl(index, replacement);
                // In the output type, bound variables are shifted by 1, so we substitute at index+1
                let new_output = output.substitute_bound_impl(index + 1, replacement);

                Term::pi(new_input, new_output)
            }
        }
    }

    /// Shift bound variable indices.
    /// Variables with index >= cutoff are shifted by amount.
    /// This is used when entering/exiting binders.
    ///
    /// Example: When substituting into a Pi body, any references to outer binders
    /// need to be adjusted since we're removing one layer of binding.
    pub fn shift_bound(&self, cutoff: u16, amount: i16) -> Term {
        if amount == 0 {
            return self.clone();
        }

        self.shift_bound_impl(cutoff, amount)
    }

    /// Helper for shift_bound using decomposition.
    fn shift_bound_impl(&self, cutoff: u16, amount: i16) -> Term {
        match self.as_ref().decompose() {
            Decomposition::Atom(atom) => {
                if let Atom::BoundVariable(i) = atom {
                    if *i >= cutoff {
                        let new_i = (*i as i16 + amount) as u16;
                        return Term::atom(Atom::BoundVariable(new_i));
                    }
                }
                self.clone()
            }
            Decomposition::Application(func_ref, arg_ref) => {
                let func = func_ref.to_owned();
                let arg = arg_ref.to_owned();

                let new_func = func.shift_bound_impl(cutoff, amount);
                let new_arg = arg.shift_bound_impl(cutoff, amount);

                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input_ref, output_ref) => {
                let input = input_ref.to_owned();
                let output = output_ref.to_owned();

                // Shift in input type
                let new_input = input.shift_bound_impl(cutoff, amount);
                // In the output type, the cutoff increases by 1 (we're under a binder)
                let new_output = output.shift_bound_impl(cutoff + 1, amount);

                Term::pi(new_input, new_output)
            }
        }
    }

    /// Replace all occurrences of `old` subterm with `new` subterm.
    /// Used for abstracting over concrete types to create polymorphic types.
    pub fn replace_subterm(&self, old: &Term, new: &Term) -> Term {
        // If this term equals old, return new
        if self == old {
            return new.clone();
        }

        // Otherwise, recursively replace in subterms
        match self.as_ref().decompose() {
            Decomposition::Atom(_) => self.clone(),
            Decomposition::Application(func_ref, arg_ref) => {
                let func = func_ref.to_owned();
                let arg = arg_ref.to_owned();
                let new_func = func.replace_subterm(old, new);
                let new_arg = arg.replace_subterm(old, new);
                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input_ref, output_ref) => {
                let input = input_ref.to_owned();
                let output = output_ref.to_owned();
                let new_input = input.replace_subterm(old, new);
                let new_output = output.replace_subterm(old, new);
                Term::pi(new_input, new_output)
            }
        }
    }

    /// Convert FreeVariables to BoundVariables for type parameter binding,
    /// and shift existing BoundVariables up to make room.
    ///
    /// When creating a polymorphic type like `Π(TypeSort, T)` where T is a type parameter,
    /// `to_type_term_with_vars` creates T as FreeVariable(0). But inside a Pi type,
    /// the bound variable should be BoundVariable(n-1) (for the outermost of n type params).
    ///
    /// This function:
    /// 1. Shifts existing BoundVariables up by n (to make room for new binders)
    /// 2. Converts FreeVariable(i) to BoundVariable(n-1-i) for i < n
    ///
    /// After calling this, the term can be wrapped with n Pi types for the type parameters.
    pub fn convert_free_to_bound(&self, num_type_params: u16) -> Term {
        self.convert_free_to_bound_with_depth(num_type_params, 0)
    }

    /// Convert FreeVariables to BoundVariables with explicit depth.
    ///
    /// Use this when the converted term will be placed inside `depth` additional
    /// Pi binders before wrapping with type param Pis. For example, if building
    /// a function type `arg -> result` and then wrapping with type params, the
    /// result type should be converted with depth=1.
    pub fn convert_free_to_bound_with_depth(&self, num_type_params: u16, depth: u16) -> Term {
        if num_type_params == 0 {
            return self.clone();
        }
        self.convert_free_to_bound_at_depth(num_type_params, depth)
    }

    /// Convert FreeVariables to BoundVariables, accounting for binding depth.
    /// `depth` is the number of Pi binders we've entered (excluding the ones we'll add for type params).
    fn convert_free_to_bound_at_depth(&self, num_type_params: u16, depth: u16) -> Term {
        let result = match self.as_ref().decompose() {
            Decomposition::Atom(atom) => {
                match atom {
                    Atom::FreeVariable(i) if *i < num_type_params => {
                        // FreeVariable(i) -> BoundVariable at appropriate depth
                        // The type params will be added as outer Pi binders.
                        // At the current depth, we need to skip `depth` binders to reach the type params.
                        // Type param 0 is the outermost, so it's at index (depth + num_type_params - 1 - i)
                        let bound_id = depth + num_type_params - 1 - *i;
                        Term::atom(Atom::BoundVariable(bound_id))
                    }
                    Atom::BoundVariable(i) => {
                        // Shift existing BoundVariables up to make room for new type param binders
                        Term::atom(Atom::BoundVariable(*i + num_type_params))
                    }
                    _ => self.clone(),
                }
            }
            Decomposition::Application(func_ref, arg_ref) => {
                let func = func_ref.to_owned();
                let arg = arg_ref.to_owned();
                let new_func = func.convert_free_to_bound_at_depth(num_type_params, depth);
                let new_arg = arg.convert_free_to_bound_at_depth(num_type_params, depth);
                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input_ref, output_ref) => {
                let input = input_ref.to_owned();
                let output = output_ref.to_owned();
                // Input is at the same depth
                let new_input = input.convert_free_to_bound_at_depth(num_type_params, depth);
                // Output is one level deeper due to the Pi's binder
                let new_output = output.convert_free_to_bound_at_depth(num_type_params, depth + 1);
                Term::pi(new_input, new_output)
            }
        };
        result
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

/// Helper function for KBO domination check.
fn dominates(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    if b.len() > a.len() {
        return false;
    }
    for i in 0..b.len() {
        if a[i] < b[i] {
            return false;
        }
    }
    true
}

/// Iterator over the arguments of a TermRef, yielding borrowed references.
pub struct TermRefArgsIterator<'a> {
    components: &'a [TermComponent],
    arg_positions: Vec<(usize, usize)>, // (start, end) for each arg
    current_index: usize,
}

impl<'a> Iterator for TermRefArgsIterator<'a> {
    type Item = TermRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.arg_positions.len() {
            return None;
        }

        let (start, end) = self.arg_positions[self.current_index];
        self.current_index += 1;
        Some(TermRef::new(&self.components[start..end]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::symbol::Symbol;
    use crate::module::ModuleId;

    #[test]
    fn test_replace_head_variable_with_compound_term() {
        // This tests the bug where replacing a variable at head position with a
        // compound term incorrectly wrapped the result in a Application marker.
        //
        // Term: x0(x1) - variable x0 applied to x1
        // Replace x0 with g0(c0) - a compound term
        // Expected result: g0(c0, x1) - g0 applied to c0 and x1
        // Bug would produce: [Application, g0, c0, x1] which is invalid
        let term = Term::parse("x0(x1)");
        let replacement = Term::parse("g0(c0)");

        // Replace x0 with g0(c0)
        let result = term.replace_variable(0, &replacement);

        // Result should be g0(c0, x1)
        // This should not panic due to invalid term structure
        let head = result.get_head_atom();
        assert!(matches!(
            head,
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0))
        ));

        // The result should have exactly two args: c0 and x1
        let args: Vec<_> = result.iter_args().collect();
        assert_eq!(args.len(), 2, "Expected 2 args, got {}", args.len());

        // First arg should be c0
        let arg0_head = args[0].get_head_atom();
        assert!(matches!(arg0_head, Atom::Symbol(Symbol::ScopedConstant(0))));

        // Second arg should be x1
        let arg1_head = args[1].get_head_atom();
        assert!(matches!(arg1_head, Atom::FreeVariable(1)));
    }

    #[test]
    fn test_replace_head_variable_simple() {
        // Simpler case: x0(x1) with x0 -> c0 (atomic replacement)
        let term = Term::parse("x0(x1)");
        let replacement = Term::parse("c0");

        let result = term.replace_variable(0, &replacement);

        // Result should be c0(x1)
        let head = result.get_head_atom();
        assert!(matches!(head, Atom::Symbol(Symbol::ScopedConstant(0))));

        let args: Vec<_> = result.iter_args().collect();
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0].get_head_atom(), Atom::FreeVariable(1)));
    }

    #[test]
    fn test_replace_non_head_variable_with_compound() {
        // Non-head position should still wrap in Application
        // Term: c0(x0) - c0 applied to variable x0
        // Replace x0 with g0(c1) - a compound term
        // Result: c0(g0(c1)) - c0 applied to g0(c1)
        let term = Term::parse("c0(x0)");
        let replacement = Term::parse("g0(c1)");

        let result = term.replace_variable(0, &replacement);

        // Result should be c0(g0(c1))
        let head = result.get_head_atom();
        assert!(matches!(head, Atom::Symbol(Symbol::ScopedConstant(0))));

        let args: Vec<_> = result.iter_args().collect();
        assert_eq!(args.len(), 1);

        // The arg should be compound: g0(c1)
        let arg = &args[0];
        let arg_head = arg.get_head_atom();
        assert!(matches!(
            arg_head,
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0))
        ));
    }

    #[test]
    fn test_nested_term_comparison() {
        // Create nested terms like f(g(a)) and f(g(b))
        // This exercises iter_args() and partial_tiebreak on composite arguments
        let term1 = Term::parse("c0(c1(c2))");
        let term2 = Term::parse("c0(c1(c3))");

        // This should not panic - it exercises the code path where
        // iter_args returns a TermRef for a composite argument
        let _ = term1.extended_kbo_cmp(&term2);
    }

    #[test]
    fn test_iter_args_on_nested_term() {
        // f(g(a), b) has two args: g(a) which is composite, and b which is atomic
        let term = Term::parse("c0(c1(c2), c3)");

        let args: Vec<_> = term.iter_args().collect();
        assert_eq!(args.len(), 2);

        // Each arg should be able to get its head atom without panicking
        for arg in &args {
            let _ = arg.get_head_atom();
        }
    }

    #[test]
    fn test_new_term_format() {
        // Test that non-atomic terms start with Application
        let term = Term::parse("c0(c1)");
        assert!(
            matches!(term.components()[0], TermComponent::Application { .. }),
            "Non-atomic term should start with Application. Got: {:?}",
            term.components()
        );

        // Test atomic term does NOT start with Application
        let atomic = Term::parse("c0");
        assert!(
            matches!(atomic.components()[0], TermComponent::Atom(_)),
            "Atomic term should start with Atom"
        );

        // Test nested term
        let nested = Term::parse("c0(c1(c2), c3)");
        assert!(
            matches!(nested.components()[0], TermComponent::Application { .. }),
            "Nested term should start with Application"
        );
        assert_eq!(nested.num_args(), 2);

        // Test decompose
        let term2 = Term::parse("c0(c1, c2)");
        if let Decomposition::Application(func, arg) = term2.as_ref().decompose() {
            assert_eq!(format!("{}", func), "c0(c1)");
            assert_eq!(format!("{}", arg), "c2");
        } else {
            panic!("Expected Application decomposition");
        }
    }

    #[test]
    fn test_bound_variable_parsing() {
        // Test parsing bound variables
        let b0 = Term::parse("b0");
        assert!(matches!(b0.get_head_atom(), Atom::BoundVariable(0)));

        let b5 = Term::parse("b5");
        assert!(matches!(b5.get_head_atom(), Atom::BoundVariable(5)));

        // Bound variables in compound terms
        let term = Term::parse("c0(b0, b1)");
        assert!(term.has_bound_variable());
        assert!(!term.has_free_variable());
    }

    #[test]
    fn test_substitute_bound_simple() {
        // Replace b0 with c0
        let term = Term::parse("b0");
        let replacement = Term::parse("c0");
        let result = term.substitute_bound(0, &replacement);
        assert_eq!(format!("{}", result), "c0");
    }

    #[test]
    fn test_substitute_bound_in_application() {
        // Replace b0 in c0(b0, b1) with c1
        // Should get c0(c1, b1)
        let term = Term::parse("c0(b0, b1)");
        let replacement = Term::parse("c1");
        let result = term.substitute_bound(0, &replacement);
        assert_eq!(format!("{}", result), "c0(c1, b1)");

        // Replace b1 in c0(b0, b1) with c2
        // Should get c0(b0, c2)
        let result2 = term.substitute_bound(1, &replacement);
        assert_eq!(format!("{}", result2), "c0(b0, c1)");
    }

    #[test]
    fn test_shift_bound_simple() {
        // Shift b0 by +1 -> b1
        let term = Term::parse("b0");
        let result = term.shift_bound(0, 1);
        assert_eq!(format!("{}", result), "b1");

        // Shift b2 by -1 -> b1
        let term2 = Term::parse("b2");
        let result2 = term2.shift_bound(0, -1);
        assert_eq!(format!("{}", result2), "b1");
    }

    #[test]
    fn test_shift_bound_with_cutoff() {
        // Shift b0 with cutoff 1 (no change - 0 < 1)
        let term = Term::parse("b0");
        let result = term.shift_bound(1, 1);
        assert_eq!(format!("{}", result), "b0");

        // Shift b1 with cutoff 1 (+1 -> b2)
        let term2 = Term::parse("b1");
        let result2 = term2.shift_bound(1, 1);
        assert_eq!(format!("{}", result2), "b2");
    }

    #[test]
    fn test_shift_bound_in_compound() {
        // c0(b0, b1) shifted by +1 at cutoff 0 -> c0(b1, b2)
        let term = Term::parse("c0(b0, b1)");
        let result = term.shift_bound(0, 1);
        assert_eq!(format!("{}", result), "c0(b1, b2)");
    }

    #[test]
    fn test_has_free_and_bound_variable() {
        let free_only = Term::parse("c0(x0, x1)");
        assert!(free_only.has_free_variable());
        assert!(!free_only.has_bound_variable());

        let bound_only = Term::parse("c0(b0, b1)");
        assert!(!bound_only.has_free_variable());
        assert!(bound_only.has_bound_variable());

        let both = Term::parse("c0(x0, b0)");
        assert!(both.has_free_variable());
        assert!(both.has_bound_variable());

        let neither = Term::parse("c0(c1)");
        assert!(!neither.has_free_variable());
        assert!(!neither.has_bound_variable());
    }

    /// Test that polymorphic type application works correctly.
    ///
    /// When we have a polymorphic type `Π(TypeSort, T)` where T is the type parameter,
    /// applying it to a concrete type `Int` should give us `Int`.
    ///
    /// With BoundVariable(0), this works correctly.
    #[test]
    fn test_polymorphic_type_application() {
        // The correct representation: Pi(TypeSort, BoundVariable(0))
        // When we apply this to a concrete type, we should get that type back.
        let correct_type = Term::pi(Term::type_sort(), Term::atom(Atom::BoundVariable(0)));
        let concrete_type = Term::parse("c0"); // Some concrete type

        let result = correct_type.type_apply_with_arg(&concrete_type);
        assert!(result.is_some());
        assert_eq!(
            format!("{}", result.unwrap()),
            "c0",
            "Applying Pi(TypeSort, b0) to c0 should give c0"
        );
    }

    /// Test that FreeVariables in Pi types don't get substituted.
    ///
    /// This test documents current behavior: type_apply_with_arg only substitutes
    /// BoundVariables, not FreeVariables. This is correct behavior for type_apply_with_arg.
    ///
    /// The implication is that polymorphic types must use BoundVariable(0) for the
    /// return type, not FreeVariable(0).
    #[test]
    fn test_free_variable_not_substituted_in_type_apply() {
        // Pi(TypeSort, FreeVariable(0)) - FreeVariable doesn't get substituted
        let pi_with_free = Term::pi(Term::type_sort(), Term::atom(Atom::FreeVariable(0)));
        let concrete_type = Term::parse("c0");

        let result = pi_with_free.type_apply_with_arg(&concrete_type);
        assert!(result.is_some());
        // FreeVariable(0) is returned unchanged - this is expected behavior
        assert_eq!(
            format!("{}", result.unwrap()),
            "x0",
            "FreeVariables are not substituted by type_apply_with_arg"
        );
    }
}
