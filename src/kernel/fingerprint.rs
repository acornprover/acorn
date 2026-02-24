use std::collections::{BTreeMap, HashMap};

use crate::kernel::atom::Atom;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{Decomposition, PathStep, Term, TermRef};
use crate::kernel::types::{GroundTypeId, TypeclassId};

/// A coarse categorization of types for fingerprint indexing.
/// Ground types are distinguished by their ID, while all arrow types
/// are grouped together and all applied types are grouped together.
/// This is cheap to compare and hash while still providing useful discrimination.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum TypeCategory {
    /// A ground type, distinguished by ID (user-defined ground types only)
    Ground(GroundTypeId),

    /// The Empty type (built-in)
    Empty,

    /// The Bool type (built-in)
    Bool,

    /// The Type0 kind (built-in)
    Type0,

    /// An arrow/function type (any Pi type)
    Arrow,

    /// An applied type constructor (like List[T])
    Applied,

    /// A type variable that could match any type
    Variable,

    /// A typeclass constraint on a type variable
    /// Similar to Variable in that it can match multiple ground types (those that are instances)
    Typeclass(TypeclassId),
}

impl TypeCategory {
    /// Create a TypeCategory from a type TermRef.
    fn from_type_ref(type_ref: TermRef) -> TypeCategory {
        if type_ref.atomic_variable().is_some() {
            TypeCategory::Variable
        } else if let Some(tc_id) = type_ref.as_typeclass() {
            TypeCategory::Typeclass(tc_id)
        } else if type_ref.is_bool_type() {
            TypeCategory::Bool
        } else if type_ref.is_empty_type() {
            TypeCategory::Empty
        } else if type_ref.is_type0() {
            TypeCategory::Type0
        } else if let Some(gid) = type_ref.as_type_atom() {
            TypeCategory::Ground(gid)
        } else if type_ref.is_pi() {
            TypeCategory::Arrow
        } else {
            TypeCategory::Applied
        }
    }

    /// Whether this category could potentially match another category.
    /// Type variables can match any category.
    /// Typeclasses can match ground types (that might be instances) and other typeclasses.
    /// For efficiency, we don't have TypeStore access here to check actual instance relationships,
    /// so we're conservative: typeclasses can potentially match any ground type.
    fn could_match(&self, other: &TypeCategory) -> bool {
        match (self, other) {
            // Variables match anything
            (TypeCategory::Variable, _) | (_, TypeCategory::Variable) => true,
            // Typeclasses can match ground types (possibly instances) or other typeclasses
            // Built-in types (Bool, Empty, Type0) can also potentially have typeclass instances
            (TypeCategory::Typeclass(_), TypeCategory::Ground(_))
            | (TypeCategory::Ground(_), TypeCategory::Typeclass(_))
            | (TypeCategory::Typeclass(_), TypeCategory::Bool)
            | (TypeCategory::Bool, TypeCategory::Typeclass(_))
            | (TypeCategory::Typeclass(_), TypeCategory::Empty)
            | (TypeCategory::Empty, TypeCategory::Typeclass(_))
            | (TypeCategory::Typeclass(_), TypeCategory::Type0)
            | (TypeCategory::Type0, TypeCategory::Typeclass(_))
            | (TypeCategory::Typeclass(_), TypeCategory::Typeclass(_)) => true,
            // Other cases require exact match
            _ => self == other,
        }
    }
}

/// Get the type category of a term efficiently without allocating the full type.
/// For applications, this traverses to the return type by peeling off Pi types
/// from the head symbol's type. Falls back to full type computation for dependent types.
fn get_type_category(
    term: TermRef,
    local_context: &LocalContext,
    kernel_context: &KernelContext,
) -> TypeCategory {
    match term.decompose() {
        Decomposition::Atom(atom) => match atom {
            Atom::FreeVariable(i) => {
                let var_type = local_context
                    .get_var_type(*i as usize)
                    .expect("Variable not found in LocalContext");
                TypeCategory::from_type_ref(var_type.as_ref())
            }
            Atom::BoundVariable(_) => TypeCategory::Variable,
            Atom::Symbol(symbol) => {
                let symbol_type = kernel_context.symbol_table.get_type(*symbol);
                TypeCategory::from_type_ref(symbol_type.as_ref())
            }
        },
        Decomposition::Application(_, _) => {
            // For applications, find the head and count arguments
            let (head_atom, num_args) = get_head_and_arg_count(term);

            // Get the head's type
            let head_type = match head_atom {
                Atom::FreeVariable(i) => local_context
                    .get_var_type(*i as usize)
                    .expect("Variable not found in LocalContext"),
                Atom::Symbol(symbol) => kernel_context.symbol_table.get_type(*symbol),
                Atom::BoundVariable(_) => return TypeCategory::Variable,
            };

            // Peel off num_args Pi types to get to the return type
            let mut current_type = head_type.as_ref();
            for _ in 0..num_args {
                match current_type.split_pi() {
                    Some((_input, output)) => {
                        // Check if the output is a bound variable (dependent type)
                        if output.is_atomic() {
                            if let Decomposition::Atom(Atom::BoundVariable(_)) = output.decompose()
                            {
                                // Fall back to full computation for dependent types
                                let full_type =
                                    term.get_type_with_context(local_context, kernel_context);
                                return TypeCategory::from_type_ref(full_type.as_ref());
                            }
                        }
                        current_type = output;
                    }
                    None => {
                        // Fall back to full computation
                        let full_type = term.get_type_with_context(local_context, kernel_context);
                        return TypeCategory::from_type_ref(full_type.as_ref());
                    }
                }
            }

            TypeCategory::from_type_ref(current_type)
        }
        Decomposition::Pi(_, _) => TypeCategory::Type0,
        Decomposition::Lambda(_, _) => TypeCategory::Variable,
        Decomposition::ForAll(_, _) | Decomposition::Exists(_, _) => TypeCategory::Bool,
    }
}

/// Get the head atom and count of arguments for a term.
fn get_head_and_arg_count(term: TermRef<'_>) -> (&Atom, usize) {
    let mut current = term;
    let mut count = 0;
    loop {
        match current.decompose() {
            Decomposition::Application(func, _) => {
                count += 1;
                current = func;
            }
            Decomposition::Atom(atom) => return (atom, count),
            Decomposition::Pi(_, _) => return (&Atom::FreeVariable(0), count),
            Decomposition::Lambda(_, _) => return (&Atom::FreeVariable(0), count),
            Decomposition::ForAll(_, _) | Decomposition::Exists(_, _) => {
                return (&Atom::FreeVariable(0), count);
            }
        }
    }
}

/// A fingerprint component describes the head of a term at a particular binary path.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum FingerprintComponent {
    /// The path goes through a variable - could match anything.
    Below,

    /// The path doesn't exist (term is smaller than path).
    Nothing,

    /// Found a subterm with this type category and head atom.
    /// Variable ids are all replaced with 0 for uniform storage.
    Something(TypeCategory, Atom),
}

impl FingerprintComponent {
    fn new(
        term: &Term,
        path: &[PathStep],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> FingerprintComponent {
        match term.as_ref().get_term_at_path(path) {
            Some(subterm) => {
                let type_category = get_type_category(subterm, local_context, kernel_context);

                match subterm.get_head_atom() {
                    Atom::FreeVariable(_) => {
                        FingerprintComponent::Something(type_category, Atom::FreeVariable(0))
                    }
                    atom => FingerprintComponent::Something(type_category, *atom),
                }
            }
            None => {
                // Path doesn't exist - check if we stopped at a variable
                // Need to traverse as far as we can and check
                let mut current = term.as_ref();
                for step in path {
                    if current.atomic_variable().is_some() {
                        return FingerprintComponent::Below;
                    }
                    match current.split_application() {
                        Some((func, arg)) => {
                            current = match step {
                                PathStep::Function => func,
                                PathStep::Argument => arg,
                            };
                        }
                        None => return FingerprintComponent::Nothing,
                    }
                }
                // Should not reach here since get_term_at_path returned None
                FingerprintComponent::Nothing
            }
        }
    }

    /// Whether a unification could combine paths with these fingerprint components.
    fn could_unify(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => true,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
                if !t1.could_match(t2) {
                    return false;
                }
                if a1.is_variable() || a2.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }

    /// Whether a specialization could turn the 'self' component into the 'other' component.
    /// For specialization: query (self) is more general, stored (other) is more specific.
    /// A query can specialize into a stored pattern if:
    /// - The query has a variable (can become anything via substitution)
    /// - Or both have the same concrete atom
    fn could_specialize(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => false,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
                if !t1.could_match(t2) {
                    return false;
                }
                // If the query (self) has a variable, it can be specialized to match anything
                if a1.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }
}

/// Paths to sample for fingerprinting.
const PATHS: [&[PathStep]; 7] = [
    &[],                                       // root
    &[PathStep::Function],                     // function part
    &[PathStep::Argument],                     // argument part
    &[PathStep::Function, PathStep::Function], // function's function
    &[PathStep::Function, PathStep::Argument], // function's argument
    &[PathStep::Argument, PathStep::Function], // arg's function (if arg is application)
    &[PathStep::Argument, PathStep::Argument], // arg's argument
];

/// The fingerprints of a term at a selection of binary paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TermFingerprint {
    components: [FingerprintComponent; 7],
}

impl TermFingerprint {
    fn new(
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> TermFingerprint {
        let mut components = [FingerprintComponent::Nothing; 7];
        for (i, path) in PATHS.iter().enumerate() {
            components[i] = FingerprintComponent::new(term, path, local_context, kernel_context);
        }
        TermFingerprint { components }
    }

    fn could_unify(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_unify(&other.components[i]) {
                return false;
            }
        }
        true
    }

    fn could_specialize(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_specialize(&other.components[i]) {
                return false;
            }
        }
        true
    }
}

/// A data structure designed to quickly find which terms unify with a query term.
#[derive(Clone, Debug)]
pub struct FingerprintUnifier<T> {
    trees: HashMap<TypeCategory, BTreeMap<TermFingerprint, Vec<T>>>,
}

impl<T> FingerprintUnifier<T> {
    pub fn new() -> FingerprintUnifier<T> {
        FingerprintUnifier {
            trees: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        term: &Term,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let fingerprint = TermFingerprint::new(term, local_context, kernel_context);
        let type_category = get_type_category(term.as_ref(), local_context, kernel_context);
        let tree = self.trees.entry(type_category).or_insert(BTreeMap::new());
        tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    /// Find all T with a fingerprint that this term could unify with.
    pub fn find_unifying(
        &self,
        term: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = TermFingerprint::new(term, local_context, kernel_context);
        let type_category = get_type_category(term.as_ref(), local_context, kernel_context);

        let mut result = vec![];

        // Determine which trees to search based on the query's type category.
        // - Variable queries can match anything, so search all trees
        // - Typeclass queries can match any ground type (instances), so search all trees
        // - Ground type queries should also search Typeclass trees (since the ground type
        //   might be an instance of those typeclasses)
        // - Other queries search their category tree + Variable tree
        let trees_to_search: Vec<_> = if type_category == TypeCategory::Variable
            || matches!(type_category, TypeCategory::Typeclass(_))
        {
            self.trees.values().collect()
        } else if matches!(type_category, TypeCategory::Ground(_)) {
            // Ground types need to search: own tree + Variable tree + all Typeclass trees
            self.trees
                .iter()
                .filter(|(k, _)| {
                    **k == type_category
                        || **k == TypeCategory::Variable
                        || matches!(k, TypeCategory::Typeclass(_))
                })
                .map(|(_, v)| v)
                .collect()
        } else {
            self.trees
                .get(&type_category)
                .into_iter()
                .chain(self.trees.get(&TypeCategory::Variable))
                .collect()
        };

        // At around 8000 goals in library, we tried doing smart tree things instead of
        // dumb search, but the dumb search was faster.
        for tree in trees_to_search {
            for (f, values) in tree {
                if fingerprint.could_unify(f) {
                    for v in values {
                        result.push(v);
                    }
                }
            }
        }

        result
    }
}

/// The fingerprints of a literal at a selection of binary paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LiteralFingerprint {
    left: TermFingerprint,
    right: TermFingerprint,
}

impl LiteralFingerprint {
    fn new(
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> LiteralFingerprint {
        LiteralFingerprint {
            left: TermFingerprint::new(left, local_context, kernel_context),
            right: TermFingerprint::new(right, local_context, kernel_context),
        }
    }

    fn could_specialize(&self, other: &LiteralFingerprint) -> bool {
        self.left.could_specialize(&other.left) && self.right.could_specialize(&other.right)
    }
}

/// A data structure designed to quickly find which literals are a specialization of a query literal.
#[derive(Clone)]
pub struct FingerprintSpecializer<T> {
    trees: HashMap<TypeCategory, BTreeMap<LiteralFingerprint, Vec<T>>>,
}

impl<T> FingerprintSpecializer<T> {
    pub fn new() -> FingerprintSpecializer<T> {
        FingerprintSpecializer {
            trees: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        literal: &Literal,
        value: T,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) {
        let fingerprint =
            LiteralFingerprint::new(&literal.left, &literal.right, local_context, kernel_context);
        let type_category = get_type_category(literal.left.as_ref(), local_context, kernel_context);
        let tree = self.trees.entry(type_category).or_insert(BTreeMap::new());
        tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    /// Find all ids with a fingerprint that this literal could specialize into.
    /// Only does a single left->right direction of lookup.
    pub fn find_specializing(
        &self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<&T> {
        let fingerprint = LiteralFingerprint::new(left, right, local_context, kernel_context);
        let type_category = get_type_category(left.as_ref(), local_context, kernel_context);

        let mut result = vec![];

        // Determine which trees to search based on the query's type category.
        // - Variable queries can match anything, so search all trees
        // - Typeclass queries can match any ground type (instances), so search all trees
        // - Ground type queries should also search Typeclass trees (since the ground type
        //   might be an instance of those typeclasses)
        // - Other queries search their category tree + Variable tree
        let trees_to_search: Vec<_> = if type_category == TypeCategory::Variable
            || matches!(type_category, TypeCategory::Typeclass(_))
        {
            self.trees.values().collect()
        } else if matches!(type_category, TypeCategory::Ground(_)) {
            // Ground types need to search: own tree + Variable tree + all Typeclass trees
            self.trees
                .iter()
                .filter(|(k, _)| {
                    **k == type_category
                        || **k == TypeCategory::Variable
                        || matches!(k, TypeCategory::Typeclass(_))
                })
                .map(|(_, v)| v)
                .collect()
        } else {
            self.trees
                .get(&type_category)
                .into_iter()
                .chain(self.trees.get(&TypeCategory::Variable))
                .collect()
        };

        // At around 8000 goals in library, we tried doing smart tree things instead of
        // dumb search, but the dumb search was faster.
        for tree in trees_to_search {
            for (f, values) in tree {
                if fingerprint.could_specialize(f) {
                    for v in values {
                        result.push(v);
                    }
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_application() {
        // g0: (Bool, Bool) -> Bool
        let term = Term::parse("g0(c0, c1)");
        let (func, arg) = term.as_ref().split_application().unwrap();

        // func should be g0(c0)
        assert_eq!(func.num_args(), 1);

        // arg should be c1
        assert!(arg.is_atomic());
    }

    #[test]
    fn test_path_navigation() {
        // g0: (Bool, Bool) -> Bool
        let term = Term::parse("g0(c0, c1)");

        // [] should return the whole term
        let root = term.as_ref().get_term_at_path(&[]).unwrap();
        assert_eq!(root.num_args(), 2);

        // [Argument] should return c1 (the last arg)
        let last_arg = term
            .as_ref()
            .get_term_at_path(&[PathStep::Argument])
            .unwrap();
        assert!(last_arg.is_atomic());

        // [Function] should return g0(c0)
        let func = term
            .as_ref()
            .get_term_at_path(&[PathStep::Function])
            .unwrap();
        assert_eq!(func.num_args(), 1);

        // [Function, Argument] should return c0
        let first_arg = term
            .as_ref()
            .get_term_at_path(&[PathStep::Function, PathStep::Argument])
            .unwrap();
        assert!(first_arg.is_atomic());

        // [Function, Function] should return g0 (the head)
        let head = term
            .as_ref()
            .get_term_at_path(&[PathStep::Function, PathStep::Function])
            .unwrap();
        assert!(head.is_atomic());
    }

    #[test]
    fn test_fingerprint() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool");
        let lctx = kctx.parse_local(&["Bool", "Bool"]);

        // g0: (Bool, Bool) -> Bool, x0 and x1 are Bool
        let term = Term::parse("g0(x0, x1)");
        TermFingerprint::new(&term, &lctx, &kctx);
    }

    #[test]
    fn test_fingerprint_matching() {
        let mut kctx = KernelContext::new();
        // c0, c1 are Bool; c2 is (Bool, Bool) -> Bool
        kctx.parse_constants(&["c0", "c1"], "Bool")
            .parse_constant("c2", "(Bool, Bool) -> Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let term1 = Term::parse("c2(x0, c0)");
        let term2 = Term::parse("c2(c1, c0)");
        assert!(TermFingerprint::new(&term1, &lctx, &kctx)
            .could_unify(&TermFingerprint::new(&term2, &lctx, &kctx)));
    }

    #[test]
    fn test_fingerprint_tree() {
        let mut kctx = KernelContext::new();
        // c0, c1 are Bool; c2 is (Bool, Bool) -> Bool
        kctx.parse_constants(&["c0", "c1"], "Bool")
            .parse_constant("c2", "(Bool, Bool) -> Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = FingerprintUnifier::new();
        let term1 = Term::parse("c2(x0, c0)");
        let term2 = Term::parse("c2(c1, c0)");
        tree.insert(&term1, 1, &lctx, &kctx);
        assert!(tree.find_unifying(&term1, &lctx, &kctx).len() > 0);
        assert!(tree.find_unifying(&term2, &lctx, &kctx).len() > 0);
    }

    #[test]
    fn test_type_category_variable() {
        // Test that type variables are correctly categorized
        let type_var = Term::atom(crate::kernel::atom::Atom::FreeVariable(0));
        assert_eq!(
            TypeCategory::from_type_ref(type_var.as_ref()),
            TypeCategory::Variable
        );

        // Bool type should be categorized as Bool
        let bool_type = Term::bool_type();
        assert_eq!(
            TypeCategory::from_type_ref(bool_type.as_ref()),
            TypeCategory::Bool
        );
    }

    #[test]
    fn test_type_category_could_match() {
        use crate::kernel::types::GroundTypeId;

        let test_ground = GroundTypeId::test(0); // Use a test ground type ID

        // Variable matches anything
        assert!(TypeCategory::Variable.could_match(&TypeCategory::Ground(test_ground)));
        assert!(TypeCategory::Variable.could_match(&TypeCategory::Arrow));
        assert!(TypeCategory::Variable.could_match(&TypeCategory::Applied));
        assert!(TypeCategory::Variable.could_match(&TypeCategory::Variable));

        // Ground matches Variable or same Ground
        assert!(TypeCategory::Ground(test_ground).could_match(&TypeCategory::Variable));
        assert!(TypeCategory::Ground(test_ground).could_match(&TypeCategory::Ground(test_ground)));
        assert!(!TypeCategory::Ground(test_ground).could_match(&TypeCategory::Arrow));

        // Arrow matches Variable or Arrow
        assert!(TypeCategory::Arrow.could_match(&TypeCategory::Variable));
        assert!(TypeCategory::Arrow.could_match(&TypeCategory::Arrow));
        assert!(!TypeCategory::Arrow.could_match(&TypeCategory::Ground(test_ground)));
    }

    #[test]
    fn test_fingerprint_unifier_with_type_variable_query() {
        // Test that a query with a type variable can find terms with concrete types

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Int").parse_datatype("Nat");

        let int_id = kctx.type_store.get_ground_id_by_name("Int").unwrap();
        let nat_id = kctx.type_store.get_ground_id_by_name("Nat").unwrap();

        let int_type = Term::ground_type(int_id);
        let nat_type = Term::ground_type(nat_id);

        // c0 has type Int, c1 has type Nat
        kctx.symbol_table.add_scoped_constant(int_type.clone());
        kctx.symbol_table.add_scoped_constant(nat_type.clone());

        // Local context: x0 has type T0 (a type variable)
        let type_type = Term::type_sort();
        let type_var = Term::atom(crate::kernel::atom::Atom::FreeVariable(0));
        let lctx_with_type_var = LocalContext::from_types(vec![type_type, type_var]);

        // Local context for concrete types
        let lctx_int = LocalContext::from_types(vec![int_type.clone()]);
        let lctx_nat = LocalContext::from_types(vec![nat_type.clone()]);

        let mut tree = FingerprintUnifier::new();

        // Insert c0 (Int) and c1 (Nat) into the tree
        let c0 = Term::parse("c0");
        let c1 = Term::parse("c1");
        tree.insert(&c0, "int_term", &lctx_int, &kctx);
        tree.insert(&c1, "nat_term", &lctx_nat, &kctx);

        // Query with x1 which has type T0 (type variable) - should find both!
        let x1 = Term::parse("x1");
        let results = tree.find_unifying(&x1, &lctx_with_type_var, &kctx);

        // Should find both terms since type variable can match any type
        assert_eq!(
            results.len(),
            2,
            "Type variable query should find terms of any type"
        );
    }

    #[test]
    fn test_fingerprint_unifier_stored_type_variable() {
        // Test that a concrete query can find stored terms with type variables
        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Int");

        let int_id = kctx.type_store.get_ground_id_by_name("Int").unwrap();
        let int_type = Term::ground_type(int_id);

        // c0 has type Int
        kctx.symbol_table.add_scoped_constant(int_type.clone());

        // Local context with type variable: x0: Type, x1: T0
        let type_type = Term::type_sort();
        let type_var = Term::atom(crate::kernel::atom::Atom::FreeVariable(0));
        let lctx_with_type_var = LocalContext::from_types(vec![type_type, type_var]);

        // Local context for concrete type
        let lctx_int = LocalContext::from_types(vec![int_type.clone()]);

        let mut tree = FingerprintUnifier::new();

        // Insert x1 which has type T0 (type variable)
        let x1 = Term::parse("x1");
        tree.insert(&x1, "type_var_term", &lctx_with_type_var, &kctx);

        // Query with c0 which has concrete type Int
        let c0 = Term::parse("c0");
        let results = tree.find_unifying(&c0, &lctx_int, &kctx);

        // Should find the type variable term since it can match any type
        assert_eq!(
            results.len(),
            1,
            "Concrete query should find terms with type variables"
        );
    }

    #[test]
    fn test_fingerprint_specializer_with_type_variable() {
        // Test that FingerprintSpecializer works with type variables
        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Int");

        let int_id = kctx.type_store.get_ground_id_by_name("Int").unwrap();
        let int_type = Term::ground_type(int_id);

        // c0 and c1 have type Int
        kctx.symbol_table.add_scoped_constant(int_type.clone());
        kctx.symbol_table.add_scoped_constant(int_type.clone());

        // Local context with type variable: x0: Type, x1: T0
        let type_type = Term::type_sort();
        let type_var = Term::atom(crate::kernel::atom::Atom::FreeVariable(0));
        let lctx_with_type_var = LocalContext::from_types(vec![type_type, type_var]);

        // Local context for concrete type
        let lctx_int = LocalContext::from_types(vec![int_type.clone()]);

        let mut specializer = FingerprintSpecializer::new();

        // Insert a literal with concrete Int type: c0 = c1
        let c0 = Term::parse("c0");
        let c1 = Term::parse("c1");
        let lit = Literal::equals(c0.clone(), c1.clone());
        specializer.insert(&lit, "concrete_literal", &lctx_int, &kctx);

        // Query with type variable terms: x1 = x1
        let x1 = Term::parse("x1");
        let results = specializer.find_specializing(&x1, &x1, &lctx_with_type_var, &kctx);

        // Should find the concrete literal since type variable can specialize to Int
        assert_eq!(
            results.len(),
            1,
            "Type variable query should find concrete literals"
        );
    }

    #[test]
    fn test_type_category_typeclass() {
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut kctx = KernelContext::new();

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = kctx.type_store.add_typeclass(&monoid);

        // Create a type term for the typeclass
        let typeclass_type = Term::typeclass(monoid_id);
        let category = TypeCategory::from_type_ref(typeclass_type.as_ref());

        // Should be categorized as Typeclass
        assert!(
            matches!(category, TypeCategory::Typeclass(tc) if tc == monoid_id),
            "Typeclass type term should produce TypeCategory::Typeclass"
        );

        // Typeclass should match Ground types (conservatively, for potential instances)
        let bool_type = Term::bool_type();
        let ground_cat = TypeCategory::from_type_ref(bool_type.as_ref());
        assert!(
            category.could_match(&ground_cat),
            "Typeclass should potentially match Ground types"
        );
        assert!(
            ground_cat.could_match(&category),
            "Ground types should potentially match Typeclass"
        );

        // Typeclass should match other typeclasses
        let group = Typeclass {
            module_id: ModuleId(0),
            name: "Group".to_string(),
        };
        let group_id = kctx.type_store.add_typeclass(&group);
        let group_type = Term::typeclass(group_id);
        let group_cat = TypeCategory::from_type_ref(group_type.as_ref());
        assert!(
            category.could_match(&group_cat),
            "Typeclass should match other Typeclass"
        );

        // Typeclass should match Variable
        assert!(
            category.could_match(&TypeCategory::Variable),
            "Typeclass should match Variable"
        );
    }

    #[test]
    fn test_fingerprint_unifier_with_typeclass_query() {
        // Test that a typeclass-constrained variable can find terms of concrete types
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Int");

        let int_id = kctx.type_store.get_ground_id_by_name("Int").unwrap();
        let int_type = Term::ground_type(int_id);

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = kctx.type_store.add_typeclass(&monoid);

        // c0 has type Int
        kctx.symbol_table.add_scoped_constant(int_type.clone());

        // Local context with typeclass constraint: x0 has type Monoid (the typeclass)
        let typeclass_type = Term::typeclass(monoid_id);
        let lctx_typeclass = LocalContext::from_types(vec![typeclass_type.clone()]);

        // Local context for concrete type
        let lctx_int = LocalContext::from_types(vec![int_type.clone()]);

        let mut tree = FingerprintUnifier::new();

        // Insert c0 (Int) into the tree
        let c0 = Term::parse("c0");
        tree.insert(&c0, "int_term", &lctx_int, &kctx);

        // Query with x0 which has typeclass constraint Monoid
        let x0 = Term::parse("x0");
        let results = tree.find_unifying(&x0, &lctx_typeclass, &kctx);

        // Should find the Int term since typeclass queries search all trees
        assert_eq!(
            results.len(),
            1,
            "Typeclass query should find terms of any type (conservatively)"
        );
    }

    #[test]
    fn test_fingerprint_unifier_ground_finds_typeclass_stored() {
        // Test that a concrete query can find stored terms with typeclass constraints
        use crate::elaborator::acorn_type::Typeclass;
        use crate::module::ModuleId;

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Int");

        let int_id = kctx.type_store.get_ground_id_by_name("Int").unwrap();
        let int_type = Term::ground_type(int_id);

        // Register a typeclass
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let monoid_id = kctx.type_store.add_typeclass(&monoid);

        // c0 has type Int
        kctx.symbol_table.add_scoped_constant(int_type.clone());

        // Local context with typeclass constraint
        let typeclass_type = Term::typeclass(monoid_id);
        let lctx_typeclass = LocalContext::from_types(vec![typeclass_type.clone()]);

        // Local context for concrete type
        let lctx_int = LocalContext::from_types(vec![int_type.clone()]);

        let mut tree = FingerprintUnifier::new();

        // Insert x0 which has typeclass constraint Monoid
        let x0 = Term::parse("x0");
        tree.insert(&x0, "typeclass_term", &lctx_typeclass, &kctx);

        // Query with c0 which has concrete type Int
        let c0 = Term::parse("c0");
        let results = tree.find_unifying(&c0, &lctx_int, &kctx);

        // Should find the typeclass term since Ground queries also search Typeclass trees
        assert_eq!(
            results.len(),
            1,
            "Ground type query should find terms with typeclass constraints"
        );
    }

    #[test]
    fn test_fingerprint_unifier_with_dependent_pi_type() {
        // Test that functions with dependent Pi types like Π(R: Ring). R -> R -> R
        // can be stored and retrieved from FingerprintUnifier
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        // Create dependent Pi type: Π(R: Ring). R -> R -> R
        let add_type = kctx.parse_pi("R: Ring", "R -> R -> R");

        // c0 : Π(R: Ring). R -> R -> R (the 'add' function)
        kctx.symbol_table.add_scoped_constant(add_type.clone());

        let mut tree = FingerprintUnifier::new();

        // Insert c0 (add function with dependent Pi type)
        let c0 = Term::parse("c0");
        tree.insert(&c0, "add", &LocalContext::empty(), &kctx);

        // Query with the same term
        let results = tree.find_unifying(&c0, &LocalContext::empty(), &kctx);

        assert_eq!(results.len(), 1, "Should find the dependent Pi typed term");
        assert_eq!(results[0], &"add");
    }

    #[test]
    fn test_fingerprint_unifier_multiple_dependent_pi_functions() {
        // Test that multiple functions with the same dependent Pi type structure
        // can be stored and found
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        // Create dependent Pi type: Π(R: Ring). R -> R -> R
        let op_type = kctx.parse_pi("R: Ring", "R -> R -> R");

        // c0 : add, c1 : mul, both with type Π(R: Ring). R -> R -> R
        kctx.symbol_table.add_scoped_constant(op_type.clone());
        kctx.symbol_table.add_scoped_constant(op_type.clone());

        let mut tree = FingerprintUnifier::new();

        let c0 = Term::parse("c0");
        let c1 = Term::parse("c1");
        tree.insert(&c0, "add", &LocalContext::empty(), &kctx);
        tree.insert(&c1, "mul", &LocalContext::empty(), &kctx);

        // Query with c0 should find both (since they have the same type category)
        let results = tree.find_unifying(&c0, &LocalContext::empty(), &kctx);

        // Both have Arrow type category, so both should be candidates
        assert!(results.len() >= 1, "Should find at least one term");
    }

    #[test]
    fn test_fingerprint_unifier_dependent_pi_with_variable() {
        // Test that a type variable can unify with a dependent Pi type
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");
        kctx.parse_datatype("Bool");

        // Create dependent Pi type: Π(R: Ring). R -> R -> R
        let add_type = kctx.parse_pi("R: Ring", "R -> R -> R");

        // c0 : Π(R: Ring). R -> R -> R
        kctx.symbol_table.add_scoped_constant(add_type.clone());

        // x0 is a type variable (could be any type)
        let var_type = Term::atom(Atom::FreeVariable(0));
        let lctx_var = LocalContext::from_types(vec![var_type]);

        let mut tree = FingerprintUnifier::new();

        // Insert c0 (has dependent Pi type)
        let c0 = Term::parse("c0");
        tree.insert(&c0, "add", &LocalContext::empty(), &kctx);

        // Query with x0 (has variable type)
        let x0 = Term::parse("x0");
        let results = tree.find_unifying(&x0, &lctx_var, &kctx);

        // Variable type should potentially match Arrow type
        assert_eq!(
            results.len(),
            1,
            "Variable should find dependent Pi typed terms"
        );
    }

    #[test]
    fn test_fingerprint_specializer_with_dependent_pi_type() {
        // Test that FingerprintSpecializer works with dependent Pi types
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        // Create dependent Pi type: Π(R: Ring). R -> R -> R
        let add_type = kctx.parse_pi("R: Ring", "R -> R -> R");

        // c0 : Π(R: Ring). R -> R -> R
        kctx.symbol_table.add_scoped_constant(add_type.clone());

        let mut spec = FingerprintSpecializer::new();

        // Create a literal: c0 = c0 (reflexive equality with dependent Pi type)
        let c0 = Term::parse("c0");
        let lit = Literal::equals(c0.clone(), c0.clone());

        spec.insert(&lit, "reflexive_add", &LocalContext::empty(), &kctx);

        // Query should find the literal (using left and right terms)
        let results = spec.find_specializing(&c0, &c0, &LocalContext::empty(), &kctx);

        assert_eq!(
            results.len(),
            1,
            "Should find literal with dependent Pi typed terms"
        );
    }

    #[test]
    fn test_type_category_dependent_pi_is_arrow() {
        // Verify that dependent Pi types are categorized as Arrow
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");

        // Create dependent Pi type: Π(R: Ring). R -> R -> R
        let dependent_pi = kctx.parse_pi("R: Ring", "R -> R -> R");

        let category = TypeCategory::from_type_ref(dependent_pi.as_ref());
        assert_eq!(
            category,
            TypeCategory::Arrow,
            "Dependent Pi type should be categorized as Arrow"
        );
    }

    #[test]
    fn test_fingerprint_unifier_nested_dependent_pi() {
        // Test with more complex nested dependent Pi types
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Ring");
        kctx.parse_datatype("Nat");
        kctx.parse_type_constructor("Matrix", 3);

        // Π(R: Ring). Π(n: Nat). Matrix[R, n, n] -> Matrix[R, n, n]
        let matrix_op_type = kctx.parse_pi("R: Ring, n: Nat", "Matrix[R, n, n] -> Matrix[R, n, n]");

        // c0 : matrix operation with nested dependent type
        kctx.symbol_table
            .add_scoped_constant(matrix_op_type.clone());

        let mut tree = FingerprintUnifier::new();

        let c0 = Term::parse("c0");
        tree.insert(&c0, "matrix_op", &LocalContext::empty(), &kctx);

        let results = tree.find_unifying(&c0, &LocalContext::empty(), &kctx);

        assert_eq!(
            results.len(),
            1,
            "Should find nested dependent Pi typed term"
        );
        assert_eq!(results[0], &"matrix_op");
    }
}
