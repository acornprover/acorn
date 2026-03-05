use serde::{Deserialize, Serialize};

use crate::kernel::atom::AtomId;
use crate::kernel::term::Term;
use crate::kernel::types::TypeclassId;

/// A context stores type information for variables.
/// This is used with terms/literals/clauses to track variable types
/// without embedding them in the term structure itself.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LocalContext {
    /// The types of variables, indexed by variable id.
    /// var_types[i] is the type (as a Term) for variable x_i.
    ///
    /// Some entries may be None in intermediate contexts where variable IDs are sparse.
    var_types: Vec<Option<Term>>,
}

use std::sync::LazyLock;

/// A static empty LocalContext for use when no context is needed.
static EMPTY_LOCAL_CONTEXT: LazyLock<LocalContext> = LazyLock::new(LocalContext::empty);

impl LocalContext {
    pub fn empty() -> LocalContext {
        LocalContext { var_types: vec![] }
    }

    /// Creates a new LocalContext by remapping variables from this context.
    ///
    /// `var_ids` specifies which original variable IDs to include in the new context.
    /// The new context will have variables numbered 0, 1, 2, ... corresponding to
    /// the original variable IDs in `var_ids`.
    ///
    /// For example, if `var_ids = [2, 0, 5]`, the new context will have:
    /// - New variable 0 with the type of original variable 2
    /// - New variable 1 with the type of original variable 0
    /// - New variable 2 with the type of original variable 5
    ///
    /// FreeVariable references within the types are also updated to point to the
    /// new variable positions.
    ///
    /// # Panics
    /// Panics if any variable ID in `var_ids` is out of bounds for this context.
    pub fn remap(&self, var_ids: &[AtomId]) -> LocalContext {
        let var_types: Vec<Option<Term>> = var_ids
            .iter()
            .map(|&id| {
                Some(
                    self.get_var_type(id as usize)
                        .unwrap_or_else(|| {
                            panic!(
                                "LocalContext::remap: variable x{} not found (context has {} variables)",
                                id,
                                self.len()
                            )
                        })
                        .renumber_variables(var_ids),
                )
            })
            .collect();

        LocalContext { var_types }
    }

    /// Returns a reference to a static empty LocalContext.
    /// Use this when you need a &LocalContext but don't have actual variable types.
    pub fn empty_ref() -> &'static LocalContext {
        &EMPTY_LOCAL_CONTEXT
    }

    /// Get the type of a variable by its id.
    pub fn get_var_type(&self, var_id: usize) -> Option<&Term> {
        self.var_types.get(var_id).and_then(|t| t.as_ref())
    }

    /// Returns the typeclass constraint if the variable's type is a typeclass.
    /// When a type variable is constrained to a typeclass (e.g., `M: Monoid`),
    /// its type in the context is stored as `Symbol::Typeclass(monoid_id)`.
    pub fn get_typeclass_constraint(&self, var_id: usize) -> Option<TypeclassId> {
        self.get_var_type(var_id)
            .and_then(|t| t.as_ref().as_typeclass())
    }

    /// Returns a slice of all variable types.
    pub fn get_var_types(&self) -> &[Option<Term>] {
        &self.var_types
    }

    /// Push a new type to the context.
    /// The variable ID will be the current length of the context.
    /// Returns the assigned variable ID.
    pub fn push_type(&mut self, var_type: Term) -> usize {
        let var_id = self.var_types.len();
        self.var_types.push(Some(var_type));
        var_id
    }

    /// Set type for a variable at a specific index.
    /// If the context is too short, it will be extended with missing entries.
    pub fn set_type(&mut self, var_id: usize, var_type: Term) {
        if var_id >= self.var_types.len() {
            self.var_types.resize(var_id + 1, None);
        }
        self.var_types[var_id] = Some(var_type);
    }

    /// Truncate the context to keep only the first `len` variable types.
    pub fn truncate(&mut self, len: usize) {
        self.var_types.truncate(len);
    }

    /// Returns the number of variables in this context.
    pub fn len(&self) -> usize {
        self.var_types.len()
    }

    /// Returns true if this context has no variables.
    pub fn is_empty(&self) -> bool {
        self.var_types.is_empty()
    }

    /// Replaces all occurrences of a variable in the stored types with the given term.
    /// This is used when unification discovers that an output variable should be
    /// replaced with a concrete term.
    pub fn replace_variable(&mut self, var_id: AtomId, replacement: &Term) {
        for var_type in &mut self.var_types {
            if let Some(t) = var_type.as_mut() {
                *t = t.replace_variable(var_id, replacement);
            }
        }
    }

    /// Create a new LocalContext from types.
    pub fn from_types(var_types: Vec<Term>) -> LocalContext {
        LocalContext {
            var_types: var_types.into_iter().map(Some).collect(),
        }
    }

    /// Validates that variable types only reference lower-numbered variables.
    ///
    /// For variable x_i, its type can only contain variables x_j where j < i.
    /// This ensures a well-founded ordering where type variables come before
    /// term variables that depend on them.
    ///
    /// Returns true if all variable types satisfy this constraint.
    pub fn validate_variable_ordering(&self) -> bool {
        for (i, var_type) in self.var_types.iter().enumerate() {
            if let Some(var_type) = var_type {
                if let Some(max_var) = var_type.max_variable() {
                    if max_var as usize >= i {
                        return false;
                    }
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::types::GroundTypeId;
    use crate::module::ModuleId;

    fn ground(id: u16) -> Term {
        Term::ground_type(GroundTypeId::test(id))
    }

    #[test]
    fn test_remap_reorders_variables() {
        // Create a context with 3 variables of different types
        let ctx = LocalContext::from_types(vec![ground(0), ground(1), ground(2)]);

        // Remap to reorder: take vars [2, 0, 1]
        let remapped = ctx.remap(&[2, 0, 1]);

        assert_eq!(remapped.len(), 3);
        assert_eq!(remapped.get_var_type(0), Some(&ground(2)));
        assert_eq!(remapped.get_var_type(1), Some(&ground(0)));
        assert_eq!(remapped.get_var_type(2), Some(&ground(1)));
    }

    #[test]
    fn test_remap_subsets_variables() {
        // Create a context with 4 variables
        let ctx = LocalContext::from_types(vec![ground(0), ground(1), ground(2), ground(3)]);

        // Remap to take only vars [1, 3]
        let remapped = ctx.remap(&[1, 3]);

        assert_eq!(remapped.len(), 2);
        assert_eq!(remapped.get_var_type(0), Some(&ground(1)));
        assert_eq!(remapped.get_var_type(1), Some(&ground(3)));
    }

    #[test]
    fn test_remap_preserves_types() {
        // Create a context with a Pi type (function type)
        let pi_type = Term::pi(Term::bool_type(), Term::bool_type());
        let ground_type = Term::type_sort();

        let ctx = LocalContext::from_types(vec![ground_type.clone(), pi_type.clone()]);

        // Remap to reverse the order
        let remapped = ctx.remap(&[1, 0]);

        assert_eq!(remapped.len(), 2);
        // Check that types are preserved correctly
        assert_eq!(remapped.get_var_type(0), Some(&pi_type));
        assert_eq!(remapped.get_var_type(1), Some(&ground_type));
    }

    #[test]
    fn test_remap_empty() {
        let ctx = LocalContext::from_types(vec![Term::bool_type(), Term::type_sort()]);

        // Remap to empty
        let remapped = ctx.remap(&[]);

        assert_eq!(remapped.len(), 0);
    }

    #[test]
    fn test_remap_duplicates_variable() {
        // It's valid to include the same variable ID multiple times
        let ctx = LocalContext::from_types(vec![Term::bool_type(), Term::type_sort()]);

        let remapped = ctx.remap(&[0, 0, 1, 0]);

        assert_eq!(remapped.len(), 4);
        assert_eq!(remapped.get_var_type(0), Some(&Term::bool_type()));
        assert_eq!(remapped.get_var_type(1), Some(&Term::bool_type()));
        assert_eq!(remapped.get_var_type(2), Some(&Term::type_sort()));
        assert_eq!(remapped.get_var_type(3), Some(&Term::bool_type()));
    }

    #[test]
    #[should_panic(expected = "variable x5 not found")]
    fn test_remap_panics_on_out_of_bounds() {
        let ctx = LocalContext::from_types(vec![Term::bool_type(), Term::type_sort()]);

        // Try to remap with an out-of-bounds variable ID
        ctx.remap(&[0, 5]);
    }

    #[test]
    fn test_remap_updates_variable_references_in_types() {
        use crate::kernel::atom::Atom;

        // Create a context where x1's type references x0:
        // x0 : Type
        // x1 : List[x0] (represented as application of ground type to FreeVariable(0))
        let type_sort = Term::type_sort();
        let list_of_x0 = Term::type_application(ground(0), vec![Term::atom(Atom::FreeVariable(0))]);

        let ctx = LocalContext::from_types(vec![type_sort.clone(), list_of_x0]);

        // Original context should be valid: x1 references x0 which comes before
        assert!(ctx.validate_variable_ordering());

        // Remap to reverse the order: [1, 0]
        // This swaps x0 and x1, so new x0 gets old x1's type, new x1 gets old x0's type
        // The variable references in types must be updated to point to new positions
        let remapped = ctx.remap(&[1, 0]);

        // Verify the types have correctly updated variable references:
        // new x0 should have type List[x1] (updated from List[x0])
        // Without the fix, this would still be List[x0], creating a self-reference!
        let expected_x0_type =
            Term::type_application(ground(0), vec![Term::atom(Atom::FreeVariable(1))]);
        assert_eq!(remapped.get_var_type(0), Some(&expected_x0_type));

        // new x1 should have type Type (no variable references to update)
        assert_eq!(remapped.get_var_type(1), Some(&type_sort));

        // Note: The resulting context has a forward reference (x0 references x1),
        // which is invalid for clause construction. The caller (clause normalization)
        // is responsible for passing var_ids in an order that satisfies type dependencies.
    }

    #[test]
    fn test_remap_preserves_valid_ordering() {
        use crate::kernel::atom::Atom;

        // Create a context with a valid type dependency: x1 depends on x0
        // x0 : Type
        // x1 : List[x0]
        let type_sort = Term::type_sort();
        let list_of_x0 = Term::type_application(ground(0), vec![Term::atom(Atom::FreeVariable(0))]);
        let ctx = LocalContext::from_types(vec![type_sort.clone(), list_of_x0.clone()]);

        // Remap keeping the same order: [0, 1]
        let remapped = ctx.remap(&[0, 1]);

        // The context should remain valid
        assert!(remapped.validate_variable_ordering());
        assert_eq!(remapped.get_var_type(0), Some(&type_sort));
        assert_eq!(remapped.get_var_type(1), Some(&list_of_x0));
    }

    #[test]
    fn test_validate_variable_ordering_valid() {
        use crate::kernel::atom::Atom;

        // Valid: x0 : Type (no variable references)
        let ctx1 = LocalContext::from_types(vec![Term::type_sort()]);
        assert!(ctx1.validate_variable_ordering());

        // Valid: x0 : Type, x1 : x0 (references lower-numbered variable)
        let type_type = Term::type_sort();
        let type_var_x0 = Term::atom(Atom::FreeVariable(0));
        let ctx2 = LocalContext::from_types(vec![type_type, type_var_x0]);
        assert!(ctx2.validate_variable_ordering());

        // Valid: x0 : Bool, x1 : Bool (no variable references in types)
        let ctx3 = LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]);
        assert!(ctx3.validate_variable_ordering());
    }

    #[test]
    fn test_validate_variable_ordering_invalid_self_reference() {
        use crate::kernel::atom::Atom;

        // Invalid: x0 : x0 (variable referencing itself)
        let type_var_x0 = Term::atom(Atom::FreeVariable(0));
        let ctx = LocalContext::from_types(vec![type_var_x0]);
        assert!(!ctx.validate_variable_ordering());
    }

    #[test]
    fn test_validate_variable_ordering_invalid_forward_reference() {
        use crate::kernel::atom::Atom;

        // Invalid: x0 : x1, x1 : Type (x0 references higher-numbered x1)
        let type_type = Term::type_sort();
        let type_var_x1 = Term::atom(Atom::FreeVariable(1));
        let ctx = LocalContext::from_types(vec![type_var_x1, type_type]);
        assert!(!ctx.validate_variable_ordering());
    }

    #[test]
    fn test_validate_variable_ordering_nested_reference() {
        use crate::kernel::atom::Atom;

        // Setup: need a type constructor like List
        // For this test, we'll use a Pi type: x0 : Type, x1 : x0 -> x0

        let type_type = Term::type_sort();
        let type_var_x0 = Term::atom(Atom::FreeVariable(0));
        let arrow_type = Term::pi(type_var_x0.clone(), type_var_x0.clone()); // x0 -> x0

        // Valid: x0 : Type, x1 : x0 -> x0
        let ctx = LocalContext::from_types(vec![type_type, arrow_type]);
        assert!(ctx.validate_variable_ordering());
    }

    #[test]
    fn test_get_typeclass_constraint() {
        use crate::kernel::types::TypeclassId;

        // Create a context with a typeclass-constrained type variable
        let monoid_id = TypeclassId::test(0);
        let typeclass_type = Term::typeclass(monoid_id);
        let ctx = LocalContext::from_types(vec![typeclass_type, Term::bool_type()]);

        // x0 has typeclass constraint
        assert_eq!(ctx.get_typeclass_constraint(0), Some(monoid_id));

        // x1 has no typeclass constraint (it's Bool, not a typeclass)
        assert_eq!(ctx.get_typeclass_constraint(1), None);

        // x2 doesn't exist
        assert_eq!(ctx.get_typeclass_constraint(2), None);
    }

    #[test]
    fn test_normalize_puts_type_dependency_first() {
        use crate::kernel::atom::Atom;

        // Context where x0's type is x1 (a type variable):
        // x0 : x1
        // x1 : Type
        let type_of_x0 = Term::atom(Atom::FreeVariable(1)); // x0's type is x1
        let type_of_x1 = Term::type_sort(); // x1 is a type variable
        let ctx = LocalContext::from_types(vec![type_of_x0, type_of_x1]);

        // This context has bad ordering: x0's type references x1 which comes after
        assert!(!ctx.validate_variable_ordering());

        // Create a term that just contains x0: f(x0)
        let mut term = Term::new(
            Atom::Symbol(crate::kernel::symbol::Symbol::GlobalConstant(
                ModuleId(0),
                0,
            )),
            vec![Term::atom(Atom::FreeVariable(0))],
        );

        // Normalize the term with context awareness
        let mut var_ids = vec![];
        term.normalize_var_ids_with_context(&mut var_ids, &ctx);

        // var_ids should be [1, 0] - x1 comes first (it's the type dependency), then x0
        assert_eq!(var_ids, vec![1, 0]);

        // The term should now reference x1 (the new position of original x0)
        assert_eq!(term.to_string(), "g0_0(x1)");

        // Remap the context
        let new_ctx = ctx.remap(&var_ids);

        // New context should be valid: x0 : Type, x1 : x0
        assert!(new_ctx.validate_variable_ordering());
        assert_eq!(new_ctx.get_var_type(0), Some(&Term::type_sort()));
        assert_eq!(
            new_ctx.get_var_type(1),
            Some(&Term::atom(Atom::FreeVariable(0)))
        );
    }
}
