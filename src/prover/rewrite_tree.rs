// The RewriteTree stores a set of potential rewrites.
// A given pattern can be rewritten to multiple different output terms.

use std::collections::HashMap;

use crate::kernel::atom::{Atom as KernelAtom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::pdt::{compute_unbound_var_remap, substitute_term, term_key_prefix, Pdt};
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term, TermRef};

// Each term can correspond with multiple RewriteValues.
// This is the internal representation of the pattern, before it has been applied to a term.
#[derive(Clone)]
struct RewriteValue {
    // Which rule this rewrite is generated from
    pattern_id: usize,

    // For an s = t rule, "forwards" is rewriting s -> t, "backwards" is rewriting t -> s
    forwards: bool,

    // The pattern that we are rewriting into.
    // The pattern that we are rewriting *from* is kept in the key.
    output: Term,

    // Context for variables in the output term.
    output_context: LocalContext,
}

// The external representation of a rewrite, after it has been applied to a particular term.
#[derive(Clone)]
pub struct Rewrite {
    // Which rule this rewrite is generated from
    pub pattern_id: usize,

    // For an s = t rule, "forwards" is rewriting s -> t, "backwards" is rewriting t -> s
    pub forwards: bool,

    // The term that we are rewriting into.
    pub term: Term,

    // The context for variables in the rewritten term.
    // This is important for backwards rewrites where the context may differ from the original pattern.
    pub context: LocalContext,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum TypeConstraintKind {
    Type0,
    Typeclass(crate::kernel::types::TypeclassId),
    Other,
}

fn resolve_type_constraint_kind(
    type_term: TermRef,
    local_context: &LocalContext,
) -> TypeConstraintKind {
    match type_term.decompose() {
        Decomposition::Atom(KernelAtom::Symbol(Symbol::Type0)) => TypeConstraintKind::Type0,
        Decomposition::Atom(KernelAtom::Symbol(Symbol::Typeclass(tc_id))) => {
            TypeConstraintKind::Typeclass(*tc_id)
        }
        Decomposition::Atom(KernelAtom::FreeVariable(var_id)) => local_context
            .get_var_type(*var_id as usize)
            .map(|var_type| resolve_type_constraint_kind(var_type.as_ref(), local_context))
            .unwrap_or(TypeConstraintKind::Other),
        _ => TypeConstraintKind::Other,
    }
}

/// Recursively extracts type variable bindings by matching a pattern type against a concrete type.
///
/// For example, if pattern_type is `Pi(x1, x2)` (a function from x1 to x2) and
/// concrete_type is `Pi(Foo, Foo)`, this will bind x1 -> Foo and x2 -> Foo.
///
/// Returns false if there's an inconsistency (a type variable would need to be bound to
/// two different concrete types), true otherwise.
fn extract_type_bindings(
    pattern_type: TermRef,
    concrete_type: TermRef,
    bindings: &mut HashMap<AtomId, Term>,
) -> bool {
    match pattern_type.decompose() {
        Decomposition::Atom(KernelAtom::FreeVariable(var_id)) => {
            // Pattern type is a type variable - bind it if not already bound
            if let Some(existing_binding) = bindings.get(var_id) {
                // Check consistency: the existing binding must match the new concrete type
                if *existing_binding != concrete_type.to_owned() {
                    return false;
                }
            } else {
                bindings.insert(*var_id, concrete_type.to_owned());
            }
        }
        Decomposition::Pi(pattern_input, pattern_output) => {
            // Pattern type is a function type - recursively match input and output
            if let Decomposition::Pi(concrete_input, concrete_output) = concrete_type.decompose() {
                if !extract_type_bindings(pattern_input, concrete_input, bindings) {
                    return false;
                }
                if !extract_type_bindings(pattern_output, concrete_output, bindings) {
                    return false;
                }
            } else {
                // Pattern is Pi but concrete is not - types are incompatible
                return false;
            }
        }
        Decomposition::Application(pattern_func, pattern_arg) => {
            // Pattern type is an applied type constructor like List[x0]
            // Decomposition gives (func, last_arg) for curried applications
            if let Decomposition::Application(concrete_func, concrete_arg) =
                concrete_type.decompose()
            {
                // Recursively match both the function part and the argument
                if !extract_type_bindings(pattern_func, concrete_func, bindings) {
                    return false;
                }
                if !extract_type_bindings(pattern_arg, concrete_arg, bindings) {
                    return false;
                }
            } else {
                // Pattern is Application but concrete is not - types are incompatible
                return false;
            }
        }
        Decomposition::Lambda(pattern_input, pattern_body) => {
            // Pattern type is a lambda - recursively match input and body.
            if let Decomposition::Lambda(concrete_input, concrete_body) = concrete_type.decompose()
            {
                if !extract_type_bindings(pattern_input, concrete_input, bindings) {
                    return false;
                }
                if !extract_type_bindings(pattern_body, concrete_body, bindings) {
                    return false;
                }
            } else {
                return false;
            }
        }
        Decomposition::ForAll(pattern_binder_type, pattern_body) => {
            if let Decomposition::ForAll(concrete_binder_type, concrete_body) =
                concrete_type.decompose()
            {
                if !extract_type_bindings(pattern_binder_type, concrete_binder_type, bindings) {
                    return false;
                }
                if !extract_type_bindings(pattern_body, concrete_body, bindings) {
                    return false;
                }
            } else {
                return false;
            }
        }
        Decomposition::Exists(pattern_binder_type, pattern_body) => {
            if let Decomposition::Exists(concrete_binder_type, concrete_body) =
                concrete_type.decompose()
            {
                if !extract_type_bindings(pattern_binder_type, concrete_binder_type, bindings) {
                    return false;
                }
                if !extract_type_bindings(pattern_body, concrete_body, bindings) {
                    return false;
                }
            } else {
                return false;
            }
        }
        Decomposition::Atom(pattern_atom) => {
            // Pattern type is a concrete atom (not a variable)
            // It must match the concrete type exactly, with one exception:
            // A Typeclass constraint can match TypeSort (e.g., P: Pointed matches concrete types)
            if let Decomposition::Atom(concrete_atom) = concrete_type.decompose() {
                if pattern_atom != concrete_atom {
                    // Allow Typeclass to match TypeSort
                    // A typeclass constraint like P: Pointed should match any concrete type
                    // Concrete types have kind Type (TypeSort), not the typeclass kind
                    let is_typeclass_matching_typesort = matches!(
                        (pattern_atom, concrete_atom),
                        (
                            KernelAtom::Symbol(Symbol::Typeclass(_)),
                            KernelAtom::Symbol(Symbol::Type0)
                        )
                    );
                    if !is_typeclass_matching_typesort {
                        return false;
                    }
                }
            } else {
                // Pattern is Atom but concrete is not - types are incompatible
                return false;
            }
        }
    }
    true
}

/// Builds bindings from structural replacements, including inferred type variable bindings.
///
/// When a pattern variable's type contains type variables, and we've matched
/// the pattern variable to a concrete term, we can infer the type variables'
/// values from the matched term's type.
///
/// Example 1: Pattern variable x0 has type x1 where x1: Type.
/// If we match x0 → c1 where c1: Foo, then x1 should be bound to Foo.
///
/// Example 2: Pattern variable x0 has type (x1 -> x2) where x1, x2: Type.
/// If we match x0 → f where f: Foo -> Bar, then x1 -> Foo and x2 -> Bar.
///
/// Returns None if there's a type variable inconsistency (e.g., same type variable
/// would need to bind to different concrete types). Otherwise returns a HashMap
/// mapping pattern variable IDs to their replacement terms.
/// Resolves a type through variable references to find the ultimate typeclass constraint.
/// For example, if x1 has type x0 and x0 has type Typeclass(Field), this returns Some(Field).
fn resolve_typeclass_constraint(
    var_type: TermRef,
    pattern_context: &LocalContext,
) -> Option<crate::kernel::types::TypeclassId> {
    // Direct typeclass constraint
    if let Some(tc_id) = var_type.as_typeclass() {
        return Some(tc_id);
    }
    // Indirect constraint via type variable reference
    if let Decomposition::Atom(KernelAtom::FreeVariable(ref_var)) = var_type.decompose() {
        if let Some(ref_type) = pattern_context.get_var_type(*ref_var as usize) {
            return resolve_typeclass_constraint(ref_type.as_ref(), pattern_context);
        }
    }
    None
}

fn typeclass_binding_is_compatible(
    actual_tc_id: crate::kernel::types::TypeclassId,
    required_tc_id: crate::kernel::types::TypeclassId,
    kernel_context: &KernelContext,
) -> bool {
    actual_tc_id == required_tc_id
        || kernel_context
            .type_store
            .typeclass_extends(actual_tc_id, required_tc_id)
}

fn type_term_satisfies_typeclass_constraint(
    type_term: TermRef,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
    required_tc_id: crate::kernel::types::TypeclassId,
) -> bool {
    if kernel_context
        .type_store
        .type_term_is_instance_of(type_term, query_context, required_tc_id)
    {
        return true;
    }

    if let Some(var_id) = type_term.atomic_variable() {
        let Some(var_type) = query_context.get_var_type(var_id as usize) else {
            return false;
        };
        let Some(actual_tc_id) = resolve_typeclass_constraint(var_type.as_ref(), query_context)
        else {
            return false;
        };
        return typeclass_binding_is_compatible(actual_tc_id, required_tc_id, kernel_context);
    }

    false
}

fn is_proper_type_expr(
    type_expr: TermRef,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> bool {
    match type_expr.decompose() {
        Decomposition::Atom(KernelAtom::Symbol(Symbol::Bool)) => true,
        Decomposition::Atom(KernelAtom::Symbol(Symbol::Type(ground_id))) => {
            kernel_context.type_store.get_arity(*ground_id) == 0
        }
        Decomposition::Atom(KernelAtom::FreeVariable(var_id)) => query_context
            .get_var_type(*var_id as usize)
            .is_some_and(|var_type| {
                matches!(
                    resolve_type_constraint_kind(var_type.as_ref(), query_context),
                    TypeConstraintKind::Type0 | TypeConstraintKind::Typeclass(_)
                )
            }),
        Decomposition::Application(_, _) => {
            let Some((head, args)) = type_expr.split_application_multi() else {
                return false;
            };
            let Some(ground_id) = head.as_ref().as_type_atom() else {
                return false;
            };
            if args.len() != kernel_context.type_store.get_arity(ground_id) as usize {
                return false;
            }
            args.iter()
                .all(|arg| is_proper_type_expr(arg.as_ref(), query_context, kernel_context))
        }
        Decomposition::Pi(input, _) => !input.is_type_param_kind(),
        _ => false,
    }
}

fn term_satisfies_typeclass_constraint(
    term: TermRef,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
    required_tc_id: crate::kernel::types::TypeclassId,
) -> bool {
    let term_type = term.get_type_with_context(query_context, kernel_context);

    if term_type.as_ref().is_type0() || term_type.as_ref().as_typeclass().is_some() {
        return type_term_satisfies_typeclass_constraint(
            term,
            query_context,
            kernel_context,
            required_tc_id,
        );
    }

    type_term_satisfies_typeclass_constraint(
        term_type.as_ref(),
        query_context,
        kernel_context,
        required_tc_id,
    )
}

fn build_bindings(
    structural_replacements: &[TermRef],
    pattern_context: &LocalContext,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> Option<HashMap<AtomId, Term>> {
    let mut bindings: HashMap<AtomId, Term> = HashMap::new();

    // Add structural replacements to bindings
    for (i, replacement) in structural_replacements.iter().enumerate() {
        if replacement.to_owned().has_escaping_bound_variable() {
            // Rewrites may not instantiate a free pattern variable with a term that only
            // has meaning relative to an enclosing binder in the query.
            return None;
        }
        bindings.insert(i as AtomId, replacement.to_owned());
    }

    // Infer type variable bindings from the types of matched terms
    for (i, replacement) in structural_replacements.iter().enumerate() {
        if let Some(var_type) = pattern_context.get_var_type(i) {
            // Check typeclass constraints before inferring any dependent bindings.
            // This rejects parameterized type terms like List[T] for constraints such as
            // F: Add, while still allowing query-side type variables that already carry
            // a compatible typeclass constraint.
            if let Some(tc_id) = resolve_typeclass_constraint(var_type.as_ref(), pattern_context) {
                if !term_satisfies_typeclass_constraint(
                    *replacement,
                    query_context,
                    kernel_context,
                    tc_id,
                ) {
                    return None;
                }
            }

            // Get the type of the replacement term
            let replacement_type = replacement.get_type_with_context(query_context, kernel_context);
            // Recursively extract type variable bindings by matching pattern type to concrete type
            if !extract_type_bindings(var_type.as_ref(), replacement_type.as_ref(), &mut bindings) {
                return None;
            }
        }
    }

    // Enforce typeclass constraints for any inferred type variable bindings.
    // These bindings can be introduced via extract_type_bindings and may not
    // correspond to a structural replacement.
    for (&var_id, bound_term) in &bindings {
        // Structural replacements were already validated above (including typeclass checks
        // that use the replacement's type). Here we only enforce constraints for bindings
        // inferred via extract_type_bindings.
        if (var_id as usize) < structural_replacements.len() {
            continue;
        }
        let Some(var_type) = pattern_context.get_var_type(var_id as usize) else {
            continue;
        };
        if matches!(
            resolve_type_constraint_kind(var_type.as_ref(), pattern_context),
            TypeConstraintKind::Type0
        ) && !is_proper_type_expr(bound_term.as_ref(), query_context, kernel_context)
        {
            return None;
        }
        let Some(tc_id) = resolve_typeclass_constraint(var_type.as_ref(), pattern_context) else {
            continue;
        };

        match bound_term.as_ref().decompose() {
            // Allow unbound type variables (polymorphic matching)
            Decomposition::Atom(KernelAtom::FreeVariable(_)) => {}
            _ => {
                // Require a concrete type instance for typeclass constraints
                if !kernel_context.type_store.type_term_is_instance_of(
                    bound_term.as_ref(),
                    query_context,
                    tc_id,
                ) {
                    return None;
                }
            }
        }
    }

    Some(bindings)
}

#[derive(Clone)]
pub struct RewriteTree {
    tree: Pdt<Vec<RewriteValue>>,
}

impl RewriteTree {
    pub fn new() -> RewriteTree {
        RewriteTree { tree: Pdt::new() }
    }

    // Inserts one direction.
    // NOTE: The input term's variable ids must be normalized.
    fn insert_terms(
        &mut self,
        pattern_id: usize,
        input_term: &Term,
        output_term: &Term,
        forwards: bool,
        local_context: &LocalContext,
    ) {
        if input_term.is_true() {
            panic!("cannot rewrite true to something else");
        }
        let value = RewriteValue {
            pattern_id,
            forwards,
            output: output_term.clone(),
            output_context: local_context.clone(),
        };
        Pdt::insert_or_append(&mut self.tree, input_term, value, local_context);
    }

    // Inserts both directions.
    // NOTE: The input term's variable ids must be normalized.
    pub fn insert_literal(
        &mut self,
        pattern_id: usize,
        literal: &Literal,
        local_context: &LocalContext,
    ) {
        // Already normalized
        self.insert_terms(
            pattern_id,
            &literal.left,
            &literal.right,
            true,
            local_context,
        );

        if !literal.right.is_true() {
            let (mut right, mut left, reversed_context) =
                literal.normalized_reversed(local_context);

            // The PDT expects variables numbered by structural occurrence order (0, 1, 2, ...),
            // but normalized_reversed uses type-dependency ordering. We need to renumber
            // variables structurally for PDT matching to work correctly.
            let mut structural_var_ids: Vec<AtomId> = vec![];
            right.collect_structural_var_ids(&mut structural_var_ids);
            left.collect_structural_var_ids(&mut structural_var_ids);

            // Also collect type variables that only appear in the types of structural variables.
            // These "phantom" type variables don't appear in terms but are needed when remapping
            // the context. We iterate until no new variables are found.
            let mut i = 0;
            while i < structural_var_ids.len() {
                let var_id = structural_var_ids[i];
                if let Some(var_type) = reversed_context.get_var_type(var_id as usize) {
                    for atom in var_type.iter_atoms() {
                        if let KernelAtom::FreeVariable(dep_id) = atom {
                            if !structural_var_ids.contains(dep_id) {
                                structural_var_ids.push(*dep_id);
                            }
                        }
                    }
                }
                i += 1;
            }

            // Renumber variables in both terms
            right.apply_var_renumbering(&structural_var_ids, &[]);
            left.apply_var_renumbering(&structural_var_ids, &[]);

            // Remap the context to match the new variable ordering
            let structural_context = reversed_context.remap(&structural_var_ids);

            self.insert_terms(pattern_id, &right, &left, false, &structural_context);
        }
    }

    // The callback is on (rule id, forwards, new term, new context).
    fn find_rewrites<F>(
        &self,
        input_term: TermRef,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
        next_var: AtomId,
        callback: &mut F,
    ) where
        F: FnMut(usize, bool, Term, LocalContext),
    {
        let mut key = term_key_prefix();
        let mut replacements: Vec<TermRef> = vec![];
        self.tree.find_term_matches_while(
            &mut key,
            &[input_term],
            local_context,
            kernel_context,
            &mut replacements,
            &mut |value_id, replacements| {
                for value in &self.tree.values[value_id] {
                    // Step 1: Build bindings from structural replacements + inferred type bindings
                    // Skip this rewrite if there's a type variable inconsistency
                    let bindings = match build_bindings(
                        replacements,
                        &value.output_context,
                        local_context,
                        kernel_context,
                    ) {
                        Some(b) => b,
                        None => continue, // Type variable inconsistency - skip this rewrite
                    };

                    // Step 2: Compute var_remap and output context for unbound variables
                    let (var_remap, new_context) = compute_unbound_var_remap(
                        &value.output,
                        &value.output_context,
                        local_context,
                        &bindings,
                        next_var,
                    );

                    // Step 3: Substitute into output term
                    let new_term = substitute_term(&value.output, &bindings, &var_remap);

                    callback(value.pattern_id, value.forwards, new_term, new_context);
                }
                true
            },
        );
    }

    // Finds all the ways to rewrite the given term, at the root level.
    //
    // Sometimes rewrites have to create a new variable.
    // When we create new variables, we start numbering from next_var.
    //
    // Returns a list of (pattern_id, forwards, new_term) tuples.
    pub fn get_rewrites(
        &self,
        input_term: &Term,
        next_var: AtomId,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Vec<Rewrite> {
        let mut answer = vec![];
        self.find_rewrites(
            input_term.as_ref(),
            local_context,
            kernel_context,
            next_var,
            &mut |pattern_id, forwards, term, context| {
                answer.push(Rewrite {
                    pattern_id,
                    forwards,
                    term,
                    context,
                });
            },
        );
        answer
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::atom::Atom;

    use super::*;

    #[test]
    fn test_rewrite_tree_atoms() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1"], "Bool");
        let lctx = kctx.parse_local(&[]);

        let mut tree = RewriteTree::new();
        tree.insert_terms(0, &Term::parse("c1"), &Term::parse("c0"), true, &lctx);
        let rewrites = tree.get_rewrites(&Term::parse("c1"), 0, &lctx, &kctx);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].term, Term::parse("c0"));
    }

    #[test]
    fn test_rewrite_tree_functions() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c2"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = RewriteTree::new();
        // Rewrite rule: g1(x0, c0) -> g0(x0, c0)
        tree.insert_terms(
            0,
            &Term::parse("g1(x0, c0)"),
            &Term::parse("g0(x0, c0)"),
            true,
            &lctx,
        );

        // Query: g1(c2, c0) should rewrite to g0(c2, c0)
        let query_lctx = kctx.parse_local(&[]);
        let rewrites = tree.get_rewrites(&Term::parse("g1(c2, c0)"), 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].term, Term::parse("g0(c2, c0)"));
    }

    #[test]
    fn test_rewrite_tree_multiple_rewrites() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("g3", "(Bool, Bool) -> Bool")
            .parse_constant("g4", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c2"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = RewriteTree::new();
        // Rule 1: g1(x0, c2) -> g3(x0, c0)
        tree.insert_terms(
            0,
            &Term::parse("g1(x0, c2)"),
            &Term::parse("g3(x0, c0)"),
            true,
            &lctx,
        );
        // Rule 2: g1(c2, x0) -> g4(x0, c0)
        tree.insert_terms(
            1,
            &Term::parse("g1(c2, x0)"),
            &Term::parse("g4(x0, c0)"),
            true,
            &lctx,
        );

        // Query: g1(c2, c2) should match both rules
        let query_lctx = kctx.parse_local(&[]);
        let rewrites = tree.get_rewrites(&Term::parse("g1(c2, c2)"), 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 2);
        assert_eq!(rewrites[0].term, Term::parse("g3(c2, c0)"));
        assert_eq!(rewrites[1].term, Term::parse("g4(c2, c0)"));
    }

    #[test]
    fn test_rewrite_tree_inserting_edge_literals() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool");

        let mut tree = RewriteTree::new();
        // x0 = c0 where both are Bool
        let clause1 = kctx.parse_clause("x0 = c0", &["Bool"]);
        tree.insert_literal(0, &clause1.literals[0], clause1.get_local_context());
        // c0 alone as literal (Bool = true)
        let clause2 = kctx.parse_clause("c0", &[]);
        tree.insert_literal(1, &clause2.literals[0], clause2.get_local_context());
    }

    #[test]
    fn test_new_variable_created_during_rewrite() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c1"], "Bool");

        let mut tree = RewriteTree::new();
        // g1(x0, c1) = c0 means c0 rewrites to g1(x1, c1) with a new variable x1
        let clause = kctx.parse_clause("g1(x0, c1) = c0", &["Bool"]);
        tree.insert_literal(0, &clause.literals[0], clause.get_local_context());

        let query_lctx = kctx.parse_local(&[]);
        let rewrites = tree.get_rewrites(&Term::parse("c0"), 1, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].term, Term::parse("g1(x1, c1)"));
    }

    #[test]
    fn test_rewrite_tree_checks_type() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("c0", "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree = RewriteTree::new();
        // Make a rule for Bool-typed variables
        let var_bool = Term::atom(Atom::FreeVariable(0));
        tree.insert_terms(0, &var_bool, &var_bool, true, &lctx);

        // A Bool constant should match it
        let query_lctx = kctx.parse_local(&[]);
        let const_bool = Term::parse("c0");
        let rewrites = tree.get_rewrites(&const_bool, 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 1);

        // A different type term should not match
        // g0 has type (Bool, Bool) -> Bool which is different from Bool
        let func_term = Term::parse("g0");
        let rewrites = tree.get_rewrites(&func_term, 0, &query_lctx, &kctx);
        assert_eq!(rewrites.len(), 0);
    }

    #[test]
    fn test_rewrite_tree_polymorphic_forward() {
        // Test forward rewriting with polymorphic types.
        // Pattern: g0(T, x) = x where T: Type, x: T
        // Query: g0(Foo, c1) should rewrite to c1

        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T1" to avoid conflict with type variable syntax (T0, T1, etc.)
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_constant("c1", "Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("g0(Foo, c1)");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Filter for forward rewrites only (backwards rewrites also match but produce different results)
        let forward_rewrites: Vec<_> = rewrites.iter().filter(|r| r.forwards).collect();
        assert_eq!(forward_rewrites.len(), 1);
        assert_eq!(forward_rewrites[0].term, kctx.parse_term("c1"));
    }

    #[test]
    fn test_rewrite_tree_polymorphic_nested() {
        // Test forward rewriting with nested polymorphic functions.
        // Pattern: g1(T, g0(T, x)) = x
        // Query: g1(Foo, g0(Foo, c1)) should rewrite to c1

        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T1" to avoid conflict with type variable syntax (T0, T1, etc.)
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_polymorphic_constant("g1", "T: Type", "T -> T");
        kctx.parse_constant("c1", "Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g1(x0, g0(x0, x1)) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("g1(Foo, g0(Foo, c1))");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Filter for forward rewrites only (backwards rewrites also match but produce different results)
        let forward_rewrites: Vec<_> = rewrites.iter().filter(|r| r.forwards).collect();
        assert_eq!(forward_rewrites.len(), 1);
        assert_eq!(forward_rewrites[0].term, kctx.parse_term("c1"));
    }

    #[test]
    fn test_rewrite_tree_polymorphic_backwards() {
        // Test backwards rewriting with polymorphic types.
        //
        // Pattern: g0(T, x) = x where T: Type, x: T
        // Backwards rewrite: x -> g0(T, x)
        //
        // When we rewrite c1 (type Foo) backwards, T should be inferred from
        // the type of the matched term. Result should be g0(Foo, c1).

        let mut kctx = KernelContext::new();
        // Use "Foo" instead of "T1" to avoid conflict with type variable syntax (T0, T1, etc.)
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_constant("c1", "Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        // Query: c1 (for backwards rewrite)
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c1");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Should find a backwards rewrite
        assert_eq!(rewrites.len(), 1, "Should find one backwards rewrite");

        // The type variable T should be inferred from c1's type (Foo)
        let expected = kctx.parse_term("g0(Foo, c1)");
        assert_eq!(
            rewrites[0].term, expected,
            "Backwards rewrite should infer type variable from matched term's type"
        );
    }

    #[test]
    fn test_rewrite_tree_polymorphic_backwards_rejects_higher_kinded_type_binding() {
        let mut kctx = KernelContext::new();
        kctx.parse_polymorphic_constant("g0", "T: Type", "T -> T");
        kctx.parse_constant("c0", "Type -> Bool");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Type", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c0");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);
        let backward_rewrites: Vec<_> = rewrites.iter().filter(|r| !r.forwards).collect();

        assert!(
            backward_rewrites.is_empty(),
            "Backwards rewrite should reject inferred higher-kinded type bindings like \
             Type -> Bool. Got {} backward rewrites.",
            backward_rewrites.len()
        );
    }

    #[test]
    fn test_rewrite_tree_two_type_params_backwards() {
        // Test backwards rewriting with TWO type parameters (like Pair[T, U]).
        // This is more complex because we need to infer both T and U.
        //
        // Pattern: pair(T, U, x, y).first = x where T: Type, U: Type, x: T, y: U
        // Backwards rewrite: x -> pair(T, U, x, ???).first
        //
        // When we only have x, we can infer T from x's type, but we can't know
        // what U or y should be. They should remain as new variables.

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");
        kctx.parse_datatype("Bar");
        kctx.parse_datatype("Result");
        // g0 = pair: (T: Type) -> (U: Type) -> T -> U -> Result
        kctx.parse_polymorphic_constant("g0", "T: Type, U: Type", "T -> U -> Result");
        // g1 = first: (T: Type) -> (U: Type) -> Result -> T
        kctx.parse_polymorphic_constant("g1", "T: Type, U: Type", "Result -> T");
        kctx.parse_constant("c1", "Foo");
        kctx.parse_constant("c2", "Bar");

        let mut tree = RewriteTree::new();

        // Pattern: g1(T, U, g0(T, U, x, y)) = x
        // In normalized form: g1(x0, x1, g0(x0, x1, x2, x3)) = x2
        // where x0: Type, x1: Type, x2: x0, x3: x1
        let pattern_clause = kctx.parse_clause(
            "g1(x0, x1, g0(x0, x1, x2, x3)) = x2",
            &["Type", "Type", "x0", "x1"],
        );
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        // Query: c1 (for backwards rewrite)
        // We're trying to backwards-rewrite c1 to g1(..., g0(..., c1, ?))
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c1");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Should find a backwards rewrite
        assert!(
            !rewrites.is_empty(),
            "Should find at least one backwards rewrite"
        );

        // Check the rewrite context is well-formed
        for rewrite in &rewrites {
            // The context should have proper types for all variables
            // In particular, if there are variables with type=FreeVariable(n),
            // then n should have type=Type
            for (i, var_type) in rewrite.context.get_var_types().iter().enumerate() {
                let Some(var_type) = var_type else {
                    continue;
                };
                if let Decomposition::Atom(KernelAtom::FreeVariable(type_var_id)) =
                    var_type.as_ref().decompose()
                {
                    let type_var_idx = *type_var_id as usize;
                    let type_of_type_var = rewrite.context.get_var_type(type_var_idx);
                    assert!(
                        type_of_type_var.is_some(),
                        "Variable x{} has type x{}, but x{} has no type in context. Context: {:?}",
                        i,
                        type_var_id,
                        type_var_id,
                        rewrite.context.get_var_types()
                    );
                }
            }

            // Check that the term's type is well-formed with respect to its context
            let term_type = rewrite.term.get_type_with_context(&rewrite.context, &kctx);

            // Since we're rewriting c1 (type Foo), the output term should also have type Foo
            // The backwards rewrite produces g1(T, U, g0(T, U, c1, y)) where:
            // - T should be inferred as Foo (from c1's type)
            // - U is a new variable
            // - y is a new variable of type U
            //
            // The result type of g1(T, U, ...) should be T, which should be Foo.
            let expected_type = kctx.parse_type("Foo");
            assert_eq!(
                term_type,
                expected_type,
                "Rewritten term should have type Foo. Got: {:?}. Term: {}. Context: {:?}",
                term_type,
                rewrite.term,
                rewrite.context.get_var_types()
            );
        }
    }

    #[test]
    fn test_rewrite_tree_type_only_variable() {
        // Test inserting a literal where a type variable only appears in another
        // variable's type, not in any term.
        //
        // Pattern: x0(x1) = x0(x1)
        // where x0: (Foo -> x2), x1: Foo, x2: Type
        //
        // x2 is a type variable that only appears in x0's type (the return type
        // of the function), not in the term x0(x1). When insert_literal reverses
        // this and collects structural_var_ids, x2 is missing, causing remap to fail.

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("x0(x1) = x0(x1)", &["Foo -> x2", "Foo", "Type"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );
    }

    #[test]
    fn test_rewrite_tree_function_typed_pattern_variable() {
        // Test backwards rewriting with function-typed pattern variables.
        // This is the "compose" pattern: compose(T, U, V, f: U->V, g: T->U)(x: T) = f(g(x))
        //
        // Pattern: g0(T, U, V, f, g, x) = f(g(x))
        //   where T: Type, U: Type, V: Type
        //   f: U -> V
        //   g: T -> U
        //   x: T
        //
        // Query: c0(c1(c2)) where c0: Foo -> Foo, c1: Foo -> Foo, c2: Foo
        // Backwards rewrite should produce: g0(Foo, Foo, Foo, c0, c1, c2)
        //
        // The bug: when pattern variable f has type (U -> V), we need to infer
        // U and V from the type of the matched term c0. Currently build_bindings
        // only infers type variables when the pattern variable's type IS a type
        // variable, not when it CONTAINS type variables.

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");
        // g0 = compose: (T: Type) -> (U: Type) -> (V: Type) -> (U -> V) -> (T -> U) -> T -> V
        kctx.parse_polymorphic_constant(
            "g0",
            "T: Type, U: Type, V: Type",
            "(U -> V) -> (T -> U) -> T -> V",
        );
        kctx.parse_constant("c0", "Foo -> Foo"); // like h
        kctx.parse_constant("c1", "Foo -> Foo"); // like k
        kctx.parse_constant("c2", "Foo"); // like y

        let mut tree = RewriteTree::new();

        // Pattern: g0(x0, x1, x2, x3, x4, x5) = x3(x4(x5))
        // where x0: Type, x1: Type, x2: Type, x3: (x1 -> x2), x4: (x0 -> x1), x5: x0
        let pattern_clause = kctx.parse_clause(
            "g0(x0, x1, x2, x3, x4, x5) = x3(x4(x5))",
            &["Type", "Type", "Type", "x1 -> x2", "x0 -> x1", "x0"],
        );
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        // Query: c0(c1(c2)) (for backwards rewrite)
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c0(c1(c2))");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Should find a backwards rewrite
        let backwards_rewrites: Vec<_> = rewrites.iter().filter(|r| !r.forwards).collect();
        assert!(
            !backwards_rewrites.is_empty(),
            "Should find at least one backwards rewrite"
        );

        // Verify the rewritten term is well-typed (this is where the bug manifests)
        for rewrite in &backwards_rewrites {
            // This should not panic - if type variables weren't properly inferred,
            // get_type_with_context will fail with "Function type expected"
            let term_type = rewrite.term.get_type_with_context(&rewrite.context, &kctx);

            // The result should have type Foo (same as c0(c1(c2)))
            let expected_type = kctx.parse_type("Foo");
            assert_eq!(
                term_type,
                expected_type,
                "Backwards rewrite of c0(c1(c2)) should have type Foo. Term: {}. Context: {:?}",
                rewrite.term,
                rewrite.context.get_var_types()
            );
        }
    }

    #[test]
    fn test_type_variable_consistency() {
        // Test that rewrites are rejected when type variables would need inconsistent bindings.
        //
        // Pattern: g5(x0, x1, x2, x3) = x1(x2(x3))
        //   where x0: Type, x1: x0 -> x0, x2: x0 -> x0, x3: x0
        //
        // Query: g5(Foo, g0, g1, c0)
        //   where g0: Foo -> Foo, g1: Bar -> Bar, c0: Foo
        //
        // This should NOT match because:
        // - x1 matches g0 (type Foo -> Foo), inferring x0 = Foo
        // - x2 matches g1 (type Bar -> Bar), which would require x0 = Bar
        // - x0 cannot be both Foo and Bar

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");
        kctx.parse_datatype("Bar");
        kctx.parse_polymorphic_constant("g5", "T: Type", "(T -> T) -> (T -> T) -> T -> T");
        kctx.parse_constant("g0", "Foo -> Foo");
        kctx.parse_constant("g1", "Bar -> Bar");
        kctx.parse_constant("c0", "Foo");

        let mut tree = RewriteTree::new();

        // Pattern: g5(x0, x1, x2, x3) = x1(x2(x3))
        let pattern_clause = kctx.parse_clause(
            "g5(x0, x1, x2, x3) = x1(x2(x3))",
            &["Type", "x0 -> x0", "x0 -> x0", "x0"],
        );
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        // Query with type mismatch
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("g5(Foo, g0, g1, c0)");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // Should find NO rewrites because g1: Bar -> Bar doesn't match x0 -> x0 where x0 = Foo
        assert_eq!(
            rewrites.len(),
            0,
            "Should not find any rewrites when function types don't match"
        );
    }

    #[test]
    fn test_pdt_shared_key_different_contexts() {
        // This test reproduces the bug where multiple RewriteValues share the same PDT key
        // but have DIFFERENT output_contexts.
        //
        // The PDT stores ONE metadata context per key, which is used by `types_compatible`.
        // But each RewriteValue has its own output_context used by `build_bindings`.
        //
        // Bug scenario:
        // 1. Insert pattern 1: x0 -> f1(x0) where x0: Foo (ground type)
        // 2. Insert pattern 2: x0 -> f2(x1, x2, x0) where x0: Pair[x1, x2] (parameterized type)
        // 3. Both patterns have the same PDT key (just a variable input)
        // 4. PDT uses the FIRST context (x0: Foo) for types_compatible
        // 5. Query with term of type Foo - passes types_compatible
        // 6. But build_bindings for pattern 2 uses x0: Pair[x1, x2], causing type mismatch

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");
        kctx.parse_type_constructor("Pair", 2);
        // g0: Foo -> Foo (simple identity-like function)
        kctx.parse_constant("g0", "Foo -> Foo");
        // g1: (T: Type, U: Type) -> Pair[T, U] -> Pair[T, U] (polymorphic identity)
        kctx.parse_polymorphic_constant("g1", "T: Type, U: Type", "Pair[T, U] -> Pair[T, U]");
        kctx.parse_constant("c0", "Foo");

        let mut tree = RewriteTree::new();

        // Pattern 1: x0 -> g0(x0) where x0: Foo
        // This establishes the PDT metadata context with x0: Foo
        let pattern1_lctx = kctx.parse_local(&["Foo"]);
        let pattern1_input = Term::parse("x0");
        let pattern1_output = kctx.parse_term("g0(x0)");
        tree.insert_terms(
            0,
            &pattern1_input,
            &pattern1_output,
            false, // backwards
            &pattern1_lctx,
        );

        // Pattern 2: x0 -> g1(x1, x2, x0) where x0: Pair[x1, x2], x1: Type, x2: Type
        // This has the SAME PDT key (just variable x0) but DIFFERENT context
        let pattern2_lctx = kctx.parse_local(&["Pair[x1, x2]", "Type", "Type"]);
        let pattern2_input = Term::parse("x0");
        let pattern2_output = kctx.parse_term("g1(x1, x2, x0)");
        tree.insert_terms(
            0,
            &pattern2_input,
            &pattern2_output,
            false, // backwards
            &pattern2_lctx,
        );

        // Query: c0 (type Foo)
        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c0");
        let query_type = query_term.get_type_with_context(&query_lctx, &kctx);
        assert_eq!(query_type, kctx.parse_type("Foo"));

        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);

        // We should get exactly 1 rewrite: g0(c0)
        // Pattern 2 should NOT produce a rewrite because x0: Pair[x1, x2] doesn't match type Foo
        //
        // BUG: Pattern 2 may produce an invalid rewrite because:
        // - PDT uses pattern 1's context (x0: Foo) for types_compatible, which passes
        // - build_bindings uses pattern 2's context (x0: Pair[x1, x2]), causing mismatch

        // Verify all rewrites produce well-typed terms
        for rewrite in &rewrites {
            let output_type = rewrite.term.get_type_with_context(&rewrite.context, &kctx);
            assert_eq!(
                output_type,
                query_type,
                "Rewrite output type should match input type.\n\
                 Input: {} (type {})\n\
                 Output: {} (type {})\n\
                 Context: {:?}\n\
                 BUG: Pattern 2 was matched using pattern 1's context (x0: Foo) for PDT check,\n\
                 but build_bindings used pattern 2's context (x0: Pair[x1, x2]).",
                query_term,
                query_type,
                rewrite.term,
                output_type,
                rewrite.context.get_var_types()
            );
        }

        // Should have exactly 1 valid rewrite (from pattern 1 only)
        assert_eq!(
            rewrites.len(),
            1,
            "Should only get 1 rewrite from pattern 1. Pattern 2 should be rejected \
             because Foo is not Pair[T, U] for any T, U."
        );
    }

    #[test]
    fn test_rewrite_tree_typeclass_constraint() {
        // Test for the bug from reprove rat --line 330 with polymorphic,validate features.
        //
        // ROOT CAUSE INVESTIGATION:
        // The bug manifests when the type_store doesn't have typeclass instances registered.
        // In reprove, is_instance_of(GroundTypeId(5), TypeclassId(24)) returns false because
        // typeclass_instances[24] is EMPTY - the "instance Rat: Field" is not registered.
        //
        // The rewrite tree produces rewrites, and the Unifier validation catches that they're
        // invalid because the typeclass constraint isn't satisfied.
        //
        // This test verifies the CORRECT behavior when typeclass instances ARE registered:
        // - When Rat implements Field, backward rewrites for the inverse pattern should be valid.
        // - When Foo does NOT implement Field, backward rewrites should NOT be produced.

        let mut kctx = KernelContext::new();

        // Create Field typeclass
        kctx.parse_typeclass("Field");

        // Create ground types:
        // - Foo: does NOT implement Field
        // - Rat: DOES implement Field
        kctx.parse_datatype("Foo"); // does NOT implement Field
        kctx.parse_datatype("Rat").parse_instance("Rat", "Field"); // DOES implement Field

        // Create polymorphic function inv = Inverse.inverse[Field]: (F: Field) -> F -> F
        kctx.parse_polymorphic_constant("g0", "F: Field", "F -> F");

        // Create constants of each type
        kctx.parse_constant("c0", "Foo"); // constant of type Foo
        kctx.parse_constant("c1", "Rat"); // constant of type Rat

        let mut tree = RewriteTree::new();

        // Insert pattern: inv[F](inv[F](x)) = x
        // Pattern context: x0: Field (type parameter F), x1: x0 (value x of type F)
        let pattern_clause = kctx.parse_clause("g0(x0, g0(x0, x1)) = x1", &["Field", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        let query_lctx = kctx.parse_local(&[]);

        // Query with c0 (type Foo, which does NOT implement Field)
        // No backward rewrite should be returned because Foo doesn't implement Field
        let query_foo = kctx.parse_term("c0");
        let rewrites_foo = tree.get_rewrites(&query_foo, 0, &query_lctx, &kctx);
        let backward_rewrites_foo: Vec<_> = rewrites_foo.iter().filter(|r| !r.forwards).collect();

        // Query with c1 (type Rat, which DOES implement Field)
        // A backward rewrite should be returned and valid
        let query_rat = kctx.parse_term("c1");
        let rewrites_rat = tree.get_rewrites(&query_rat, 0, &query_lctx, &kctx);
        let backward_rewrites_rat: Vec<_> = rewrites_rat.iter().filter(|r| !r.forwards).collect();

        // Foo doesn't implement Field, so no backward rewrites should be produced
        assert!(
            backward_rewrites_foo.is_empty(),
            "Query c0 (type Foo) should NOT have backward rewrites because Foo does not implement Field. \
             Got {} backward rewrites.",
            backward_rewrites_foo.len()
        );

        // Rat implements Field, so backward rewrites should be produced
        assert!(
            !backward_rewrites_rat.is_empty(),
            "Query c1 (type Rat) SHOULD have backward rewrites because Rat implements Field"
        );

        // Validate the Rat rewrite using the Unifier
        use crate::kernel::literal::Literal;
        use crate::kernel::unifier::{Scope, Unifier};

        let rewrite = &backward_rewrites_rat[0];
        let (lit, flipped) = Literal::new_with_flip(true, rewrite.term.clone(), query_rat.clone());
        let pattern_lit = &pattern_clause.literals[0];

        let mut unifier = Unifier::new(3, &kctx);
        unifier.set_input_context(Scope::LEFT, pattern_clause.get_local_context());
        unifier.set_input_context(Scope::RIGHT, LocalContext::empty_ref());

        let unified = unifier.unify_literals(Scope::LEFT, pattern_lit, Scope::RIGHT, &lit, flipped);

        assert!(unified, "Unifier should validate the Rat rewrite as valid");
    }

    #[test]
    fn test_rewrite_tree_typeclass_constraint_accepts_constrained_type_var() {
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Add");
        kctx.parse_polymorphic_constant("g0", "A: Add", "A -> A");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Add", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        // Query-side type variable x0 is already constrained by Add, so the backwards
        // rewrite should remain available.
        let query_lctx = kctx.parse_local(&["Add", "x0"]);
        let query_term = Term::parse("x1");
        let rewrites = tree.get_rewrites(&query_term, 2, &query_lctx, &kctx);
        let backward_rewrites: Vec<_> = rewrites.iter().filter(|r| !r.forwards).collect();

        assert_eq!(
            backward_rewrites.len(),
            1,
            "Backwards rewrite should be allowed when the query type variable already \
             satisfies the required typeclass constraint."
        );
        assert_eq!(backward_rewrites[0].term, Term::parse("g0(x0, x1)"));
    }

    #[test]
    fn test_rewrite_tree_typeclass_constraint_rejects_parameterized_type_var() {
        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Add");
        kctx.parse_type_constructor("List", 1);
        kctx.parse_polymorphic_constant("g0", "A: Add", "A -> A");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Add", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        // Query-side value x1 has type List[T]. Even though List[T] is a type term,
        // it does not witness the Add constraint required by the rewrite rule.
        let query_lctx = kctx.parse_local(&["Type", "List[x0]"]);
        let query_term = Term::parse("x1");
        let rewrites = tree.get_rewrites(&query_term, 2, &query_lctx, &kctx);
        let backward_rewrites: Vec<_> = rewrites.iter().filter(|r| !r.forwards).collect();

        assert!(
            backward_rewrites.is_empty(),
            "Backwards rewrite should be rejected for parameterized type bindings like List[T] \
             that do not satisfy the required typeclass constraint. Got {} backward rewrites.",
            backward_rewrites.len()
        );
    }

    #[test]
    fn test_rewrite_tree_typeclass_inferred_binding_rejects_function_type() {
        // Regression test for inferred type variable bindings that violate typeclass constraints.
        //
        // Pattern: g1(x0, x1, x1) = x1
        //   where x0: Field (typeclass), x1: x0
        //
        // Backwards rewrite turns this into x1 -> g1(x0, x1, x1).
        // If we query with a term of function type (c0: Foo -> Foo),
        // we would infer x0 = Foo -> Foo, which should NOT satisfy Field.
        // The rewrite should be rejected.

        let mut kctx = KernelContext::new();
        kctx.parse_typeclass("Field");
        kctx.parse_datatype("Foo");

        // g1: (F: Field) -> F -> F -> F
        kctx.parse_polymorphic_constant("g1", "F: Field", "F -> F -> F");

        // c0: Foo -> Foo (function type, not a Field instance)
        kctx.parse_constant("c0", "Foo -> Foo");

        let mut tree = RewriteTree::new();
        let pattern_clause = kctx.parse_clause("g1(x0, x1, x1) = x1", &["Field", "x0"]);
        tree.insert_literal(
            0,
            &pattern_clause.literals[0],
            pattern_clause.get_local_context(),
        );

        let query_lctx = kctx.parse_local(&[]);
        let query_term = kctx.parse_term("c0");
        let rewrites = tree.get_rewrites(&query_term, 0, &query_lctx, &kctx);
        let backward_rewrites: Vec<_> = rewrites.iter().filter(|r| !r.forwards).collect();

        assert!(
            backward_rewrites.is_empty(),
            "Backwards rewrite should be rejected when inferred type binding violates \
             typeclass constraint. Got {} backward rewrites.",
            backward_rewrites.len()
        );
    }
}
