use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{Decomposition, Term, TermRef};
use crate::kernel::types::TypeclassId;

fn resolve_typeclass_constraint(type_term: TermRef, context: &LocalContext) -> Option<TypeclassId> {
    if let Some(tc_id) = type_term.as_typeclass() {
        return Some(tc_id);
    }
    let var_id = type_term.atomic_variable()?;
    let var_type = context.get_var_type(var_id as usize)?;
    resolve_typeclass_constraint(var_type.as_ref(), context)
}

fn typeclass_binding_is_compatible(
    actual_tc_id: TypeclassId,
    required_tc_id: TypeclassId,
    kernel_context: &KernelContext,
) -> bool {
    actual_tc_id == required_tc_id
        || kernel_context
            .type_store
            .typeclass_extends(actual_tc_id, required_tc_id)
}

fn type_term_satisfies_typeclass_constraint(
    type_term: TermRef,
    context: &LocalContext,
    kernel_context: &KernelContext,
    required_tc_id: TypeclassId,
) -> bool {
    if let Some(ground_id) = type_term.as_type_atom() {
        return kernel_context
            .type_store
            .is_instance_of(ground_id, required_tc_id);
    }

    let Some(var_id) = type_term.atomic_variable() else {
        return false;
    };
    let Some(var_type) = context.get_var_type(var_id as usize) else {
        return false;
    };
    let Some(actual_tc_id) = resolve_typeclass_constraint(var_type.as_ref(), context) else {
        return false;
    };
    typeclass_binding_is_compatible(actual_tc_id, required_tc_id, kernel_context)
}

// A VariableMap maintains a mapping from variables to terms, allowing us to turn a more general term
// into a more specific one by substituting variables.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct VariableMap {
    map: Vec<Option<Term>>,
}

impl VariableMap {
    pub fn new() -> VariableMap {
        VariableMap { map: Vec::new() }
    }

    /// Build a normalization variable map from var_ids.
    ///
    /// var_ids maps new sequential IDs to old IDs: var_ids[new] = old.
    /// The returned map maps old IDs to new IDs: old → FreeVariable(new).
    ///
    /// This captures the variable renumbering that happens during clause normalization.
    pub fn from_var_ids(var_ids: &[AtomId]) -> VariableMap {
        let mut map = VariableMap::new();
        for (new_id, &old_id) in var_ids.iter().enumerate() {
            map.set(old_id, Term::atom(Atom::FreeVariable(new_id as AtomId)));
        }
        map
    }

    /// Returns the maximum variable index in any of the mapped terms, or None if there are no variables.
    pub fn max_output_variable(&self) -> Option<AtomId> {
        let mut max: Option<AtomId> = None;
        for opt_term in &self.map {
            if let Some(term) = opt_term {
                if let Some(term_max) = term.max_variable() {
                    max = Some(match max {
                        None => term_max,
                        Some(current_max) => current_max.max(term_max),
                    });
                }
            }
        }
        max
    }

    /// Builds a LocalContext from all the variables in the replacement terms.
    /// We need the input_context to look up variable types.
    pub fn build_output_context(&self, input_context: &LocalContext) -> LocalContext {
        let mut output = LocalContext::empty();
        for opt_term in &self.map {
            if let Some(term) = opt_term {
                for (var_id, var_type) in term.collect_vars(input_context) {
                    output.set_type(var_id as usize, apply_to_term(var_type.as_ref(), self));
                }
            }
        }
        output
    }

    pub fn get_mapping(&self, i: AtomId) -> Option<&Term> {
        let i = i as usize;
        if i >= self.map.len() {
            None
        } else {
            self.map[i].as_ref()
        }
    }

    pub fn match_var(&mut self, var_id: AtomId, special_term: TermRef) -> bool {
        let var_id = var_id as usize;
        if var_id >= self.map.len() {
            self.map.resize(var_id + 1, None);
        }
        match &self.map[var_id] {
            None => {
                self.map[var_id] = Some(special_term.to_owned());
                true
            }
            Some(general_term) => general_term.as_ref() == special_term,
        }
    }

    fn match_atoms(&mut self, general: &Atom, special: &Atom) -> bool {
        if let Atom::FreeVariable(i) = general {
            self.match_var(*i, Term::atom(*special).as_ref())
        } else {
            general == special
        }
    }

    pub fn match_terms(
        &mut self,
        general: TermRef,
        special: TermRef,
        general_context: &LocalContext,
        special_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> bool {
        fn type_in_context(
            term: TermRef,
            context: &LocalContext,
            kernel_context: &KernelContext,
        ) -> Option<Term> {
            match term.decompose() {
                Decomposition::Atom(Atom::BoundVariable(i)) => {
                    let idx = context.len().checked_sub(*i as usize + 1)?;
                    context.get_var_type(idx).cloned()
                }
                _ => Some(term.get_type_with_context(context, kernel_context)),
            }
        }

        // Type checking is only needed when matching a variable to a term.
        // For other cases (atom vs atom, application vs application), if the
        // subterms match structurally, their types are guaranteed to match.
        match (general.decompose(), special.decompose()) {
            (Decomposition::Atom(Atom::FreeVariable(i)), _) => {
                // When matching a variable, we must verify type compatibility.
                // Get the variable's type directly from the context (cheap lookup)
                // rather than computing it via get_type_with_context.
                let var_type = general_context.get_var_type(*i as usize).unwrap();
                let Some(special_type) = type_in_context(special, special_context, kernel_context)
                else {
                    return false;
                };
                if var_type != &special_type {
                    return false;
                }
                if let Some(required_tc_id) =
                    resolve_typeclass_constraint(var_type.as_ref(), general_context)
                {
                    if !type_term_satisfies_typeclass_constraint(
                        special_type.as_ref(),
                        special_context,
                        kernel_context,
                        required_tc_id,
                    ) {
                        return false;
                    }
                }
                self.match_var(*i, special)
            }
            (Decomposition::Atom(g_atom), Decomposition::Atom(s_atom)) => {
                self.match_atoms(g_atom, s_atom)
            }
            (
                Decomposition::Application(g_func, g_arg),
                Decomposition::Application(s_func, s_arg),
            ) => {
                self.match_terms(
                    g_func,
                    s_func,
                    general_context,
                    special_context,
                    kernel_context,
                ) && self.match_terms(
                    g_arg,
                    s_arg,
                    general_context,
                    special_context,
                    kernel_context,
                )
            }
            (Decomposition::Lambda(g_input, g_body), Decomposition::Lambda(s_input, s_body)) => {
                if !self.match_terms(
                    g_input,
                    s_input,
                    general_context,
                    special_context,
                    kernel_context,
                ) {
                    return false;
                }

                let mut extended_general_context = general_context.clone();
                extended_general_context.push_type(g_input.to_owned());
                let mut extended_special_context = special_context.clone();
                extended_special_context.push_type(s_input.to_owned());

                self.match_terms(
                    g_body,
                    s_body,
                    &extended_general_context,
                    &extended_special_context,
                    kernel_context,
                )
            }
            (Decomposition::Pi(g_input, g_output), Decomposition::Pi(s_input, s_output)) => {
                if !self.match_terms(
                    g_input,
                    s_input,
                    general_context,
                    special_context,
                    kernel_context,
                ) {
                    return false;
                }

                let mut extended_general_context = general_context.clone();
                extended_general_context.push_type(g_input.to_owned());
                let mut extended_special_context = special_context.clone();
                extended_special_context.push_type(s_input.to_owned());

                self.match_terms(
                    g_output,
                    s_output,
                    &extended_general_context,
                    &extended_special_context,
                    kernel_context,
                )
            }
            (
                Decomposition::ForAll(g_binder_type, g_body),
                Decomposition::ForAll(s_binder_type, s_body),
            ) => {
                if !self.match_terms(
                    g_binder_type,
                    s_binder_type,
                    general_context,
                    special_context,
                    kernel_context,
                ) {
                    return false;
                }

                let mut extended_general_context = general_context.clone();
                extended_general_context.push_type(g_binder_type.to_owned());
                let mut extended_special_context = special_context.clone();
                extended_special_context.push_type(s_binder_type.to_owned());

                self.match_terms(
                    g_body,
                    s_body,
                    &extended_general_context,
                    &extended_special_context,
                    kernel_context,
                )
            }
            (
                Decomposition::Exists(g_binder_type, g_body),
                Decomposition::Exists(s_binder_type, s_body),
            ) => {
                if !self.match_terms(
                    g_binder_type,
                    s_binder_type,
                    general_context,
                    special_context,
                    kernel_context,
                ) {
                    return false;
                }

                let mut extended_general_context = general_context.clone();
                extended_general_context.push_type(g_binder_type.to_owned());
                let mut extended_special_context = special_context.clone();
                extended_special_context.push_type(s_binder_type.to_owned());

                self.match_terms(
                    g_body,
                    s_body,
                    &extended_general_context,
                    &extended_special_context,
                    kernel_context,
                )
            }
            // Atom vs Application mismatch
            _ => false,
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn get(&self, i: usize) -> Option<&Term> {
        self.map.get(i).and_then(|opt| opt.as_ref())
    }

    pub fn set(&mut self, i: AtomId, term: Term) {
        let i = i as usize;
        if i >= self.map.len() {
            self.map.resize(i + 1, None);
        }
        self.map[i] = Some(term);
    }

    pub fn has_mapping(&self, i: AtomId) -> bool {
        let i = i as usize;
        i < self.map.len() && self.map[i].is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &Term)> {
        self.map
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.as_ref().map(|term| (i, term)))
    }

    pub fn apply_to_all<F>(&mut self, mut f: F)
    where
        F: FnMut(&Term) -> Term,
    {
        for opt in &mut self.map {
            if let Some(term) = opt {
                *term = f(term);
            }
        }
    }

    pub fn push_none(&mut self) {
        self.map.push(None);
    }

    /// Compose this map with another.
    /// self maps: A vars → terms with B vars (B types in self_context)
    /// other maps: B vars → terms with C vars (C types in other_context)
    /// Result: A vars → terms with C vars
    ///
    /// This is used during proof reconstruction to compose:
    /// - premise_var_map (premise vars → output vars) with
    /// - conclusion_map (output vars → concrete terms)
    /// to get premise vars → concrete terms.
    pub fn compose(
        &self,
        self_context: &LocalContext,
        other: &VariableMap,
        other_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> VariableMap {
        let mut result = VariableMap::new();
        for (var_id, term) in self.iter() {
            let specialized =
                other.specialize_term(term.as_ref(), self_context, other_context, kernel_context);
            result.set(var_id as AtomId, specialized);
        }
        result
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    /// input_context is for the input term, output_context is for replacement terms in the map.
    fn specialize_term(
        &self,
        term: TermRef,
        input_context: &LocalContext,
        output_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        match term.decompose() {
            Decomposition::Atom(Atom::FreeVariable(i)) => {
                // Check if we have a mapping for this variable
                if let Some(replacement) = self.get_mapping(*i) {
                    replacement.clone()
                } else {
                    // Keep the variable as-is if unmapped
                    term.to_owned()
                }
            }
            Decomposition::Atom(_) => term.to_owned(),
            Decomposition::Application(func, arg) => {
                let specialized_func =
                    self.specialize_term(func, input_context, output_context, kernel_context);
                let specialized_arg =
                    self.specialize_term(arg, input_context, output_context, kernel_context);
                specialized_func.apply(&[specialized_arg])
            }
            Decomposition::Pi(input, output) => {
                let specialized_input =
                    self.specialize_term(input, input_context, output_context, kernel_context);
                let specialized_output =
                    self.specialize_term(output, input_context, output_context, kernel_context);
                Term::pi(specialized_input, specialized_output)
            }
            Decomposition::Lambda(input, body) => {
                let specialized_input =
                    self.specialize_term(input, input_context, output_context, kernel_context);
                let specialized_body =
                    self.specialize_term(body, input_context, output_context, kernel_context);
                Term::lambda(specialized_input, specialized_body)
            }
            Decomposition::ForAll(binder_type, body) => {
                let specialized_binder_type = self.specialize_term(
                    binder_type,
                    input_context,
                    output_context,
                    kernel_context,
                );
                let specialized_body =
                    self.specialize_term(body, input_context, output_context, kernel_context);
                Term::forall(specialized_binder_type, specialized_body)
            }
            Decomposition::Exists(binder_type, body) => {
                let specialized_binder_type = self.specialize_term(
                    binder_type,
                    input_context,
                    output_context,
                    kernel_context,
                );
                let specialized_body =
                    self.specialize_term(body, input_context, output_context, kernel_context);
                Term::exists(specialized_binder_type, specialized_body)
            }
        }
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    /// input_context is for the input literal, output_context is for replacement terms in the map.
    fn specialize_literal(
        &self,
        literal: &Literal,
        input_context: &LocalContext,
        output_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Literal {
        Literal::new(
            literal.positive,
            self.specialize_term(
                literal.left.as_ref(),
                input_context,
                output_context,
                kernel_context,
            ),
            self.specialize_term(
                literal.right.as_ref(),
                input_context,
                output_context,
                kernel_context,
            ),
        )
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    pub fn specialize_clause(&self, clause: &Clause, kernel_context: &KernelContext) -> Clause {
        let input_context = clause.get_local_context();
        // Build output context from replacement terms, then preserve unmapped input variables.
        // Unmapped variables stay in the specialized clause, so their types must remain available.
        let mut output_context = self.build_output_context(input_context);
        for i in 0..input_context.len() {
            if self.get_mapping(i as AtomId).is_none() {
                if let Some(var_type) = input_context.get_var_type(i) {
                    output_context.set_type(i, var_type.clone());
                }
            }
        }
        let literals = clause
            .literals
            .iter()
            .map(|lit| self.specialize_literal(lit, input_context, &output_context, kernel_context))
            .collect();
        Clause::from_literals_unnormalized(literals, &output_context)
    }

    /// Like `specialize_clause`, but compacts surviving free-variable IDs to remove gaps.
    ///
    /// This preserves literal shape and does not do full clause normalization; it only rewrites
    /// local-variable numbering so replay/display paths can compare structurally equivalent
    /// specialized clauses without depending on sparse variable IDs.
    pub fn specialize_clause_with_compact_vars(
        &self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Clause {
        self.specialize_clause(clause, kernel_context)
            .compacted_var_ids_preserving_literal_shape()
    }

    /// Like specialize_clause, but uses a separate context for looking up types in replacement terms.
    /// This is needed when the VariableMap's replacement terms were created with
    /// variables from a different context than the clause being specialized.
    pub fn specialize_clause_with_replacement_context(
        &self,
        clause: &Clause,
        replacement_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Clause {
        let input_context = clause.get_local_context();
        // Build output context from replacement terms
        let mut output_context = self.build_output_context(replacement_context);
        // Also need to include unmapped variables from the input clause
        // These keep their original types from the input context
        for i in 0..input_context.len() {
            if self.get_mapping(i as AtomId).is_none() {
                // This variable is unmapped, so it will remain in the output
                if let Some(var_type) = input_context.get_var_type(i) {
                    output_context.set_type(i, var_type.clone());
                }
            }
        }
        let literals = clause
            .literals
            .iter()
            .map(|lit| self.specialize_literal(lit, input_context, &output_context, kernel_context))
            .collect();
        Clause::from_literals_unnormalized(literals, &output_context)
    }

    /// Like `specialize_clause_with_replacement_context`, but compacts surviving free-variable
    /// IDs to remove gaps.
    ///
    /// This preserves literal shape and does not do full clause normalization.
    pub fn specialize_clause_with_replacement_context_and_compact_vars(
        &self,
        clause: &Clause,
        replacement_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Clause {
        self.specialize_clause_with_replacement_context(clause, replacement_context, kernel_context)
            .compacted_var_ids_preserving_literal_shape()
    }

    pub fn output_has_any_variable(&self) -> bool {
        for term in &self.map {
            if let Some(term) = term {
                if term.has_any_variable() {
                    return true;
                }
            }
        }
        false
    }

    /// One-way structural term matching without type checking.
    /// Matches `general` (with variables) against `special` (variables treated as constants).
    /// General's FreeVariables get bound; all other atoms are compared for equality.
    fn match_term_no_type_check(&mut self, general: TermRef, special: TermRef) -> bool {
        match (general.decompose(), special.decompose()) {
            (Decomposition::Atom(Atom::FreeVariable(i)), _) => self.match_var(*i, special),
            (Decomposition::Atom(g_atom), Decomposition::Atom(s_atom)) => g_atom == s_atom,
            (
                Decomposition::Application(g_func, g_arg),
                Decomposition::Application(s_func, s_arg),
            ) => {
                self.match_term_no_type_check(g_func, s_func)
                    && self.match_term_no_type_check(g_arg, s_arg)
            }
            (Decomposition::Pi(g_input, g_output), Decomposition::Pi(s_input, s_output))
            | (
                Decomposition::Lambda(g_input, g_output),
                Decomposition::Lambda(s_input, s_output),
            )
            | (
                Decomposition::ForAll(g_input, g_output),
                Decomposition::ForAll(s_input, s_output),
            )
            | (
                Decomposition::Exists(g_input, g_output),
                Decomposition::Exists(s_input, s_output),
            ) => {
                self.match_term_no_type_check(g_input, s_input)
                    && self.match_term_no_type_check(g_output, s_output)
            }
            _ => false,
        }
    }

    /// Match a general literal against a special literal for proof reconstruction.
    /// `flipped` swaps the general literal's left/right when matching.
    /// Returns true if match succeeds, updating this map with variable bindings.
    /// Type checking is not performed - callers should ensure type compatibility
    /// (e.g., via PDT's find_generalization).
    pub fn match_literal(&mut self, general: &Literal, special: &Literal, flipped: bool) -> bool {
        if general.is_signed_term() && special.is_signed_term() {
            // For signed boolean terms (x = true / x != true), only match the left sides
            self.match_term_no_type_check(general.left.as_ref(), special.left.as_ref())
        } else if flipped {
            self.match_term_no_type_check(general.left.as_ref(), special.right.as_ref())
                && self.match_term_no_type_check(general.right.as_ref(), special.left.as_ref())
        } else {
            self.match_term_no_type_check(general.left.as_ref(), special.left.as_ref())
                && self.match_term_no_type_check(general.right.as_ref(), special.right.as_ref())
        }
    }
}

/// Substitute variables in a term according to a map. Unmapped variables are kept as-is.
pub fn apply_to_term(term: TermRef, map: &VariableMap) -> Term {
    match term.decompose() {
        Decomposition::Atom(Atom::FreeVariable(i)) => map
            .get_mapping(*i)
            .cloned()
            .unwrap_or_else(|| term.to_owned()),
        Decomposition::Atom(_) => term.to_owned(),
        Decomposition::Application(func, arg) => {
            let new_func = apply_to_term(func, map);
            let new_arg = apply_to_term(arg, map);
            new_func.apply(&[new_arg])
        }
        Decomposition::Pi(input, output) => {
            let new_input = apply_to_term(input, map);
            let new_output = apply_to_term(output, map);
            Term::pi(new_input, new_output)
        }
        Decomposition::Lambda(input, body) => {
            let new_input = apply_to_term(input, map);
            let new_body = apply_to_term(body, map);
            Term::lambda(new_input, new_body)
        }
        Decomposition::ForAll(binder_type, body) => {
            let new_binder_type = apply_to_term(binder_type, map);
            let new_body = apply_to_term(body, map);
            Term::forall(new_binder_type, new_body)
        }
        Decomposition::Exists(binder_type, body) => {
            let new_binder_type = apply_to_term(binder_type, map);
            let new_body = apply_to_term(body, map);
            Term::exists(new_binder_type, new_body)
        }
    }
}

impl fmt::Display for VariableMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let mut first = true;
        for (i, term) in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "x{} -> {}", i, term)?;
            first = false;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::literal::Literal;

    #[test]
    fn test_specialize_clause_with_compact_vars_removes_gaps() {
        let kernel_context = KernelContext::new();
        let clause = Clause::from_literals_unnormalized(
            vec![
                Literal::positive(Term::new_variable(0)),
                Literal::positive(Term::new_variable(2)),
            ],
            &LocalContext::from_types(vec![
                Term::bool_type(),
                Term::bool_type(),
                Term::bool_type(),
            ]),
        );

        let specialized =
            VariableMap::new().specialize_clause_with_compact_vars(&clause, &kernel_context);

        assert_eq!(specialized.get_local_context().len(), 2);
        assert!(specialized
            .literals
            .iter()
            .any(|lit| lit.left == Term::new_variable(0)));
        assert!(specialized
            .literals
            .iter()
            .any(|lit| lit.left == Term::new_variable(1)));
    }

    #[test]
    fn test_match_terms_with_lambda_bound_variable_does_not_panic() {
        let kctx = KernelContext::new();
        let general_context = LocalContext::from_types(vec![Term::bool_type()]);
        let special_context = LocalContext::empty();

        let general = Term::lambda(Term::bool_type(), Term::atom(Atom::FreeVariable(0)));
        let special = Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0)));

        let mut var_map = VariableMap::new();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            var_map.match_terms(
                general.as_ref(),
                special.as_ref(),
                &general_context,
                &special_context,
                &kctx,
            )
        }));

        assert!(result.is_ok(), "match_terms should not panic under binders");
        assert!(
            result.unwrap(),
            "lambda pattern should match lambda with bound body"
        );
        assert_eq!(
            var_map.get_mapping(0),
            Some(&Term::atom(Atom::BoundVariable(0)))
        );
    }
}
