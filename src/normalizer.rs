use std::collections::HashMap;
use std::sync::Arc;

use crate::builder::BuildError;
use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::ConstantInstance;
use crate::elaborator::acorn_value::{AcornValue, BinaryOp};
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::elaborator::synthetic::{SyntheticDefinition, SyntheticRegistry};
use crate::kernel::atom::{Atom, AtomId, INVALID_SYNTHETIC_MODULE};
use crate::kernel::clause::Clause;
use crate::kernel::cnf::Cnf;
use crate::kernel::extended_term::ExtendedTerm;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::module::ModuleId;
use crate::proof_step::{ProofStep, Truthiness};
use tracing::trace;

/// A fact that has been normalized into proof steps.
#[derive(Clone)]
pub struct NormalizedFact {
    pub steps: Vec<ProofStep>,
}

/// A goal that has been normalized into proof steps.
/// Includes the normalizer state after normalizing this goal.
#[derive(Clone)]
pub struct NormalizedGoal {
    pub goal: Goal,
    pub steps: Vec<ProofStep>,
    /// The normalizer state after normalizing this goal (with negated goal added).
    pub normalizer: Normalizer,
}

#[derive(Clone)]
pub struct Normalizer {
    /// Registry for synthetic atom definitions.
    synthetic_registry: SyntheticRegistry,

    /// The kernel context containing TypeStore and SymbolTable.
    kernel_context: KernelContext,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            synthetic_registry: SyntheticRegistry::new(),
            kernel_context: KernelContext::new(),
        }
    }

    pub fn get_synthetic_type(&self, module_id: ModuleId, local_id: AtomId) -> AcornType {
        let symbol = Symbol::Synthetic(module_id, local_id);
        let type_term = self.kernel_context.symbol_table.get_type(symbol);
        self.kernel_context
            .type_store
            .type_term_to_acorn_type(type_term)
    }

    /// Returns all synthetic atom IDs that have been defined.
    #[cfg(test)]
    pub fn get_synthetic_ids(&self) -> Vec<(ModuleId, AtomId)> {
        self.synthetic_registry.get_ids()
    }

    pub fn kernel_context(&self) -> &KernelContext {
        &self.kernel_context
    }

    pub fn kernel_context_mut(&mut self) -> &mut KernelContext {
        &mut self.kernel_context
    }

    /// Registers an arbitrary type with the type store.
    /// This is needed for certificate checking where type parameters defined
    /// in a let...satisfy statement need to be available for subsequent steps.
    pub fn register_arbitrary_type(&mut self, param: &TypeParam) {
        let arb_type = AcornType::Arbitrary(param.clone());
        self.kernel_context.type_store.add_type(&arb_type);

        // If the type param has a typeclass constraint, ensure the typeclass is registered.
        if let Some(typeclass) = &param.typeclass {
            self.kernel_context.type_store.add_typeclass(typeclass);
        }
    }

    /// Gets a synthetic definition for a value, if one exists.
    /// The value should be of the form "exists ___ (forall x and forall y and ...)".
    /// The type_var_map is used for polymorphic normalization.
    pub fn get_synthetic_definition(
        &self,
        value: &AcornValue,
        type_var_map: Option<&HashMap<String, (AtomId, Term)>>,
    ) -> Option<&Arc<SyntheticDefinition>> {
        let (num_definitions, alt_value, quant_types) = match value {
            AcornValue::Exists(quants, subvalue) => (
                quants.len(),
                AcornValue::ForAll(quants.clone(), subvalue.clone()),
                quants.clone(),
            ),
            _ => (0, value.clone(), vec![]),
        };

        let mut view = NormalizationContext::new_ref(self, type_var_map.cloned());
        let Ok(uninstantiated) = view.value_to_denormalized_clauses(&alt_value) else {
            return None;
        };

        // Skip the type variables when replacing existentials
        let num_type_vars = type_var_map.map_or(0, |m| m.len());

        // Convert quantifier types to type terms, including polymorphic wrapper if applicable
        // Get type variable kinds in sorted order (same as make_skolem_terms)
        let type_var_kinds: Vec<Term> = if let Some(tvm) = type_var_map {
            let mut entries: Vec<_> = tvm.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            entries.iter().map(|(_, kind)| kind.clone()).collect()
        } else {
            vec![]
        };

        let num_type_params = type_var_kinds.len() as u16;
        let synthetic_types: Vec<Term> = quant_types
            .iter()
            .map(|t| {
                // First convert the base type
                let mut type_term = self
                    .kernel_context
                    .type_store
                    .to_type_term_with_vars(t, type_var_map);
                // Convert FreeVariables to BoundVariables (same as make_skolem_terms)
                type_term = type_term.convert_free_to_bound(num_type_params);
                // Wrap with Pi types for each type variable
                for kind in type_var_kinds.iter().rev() {
                    type_term = Term::pi(kind.clone(), type_term);
                }
                type_term
            })
            .collect();

        let clauses: Vec<Clause> = uninstantiated
            .iter()
            .map(|c| c.instantiate_invalid_synthetics_with_skip(num_definitions, num_type_vars))
            .collect();

        self.synthetic_registry
            .lookup_by_key(&type_var_kinds, &synthetic_types, &clauses)
    }

    /// Declare a synthetic atom with a type already in Term form.
    /// This avoids round-trip conversion through AcornType.
    fn declare_synthetic_atom_with_type_term(
        &mut self,
        module_id: ModuleId,
        type_term: Term,
    ) -> Result<(ModuleId, AtomId), String> {
        let symbol = self
            .kernel_context
            .symbol_table
            .declare_synthetic(module_id, type_term);
        let (m, id) = match symbol {
            Symbol::Synthetic(m, id) => (m, id),
            _ => panic!("declare_synthetic should return a Synthetic symbol"),
        };
        // Check for invalid synthetic module (shouldn't happen in normal use)
        if m == INVALID_SYNTHETIC_MODULE {
            return Err("synthetic atom created with invalid module".to_string());
        }
        Ok((m, id))
    }

    /// Adds the definition for these synthetic atoms.
    fn define_synthetic_atoms(
        &mut self,
        atoms: Vec<(ModuleId, AtomId)>,
        type_vars: Vec<Term>,
        synthetic_types: Vec<Term>,
        clauses: Vec<Clause>,
        source: Option<Source>,
    ) -> Result<(), String> {
        for (i, atom) in atoms.iter().enumerate() {
            trace!(
                atom_id = ?atom,
                source = ?source,
                clause_index = i,
                "defining synthetic atom"
            );
        }
        for clause in &clauses {
            trace!(clause = %clause, "synthetic definition clause");
        }

        // In the synthetic key, we normalize synthetic ids by renumbering them.
        // Use pinned normalization to preserve type variable ordering.
        let num_type_vars = type_vars.len();
        let key_clauses: Vec<Clause> = clauses
            .iter()
            .map(|c| c.invalidate_synthetics_with_pinned(&atoms, num_type_vars))
            .collect();

        self.synthetic_registry.define(
            atoms,
            type_vars,
            synthetic_types,
            clauses,
            key_clauses,
            source,
        )
    }

    pub fn add_scoped_constant(
        &mut self,
        cname: ConstantName,
        acorn_type: &AcornType,
        type_var_map: Option<&HashMap<String, (AtomId, Term)>>,
    ) -> Atom {
        let type_term = self
            .kernel_context
            .type_store
            .to_type_term_with_vars(acorn_type, type_var_map);
        Atom::Symbol(self.kernel_context.symbol_table.add_constant(
            cname,
            NewConstantType::Local,
            type_term,
        ))
    }

    /// Merges another Normalizer into this one.
    /// Used to combine prenormalized state from dependencies.
    pub fn merge(&mut self, other: &Normalizer) {
        self.kernel_context.merge(&other.kernel_context);
        self.synthetic_registry.merge(&other.synthetic_registry);
    }

    /// Merges another Normalizer into this one, excluding scoped constants.
    /// This is intended for merging import state only.
    pub fn merge_imports(&mut self, other: &Normalizer) {
        self.kernel_context.merge_imports(&other.kernel_context);
        self.synthetic_registry.merge(&other.synthetic_registry);
    }
}

// Represents a binding for a variable on the stack during normalization.
// Each binding corresponds to a variable in the output clause.
enum TermBinding {
    Bound(Term),
    Free(Term),
}

impl TermBinding {
    /// Get the underlying term regardless of binding type
    fn term(&self) -> &Term {
        match self {
            TermBinding::Bound(t) | TermBinding::Free(t) => t,
        }
    }
}

/// Inner enum for NormalizationContext to support both ref and mut access to the Normalizer.
enum NormalizerRef<'a> {
    Ref(&'a Normalizer),
    Mut(&'a mut Normalizer),
}

/// A NormalizationContext holds state for a single normalization operation.
/// It combines a reference to the Normalizer with operation-scoped state like type_var_map.
/// This lets us share methods between mutable and non-mutable normalizer access while
/// keeping per-operation state separate from the persistent Normalizer state.
pub struct NormalizationContext<'a> {
    inner: NormalizerRef<'a>,
    /// Type variable mapping for polymorphic normalization.
    /// Maps type parameter names to (variable id, kind).
    /// This is set for the duration of normalizing a single polymorphic fact/goal.
    type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    /// The module ID for which we're normalizing. Synthetics created during
    /// normalization will be scoped to this module.
    module_id: ModuleId,
}

impl<'a> NormalizationContext<'a> {
    /// Create a new NormalizationContext with immutable access.
    /// Uses ModuleId(0) as a placeholder since immutable contexts don't create synthetics.
    pub fn new_ref(
        n: &'a Normalizer,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Self {
        NormalizationContext {
            inner: NormalizerRef::Ref(n),
            type_var_map,
            module_id: ModuleId(0),
        }
    }

    /// Create a new NormalizationContext with mutable access.
    /// The module_id determines which module synthetics will be scoped to.
    pub fn new_mut(
        n: &'a mut Normalizer,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
        module_id: ModuleId,
    ) -> Self {
        NormalizationContext {
            inner: NormalizerRef::Mut(n),
            type_var_map,
            module_id,
        }
    }

    fn as_ref(&self) -> &Normalizer {
        match &self.inner {
            NormalizerRef::Ref(n) => n,
            NormalizerRef::Mut(n) => n,
        }
    }

    fn as_mut(&mut self) -> Result<&mut Normalizer, String> {
        match &mut self.inner {
            NormalizerRef::Ref(_) => Err("Cannot mutate a NormalizationContext::Ref".to_string()),
            NormalizerRef::Mut(n) => Ok(n),
        }
    }

    fn module_id(&self) -> ModuleId {
        self.module_id
    }

    fn symbol_table(&self) -> &crate::kernel::symbol_table::SymbolTable {
        &self.as_ref().kernel_context.symbol_table
    }

    fn type_store(&self) -> &crate::kernel::type_store::TypeStore {
        &self.as_ref().kernel_context.type_store
    }

    fn kernel_context(&self) -> &KernelContext {
        &self.as_ref().kernel_context
    }

    /// Get the type variable map for polymorphic normalization.
    /// Maps type parameter names to (variable id, kind).
    /// In non-polymorphic mode, this always returns None.
    fn type_var_map(&self) -> Option<&HashMap<String, (AtomId, Term)>> {
        self.type_var_map.as_ref()
    }

    /// Get the kinds of type variables in sorted order by their IDs.
    /// Returns the types (e.g., Type) that each type variable has.
    /// Empty in non-polymorphic mode.
    fn get_type_var_kinds(&self) -> Vec<Term> {
        if let Some(type_var_map) = &self.type_var_map {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            entries.iter().map(|(_, kind)| kind.clone()).collect()
        } else {
            vec![]
        }
    }

    /// Get a mapping from variable IDs to type parameter names.
    /// This is used for denormalization to convert type variables back to named type params.
    fn get_var_id_to_name_map(&self) -> HashMap<AtomId, String> {
        if let Some(ref type_var_map) = self.type_var_map {
            return type_var_map
                .iter()
                .map(|(name, (id, _))| (*id, name.clone()))
                .collect();
        }
        HashMap::new()
    }

    /// Wrapper around value_to_cnf.
    /// Note that this only works on values that have already been "cleaned up" to some extent.
    ///
    /// This function checks for invalid conversions where variables are dropped:
    /// - Exists skolems that don't appear in clauses (would assert existence over empty type)
    /// - Forall variables that don't appear in clauses (would lose vacuous truth condition)
    pub fn nice_value_to_clauses(
        &mut self,
        value: &AcornValue,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
    ) -> Result<Vec<Clause>, String> {
        match value {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let mut left_clauses = self.nice_value_to_clauses(left, synthesized)?;
                let right_clauses = self.nice_value_to_clauses(right, synthesized)?;
                left_clauses.extend(right_clauses);
                Ok(left_clauses)
            }
            _ => {
                let mut stack = vec![];
                let mut local_context = LocalContext::empty();

                // In polymorphic mode, pre-allocate space for type variables
                let (mut next_var_id, num_type_params) =
                    if let Some(type_var_map) = self.type_var_map() {
                        // Pre-populate local_context with the type of each type variable.
                        // The type is either TypeSort (unconstrained) or Typeclass (constrained).
                        // We need to iterate in order of variable ID.
                        let mut entries: Vec<_> = type_var_map.values().collect();
                        entries.sort_by_key(|(id, _)| *id);
                        for (_, var_type) in entries {
                            local_context.push_type(var_type.clone());
                        }
                        (type_var_map.len() as AtomId, type_var_map.len())
                    } else {
                        (0, 0)
                    };

                let cnf = self.value_to_cnf(
                    &value,
                    false,
                    &mut stack,
                    &mut next_var_id,
                    synthesized,
                    &mut local_context,
                )?;
                // Pin type variables so their ordering is preserved when clauses are normalized.
                // This ensures function types like G -> H don't get swapped to H -> G.
                let clauses = cnf.into_clauses_with_pinned(&local_context, num_type_params);

                // Check for dropped variables that would lose inhabitedness information.
                // Both checks look for variables that don't appear in the resulting clauses
                // but whose type might be empty.

                // Existential witnesses: asserting existence over a potentially empty type is unsound.
                if self.has_uninhabited_existential_witness(synthesized, &clauses) {
                    return Err("exists over a potentially uninhabited type".to_string());
                }

                // Forall variables: if dropped, the statement is vacuously true when the
                // type is empty. Return empty clauses since we can't represent this properly.
                if self.has_uninhabited_dropped_variable(&local_context, &clauses, num_type_params)
                {
                    return Ok(vec![]);
                }

                Ok(clauses)
            }
        }
    }

    /// Checks if any forall variables dropped during normalization have uninhabited types.
    /// This is specifically for detecting vacuous quantification over unconstrained type parameters.
    ///
    /// For example, `forall(x: T) { P }` where T is an unconstrained type parameter and x
    /// doesn't appear in P. If T is empty, this is vacuously true; if T is inhabited, it's
    /// equivalent to P. We can't represent this ambiguity in CNF, so we return empty clauses.
    fn has_uninhabited_dropped_variable(
        &self,
        original_context: &LocalContext,
        clauses: &[Clause],
        skip_vars: usize,
    ) -> bool {
        use std::collections::HashSet;

        // Collect all types that appear in ANY clause's context.
        let mut all_clause_types: HashSet<&Term> = HashSet::new();
        for clause in clauses {
            let clause_ctx = clause.get_local_context();
            for i in 0..clause_ctx.len() {
                if let Some(var_type) = clause_ctx.get_var_type(i) {
                    all_clause_types.insert(var_type);
                }
            }
        }

        // Build a context for the type parameters (first skip_vars entries)
        let mut type_param_context = LocalContext::empty();
        for i in 0..skip_vars {
            if let Some(t) = original_context.get_var_type(i) {
                type_param_context.push_type(t.clone());
            }
        }

        // Check each variable type in the original context, skipping type parameters
        for var_id in skip_vars..original_context.len() {
            if let Some(var_type) = original_context.get_var_type(var_id) {
                // If this type doesn't appear in ANY clause context, variables of this type were dropped
                if !all_clause_types.contains(var_type) {
                    // Check if this type is provably inhabited
                    if !self
                        .kernel_context()
                        .provably_inhabited(var_type, Some(&type_param_context))
                    {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Checks if any existential witnesses were created for uninhabited types.
    /// This prevents unsound definitions where we assert existence over empty types.
    /// For example: `let inhabited[T]: Bool = exists(x: T) { true }` would create a witness
    /// for type T, but T might be empty, making the exists claim invalid.
    ///
    /// This function only checks witnesses that don't appear in any clause. The rationale is:
    /// - If a witness IS used in clauses (like `exists(x: T) { P(x) }`), then the clause P(x)
    ///   provides some constraint on the witness, and we allow it.
    /// - If a witness is NOT used (like `exists(x: T) { true }`), we're purely asserting
    ///   inhabitedness of T with no justification, which is unsound if T is empty.
    ///
    /// Note: The `synthesized` list includes all synthetics (existential witnesses, Tseitin
    /// abbreviations, etc.), but the "unused" filter effectively isolates the problematic
    /// existential cases since definition-style synthetics are always used in their defining clauses.
    fn has_uninhabited_existential_witness(
        &self,
        synthesized: &[(ModuleId, AtomId)],
        clauses: &[Clause],
    ) -> bool {
        use std::collections::HashSet;

        // Collect all synthetic atoms that appear in any clause
        let mut used_synthetics: HashSet<(ModuleId, AtomId)> = HashSet::new();
        for clause in clauses {
            for lit in &clause.literals {
                for atom in lit.left.iter_atoms() {
                    if let &Atom::Symbol(Symbol::Synthetic(m, id)) = atom {
                        used_synthetics.insert((m, id));
                    }
                }
                for atom in lit.right.iter_atoms() {
                    if let &Atom::Symbol(Symbol::Synthetic(m, id)) = atom {
                        used_synthetics.insert((m, id));
                    }
                }
            }
        }

        // Check each synthesized atom
        for &(module_id, local_id) in synthesized {
            // If this synthetic appears in clauses, it's constrained by something, so skip
            if used_synthetics.contains(&(module_id, local_id)) {
                continue;
            }

            // Get the synthetic's type
            let synth_type = self
                .kernel_context()
                .symbol_table
                .get_type(Symbol::Synthetic(module_id, local_id));

            // Get the result type by stripping off type parameter Pis only.
            // Type parameter Pis have TypeSort (or Typeclass) as the input type.
            // For example, a witness with type Pi(Type, b0) represents
            // "for any type T, return a value of type T".
            // We DON'T strip function type Pis like Pi(Nat, Bool) because those
            // represent function types, not type parameters.
            let mut result_type = synth_type.as_ref();
            let mut stripped_types = Vec::new();
            while let Some((input_type, body)) = result_type.split_pi() {
                // Only strip if this is a type parameter (input is Type/TypeSort or Typeclass)
                if !input_type.is_type_param_kind() {
                    break;
                }
                stripped_types.push(input_type.to_owned());
                result_type = body;
            }

            // Build context with types in reverse order (innermost first) to match de Bruijn indices
            let mut type_param_context = LocalContext::empty();
            for t in stripped_types.into_iter().rev() {
                type_param_context.push_type(t);
            }

            // The result term keeps its original bound variable indices
            let result_term = result_type.to_owned();

            let is_inhabited = self
                .kernel_context()
                .provably_inhabited(&result_term, Some(&type_param_context));
            if !is_inhabited {
                return true;
            }
        }

        false
    }

    /// This returns clauses that are denormalized in the sense that they sort literals,
    /// but don't filter out redundant or tautological literals.
    /// This is the format that the Checker uses.
    /// If you call normalize() on the clause afterwards, you should get the normalized one.
    pub fn value_to_denormalized_clauses(
        &mut self,
        value: &AcornValue,
    ) -> Result<Vec<Clause>, String> {
        let mut output = vec![];
        let mut context = LocalContext::empty();

        // In polymorphic mode, pre-allocate space for type variables
        // This ensures value variable IDs don't collide with type variable IDs
        let mut next_var_id = if let Some(type_var_map) = self.type_var_map() {
            // Pre-populate local_context with the type of each type variable.
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (_, var_type) in entries {
                context.push_type(var_type.clone());
            }
            type_var_map.len() as AtomId
        } else {
            0
        };

        let cnf = self.value_to_cnf(
            &value,
            false,
            &mut vec![],
            &mut next_var_id,
            &mut vec![],
            &mut context,
        )?;
        for mut literals in cnf.into_iter() {
            literals.sort();
            output.push(Clause::from_literals_unnormalized(literals, &context));
        }
        Ok(output)
    }

    /// Converts the value into a list of lists of literals, adding skolem constants
    /// to the normalizer as needed.
    /// True is [], false is [[]]. This is logical if you think hard about it.
    /// We leave general tautologies in here, and don't normalize until we convert to Clause.
    ///
    /// The variable numbering in the input and output is different.
    /// x_i in the input gets mapped to stack[i] in the output.
    /// This method must reset the stack before returning.
    ///
    /// Forall variables map into variables, but they may get renumbered, because the AcornValue
    /// a variable id can be used multiple times in different branches. In the output, variables
    /// in different branches may be combined. So each universal variable, anywhere in the value,
    /// gets a unique id.
    ///
    /// Existential variables turn into skolem terms. These are declared in the normalizer
    /// but not yet defined, because this function is creating the definition.
    /// Whenever we create a new skolem term, we add it to the synthesized list.
    fn value_to_cnf(
        &mut self,
        value: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        match value {
            AcornValue::ForAll(qs, sub) => {
                if !negate {
                    self.forall_to_cnf(qs, sub, false, stack, next_var_id, synth, context)
                } else {
                    self.exists_to_cnf(qs, sub, true, stack, next_var_id, synth, context)
                }
            }
            AcornValue::Exists(qs, sub) => {
                if !negate {
                    self.exists_to_cnf(qs, sub, false, stack, next_var_id, synth, context)
                } else {
                    self.forall_to_cnf(qs, sub, true, stack, next_var_id, synth, context)
                }
            }
            AcornValue::Binary(BinaryOp::And, left, right) => {
                if !negate {
                    self.and_to_cnf(
                        left,
                        right,
                        false,
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                } else {
                    self.or_to_cnf(left, right, true, true, stack, next_var_id, synth, context)
                }
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                if !negate {
                    self.or_to_cnf(
                        left,
                        right,
                        false,
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                } else {
                    self.and_to_cnf(left, right, true, true, stack, next_var_id, synth, context)
                }
            }
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                if !negate {
                    self.or_to_cnf(left, right, true, false, stack, next_var_id, synth, context)
                } else {
                    self.and_to_cnf(left, right, false, true, stack, next_var_id, synth, context)
                }
            }
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                self.eq_to_cnf(left, right, negate, stack, next_var_id, synth, context)
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                self.eq_to_cnf(left, right, !negate, stack, next_var_id, synth, context)
            }
            AcornValue::Not(subvalue) => {
                self.value_to_cnf(subvalue, !negate, stack, next_var_id, synth, context)
            }
            AcornValue::Try(_, _) => Err("try operator not yet implemented".to_string()),
            AcornValue::Bool(value) => {
                if *value ^ negate {
                    Ok(Cnf::true_value())
                } else {
                    Ok(Cnf::false_value())
                }
            }
            AcornValue::IfThenElse(cond_value, then_value, else_value) => {
                let cond_cnf =
                    self.value_to_cnf(cond_value, false, stack, next_var_id, synth, context)?;
                let Some(cond_lit) = cond_cnf.to_literal() else {
                    return Err("value 'if' condition is too complicated".to_string());
                };
                let then_cnf =
                    self.value_to_cnf(then_value, negate, stack, next_var_id, synth, context)?;
                let else_cnf =
                    self.value_to_cnf(else_value, negate, stack, next_var_id, synth, context)?;
                Ok(Cnf::cnf_if(cond_lit, then_cnf, else_cnf))
            }
            AcornValue::Application(app) => {
                let mut arg_exts = vec![];
                for arg in &app.args {
                    arg_exts.push(self.arg_to_extended_term(
                        arg,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?);
                }
                self.apply_to_cnf(
                    &app.function,
                    arg_exts,
                    negate,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )
            }
            AcornValue::Variable(..) | AcornValue::Constant(..) | AcornValue::Lambda(..) => {
                let term = self
                    .value_to_extended_term(value, stack, next_var_id, synth, context)?
                    .to_term()?;
                let literal = Literal::from_signed_term(term, !negate);
                Ok(Cnf::from_literal(literal))
            }
            AcornValue::Match(..) => Err("match in unexpected position".to_string()),
        }
    }

    fn apply_to_cnf(
        &mut self,
        function: &AcornValue,
        args: Vec<ExtendedTerm>,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        if let AcornValue::Lambda(_, return_value) = function {
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(arg.to_term()?);
            }
            let num_args = arg_terms.len();
            // Lambda arguments are bound variables
            for arg in arg_terms {
                stack.push(TermBinding::Bound(arg));
            }
            let answer = self.value_to_cnf(
                &return_value,
                negate,
                stack,
                next_var_id,
                synthesized,
                context,
            );
            stack.truncate(stack.len() - num_args);
            return answer;
        }

        // Fall back to converting via extended term
        let extended =
            self.apply_to_extended_term(function, args, stack, next_var_id, synthesized, context)?;
        match extended {
            ExtendedTerm::Term(term) => {
                let literal = Literal::from_signed_term(term, !negate);
                Ok(Cnf::from_literal(literal))
            }
            _ => Err("unhandled case: non-term application".to_string()),
        }
    }

    // Convert a "forall" node in a value, or the equivalent, to CNF.
    // negate is whether to negate the subvalue.
    fn forall_to_cnf(
        &mut self,
        quants: &Vec<AcornType>,
        subvalue: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        for quant in quants {
            let type_term = self
                .type_store()
                .to_type_term_with_vars(quant, self.type_var_map());
            let var_id = *next_var_id;
            context.push_type(type_term);
            let var = Term::new_variable(var_id);
            *next_var_id += 1;
            stack.push(TermBinding::Free(var));
        }
        let result =
            self.value_to_cnf(subvalue, negate, stack, next_var_id, synthesized, context)?;
        for _ in quants {
            stack.pop();
        }
        Ok(result)
    }

    // Define skolem functions that take the free variables on the stack as arguments.
    // One skolem function is created for each type in skolem_types.
    // Returns terms representing the applied skolem functions.
    fn make_skolem_terms(
        &mut self,
        skolem_types: &[AcornType],
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Vec<Term>, String> {
        let mut args = vec![];
        // Keep arg_type_terms as Terms to avoid round-trip conversion
        let mut arg_type_terms: Vec<Term> = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        // In polymorphic mode, synthetics are polymorphic constants.
        // Type variables appear in the term, and TypeSort appears in the type.
        // This is the same pattern as other polymorphic constants: the type is
        // Pi(Type, Pi(Type, ... actual_type ...)) where each Type is skipped when
        // converting to AcornType, giving the user-facing type without type params.
        if let Some(type_var_map) = self.type_var_map() {
            // Sort entries by var_id to ensure consistent ordering
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (var_id, var_type) in entries {
                let var_term = Term::new_variable(*var_id);
                args.push(var_term);
                // Type variables have their kind (Type or typeclass) as their type in the Pi
                arg_type_terms.push(var_type.clone());
                seen_vars.insert(*var_id);
            }
        }

        for binding in stack.iter() {
            // Use collect_vars with the context to get variable types
            for (var_id, closed_type) in binding.term().collect_vars(context) {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(var_id);
                    args.push(var_term);
                    // Keep types as Terms - no conversion needed
                    arg_type_terms.push(closed_type);
                }
            }
        }

        // Convert FreeVariables in value argument types to BoundVariables.
        // Type parameter kinds (TypeSort/Typeclass) don't need conversion.
        // In non-polymorphic mode, num_type_params is 0 so conversion is a no-op.
        //
        // Each arg type is converted at a depth that accounts for how many OTHER
        // non-type-param arg Pis will enclose it in the final type structure.
        // For arg at position i (0-indexed among non-type-param args), depth = i.
        let num_type_params = self.type_var_map().map_or(0, |m| m.len()) as u16;
        let mut non_type_param_index = 0u16;
        let arg_type_terms: Vec<Term> = arg_type_terms
            .into_iter()
            .map(|t| {
                if t.as_ref().is_type_param_kind() {
                    t // Type parameter kinds don't need conversion
                } else {
                    let depth = non_type_param_index;
                    non_type_param_index += 1;
                    t.convert_free_to_bound_with_depth(num_type_params, depth)
                }
            })
            .collect();

        let mut output = vec![];
        for t in skolem_types {
            // Each existential quantifier needs a new skolem atom.
            // The skolem term is that atom applied to the free variables on the stack.

            // Convert the result type to a Term.
            // to_type_term_with_vars creates FreeVariable(i) for type parameter i,
            // but inside the Pi type, these should be BoundVariable(n-1-i).
            // The result will be wrapped inside (arg_type_terms.len() - num_type_params) non-type-param
            // Pis before the type param Pis. So convert at that depth.
            let non_type_param_args = arg_type_terms.len() - num_type_params as usize;
            let result_type_term = self
                .type_store()
                .to_type_term_with_vars(t, self.type_var_map())
                .convert_free_to_bound_with_depth(num_type_params, non_type_param_args as u16);

            // Build the function type as a Term: arg1 -> arg2 -> ... -> result
            // using Term::pi for curried form
            let mut skolem_type_term = result_type_term;
            for arg_type in arg_type_terms.iter().rev() {
                skolem_type_term = Term::pi(arg_type.clone(), skolem_type_term);
            }

            let module_id = self.module_id();
            let skolem_id = self
                .as_mut()?
                .declare_synthetic_atom_with_type_term(module_id, skolem_type_term)?;
            synthesized.push(skolem_id);
            let (m, i) = skolem_id;
            let skolem_atom = Atom::Symbol(Symbol::Synthetic(m, i));
            let skolem_term = Term::new(skolem_atom, args.clone());
            output.push(skolem_term);
        }
        Ok(output)
    }

    fn make_skolem_term(
        &mut self,
        skolem_type: &AcornType,
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Term, String> {
        let mut terms = self.make_skolem_terms(
            std::slice::from_ref(skolem_type),
            stack,
            synthesized,
            context,
        )?;
        Ok(terms.pop().unwrap())
    }

    // Convert an "exists" node in a value, or the equivalent, to CNF.
    // negate is whether to negate the subvalue.
    fn exists_to_cnf(
        &mut self,
        quants: &Vec<AcornType>,
        subvalue: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let skolem_terms = self.make_skolem_terms(quants, stack, synthesized, context)?;
        let len = skolem_terms.len();
        for skolem_term in skolem_terms {
            stack.push(TermBinding::Bound(skolem_term));
        }
        let result =
            self.value_to_cnf(subvalue, negate, stack, next_var_id, synthesized, context)?;
        for _ in 0..len {
            stack.pop();
        }
        Ok(result)
    }

    // Convert an "and" node in a value, or the equivalent, to CNF.
    // negate_left and negate_right are whether to negate the respective subvalues.
    fn and_to_cnf(
        &mut self,
        left: &AcornValue,
        right: &AcornValue,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left =
            self.value_to_cnf(left, negate_left, stack, next_var_id, synthesized, context)?;
        let right = self.value_to_cnf(
            right,
            negate_right,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        Ok(left.and(right))
    }

    // Convert an "or" node in a value, or the equivalent, to CNF.
    // negate_left and negate_right are whether to negate the respective subvalues.
    fn or_to_cnf(
        &mut self,
        left: &AcornValue,
        right: &AcornValue,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left =
            self.value_to_cnf(left, negate_left, stack, next_var_id, synthesized, context)?;
        let right = self.value_to_cnf(
            right,
            negate_right,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        Ok(left.or(right))
    }

    // Convert an equality or inequality node in a value to CNF.
    // negate is whether it's an inequality.
    fn eq_to_cnf(
        &mut self,
        left: &AcornValue,
        right: &AcornValue,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        if let AcornValue::Match(scrutinee, cases) = right {
            // TODO: don't clone values here
            let mut answer = Cnf::true_value();
            for (vars, pattern, result) in cases {
                // The meaning of the branch is:
                //   scrutinee = pattern implies left (negate=) result
                let op = if negate {
                    BinaryOp::NotEquals
                } else {
                    BinaryOp::Equals
                };
                let condition = AcornValue::equals(*scrutinee.clone(), pattern.clone());
                let conclusion =
                    AcornValue::Binary(op, Box::new(left.clone()), Box::new(result.clone()));
                let branch = AcornValue::implies(condition, conclusion);
                let conjunct_value = AcornValue::forall(vars.clone(), branch);
                let conjunct_cnf =
                    self.value_to_cnf(&conjunct_value, false, stack, next_var_id, synth, context)?;
                answer = answer.and(conjunct_cnf);
            }
            return Ok(answer);
        }

        if let AcornType::Function(app) = left.get_type() {
            // Comparing functions.
            let mut arg_type_terms: Vec<Term> = Vec::with_capacity(app.arg_types.len());
            for t in &app.arg_types {
                arg_type_terms.push(
                    self.type_store()
                        .to_type_term_with_vars(t, self.type_var_map()),
                );
            }
            let result_type_term = self
                .type_store()
                .to_type_term_with_vars(&app.return_type, self.type_var_map());

            if result_type_term == Term::bool_type() {
                // Boolean functional comparison.
                if negate {
                    // Boolean functional inequality.
                    // Create skolem terms for each argument
                    let arg_terms =
                        self.make_skolem_terms(&app.arg_types, stack, synth, context)?;
                    let args: Vec<_> = arg_terms.into_iter().map(ExtendedTerm::Term).collect();
                    let left_pos = self.apply_to_cnf(
                        left,
                        args.clone(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let left_neg = self.apply_to_cnf(
                        left,
                        args.clone(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let right_pos = self.apply_to_cnf(
                        right,
                        args.clone(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let right_neg =
                        self.apply_to_cnf(right, args, true, stack, next_var_id, synth, context)?;

                    if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                        if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg)
                        {
                            // Both sides are simple, so we can return a single literal.
                            let positive = left_sign != right_sign;
                            let literal =
                                Literal::new(positive, left_term.clone(), right_term.clone());
                            return Ok(Cnf::from_literal(literal));
                        }
                    }

                    let some = left_pos.or(right_pos);
                    let not_both = left_neg.or(right_neg);
                    return Ok(not_both.and(some));
                }

                // Boolean functional equality.
                // Create new free variables for each argument
                let mut args = vec![];
                for arg_type_term in &arg_type_terms {
                    let var_id = *next_var_id;
                    context.push_type(arg_type_term.clone());
                    let var = Term::new_variable(var_id);
                    *next_var_id += 1;
                    args.push(ExtendedTerm::Term(var));
                }
                let left_pos = self.apply_to_cnf(
                    left,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let left_neg = self.apply_to_cnf(
                    left,
                    args.clone(),
                    true,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let right_pos = self.apply_to_cnf(
                    right,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let right_neg =
                    self.apply_to_cnf(right, args, true, stack, next_var_id, synth, context)?;

                if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                    if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg) {
                        // Both sides are simple, so we can return a single literal.
                        let positive = left_sign == right_sign;
                        let literal = Literal::new(positive, left_term.clone(), right_term.clone());
                        return Ok(Cnf::from_literal(literal));
                    }
                }

                let l_imp_r = left_neg.or(right_pos);
                let r_imp_l = left_pos.or(right_neg);
                return Ok(l_imp_r.and(r_imp_l));
            }

            // Non-boolean functional comparison.
            let left = self.value_to_extended_term(left, stack, next_var_id, synth, context)?;
            let right = self.value_to_extended_term(right, stack, next_var_id, synth, context)?;
            if negate {
                // Functional inequality.
                // Create skolem terms for each argument
                let args = self.make_skolem_terms(&app.arg_types, stack, synth, context)?;
                // Apply the skolem terms to both sides
                let left = left.apply(&args);
                let right = right.apply(&args);
                return left.eq_to_cnf(right, true);
            }

            // Functional equality.
            // Create new free variables for each argument
            let mut args = vec![];
            for arg_type_term in &arg_type_terms {
                let var_id = *next_var_id;
                context.push_type(arg_type_term.clone());
                let var = Term::new_variable(var_id);
                *next_var_id += 1;
                args.push(var);
            }
            // Apply the free variables to both sides
            let left = left.apply(&args);
            let right = right.apply(&args);
            return left.eq_to_cnf(right, false);
        }

        if left.is_bool_type() {
            if let Some((left_term, left_sign)) =
                self.try_simple_value_to_signed_term(left, stack)?
            {
                if let Some((right_term, right_sign)) =
                    self.try_simple_value_to_signed_term(right, stack)?
                {
                    // Both sides are terms, so we can do a simple equality or inequality
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(Cnf::from_literal(literal));
                }
            }

            // This logic duplicates subterms. Either we need to be careful that we don't synthesize
            // variables in these calls, or we need to globally deduplicate at synthesis time.
            if negate {
                // Boolean inequality.
                let some =
                    self.or_to_cnf(left, right, true, true, stack, next_var_id, synth, context)?;
                let not_both = self.or_to_cnf(
                    left,
                    right,
                    false,
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                return Ok(some.and(not_both));
            }

            // Boolean equality.
            let l_imp_r =
                self.or_to_cnf(left, right, true, false, stack, next_var_id, synth, context)?;
            let r_imp_l =
                self.or_to_cnf(left, right, false, true, stack, next_var_id, synth, context)?;
            return Ok(l_imp_r.and(r_imp_l));
        }

        // Plain old equality of terms.
        let left = self.value_to_extended_term(left, stack, next_var_id, synth, context)?;
        let right = self.value_to_extended_term(right, stack, next_var_id, synth, context)?;
        left.eq_to_cnf(right, negate)
    }

    /// Converts a value to a Term, if possible.
    /// This doesn't mutate the normalizer, so it only handles simple values, no quantifiers.
    /// This uses errors to report invalid values.
    /// If it is called on a value that doesn't convert to a term, it returns Ok(None).
    fn try_simple_value_to_term(
        &self,
        value: &AcornValue,
        stack: &Vec<TermBinding>,
    ) -> Result<Option<Term>, String> {
        match self.try_simple_value_to_signed_term(value, stack)? {
            None => Ok(None),
            Some((t, sign)) => {
                if sign {
                    Ok(Some(t))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Converts a value to a Term plus a sign, if possible.
    /// true = positive.
    /// This doesn't mutate the normalizer, so it only handles simple values, no quantifiers.
    /// This uses errors to report invalid values.
    /// If it is just called on a value that doesn't convert to a signed term, it returns Ok(None).
    fn try_simple_value_to_signed_term(
        &self,
        value: &AcornValue,
        stack: &Vec<TermBinding>,
    ) -> Result<Option<(Term, bool)>, String> {
        match value {
            AcornValue::Variable(i, _) => {
                if (*i as usize) < stack.len() {
                    Ok(Some((stack[*i as usize].term().clone(), true)))
                } else {
                    Err(format!("variable {} out of range in simple term", i))
                }
            }
            AcornValue::Application(application) => {
                let func_term = match self.try_simple_value_to_term(&application.function, stack)? {
                    Some(t) => t,
                    None => return Ok(None),
                };
                let head = *func_term.get_head_atom();
                let mut args = func_term.args().to_vec();
                for arg in &application.args {
                    let arg_term = match self.try_simple_value_to_term(arg, stack)? {
                        Some(t) => t,
                        None => return Ok(None),
                    };
                    args.push(arg_term);
                }
                Ok(Some((Term::new(head, args), true)))
            }
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    let Some(symbol) = self.symbol_table().get_symbol(&c.name) else {
                        return Err(format!("constant {} not found in symbol table", c));
                    };
                    Ok(Some((Term::new(Atom::Symbol(symbol), vec![]), true)))
                } else {
                    let term = self.symbol_table().term_from_instance_with_vars(
                        &c,
                        self.type_store(),
                        self.type_var_map(),
                    )?;
                    Ok(Some((term, true)))
                }
            }
            AcornValue::Not(subvalue) => {
                match self.try_simple_value_to_signed_term(subvalue, stack)? {
                    None => Ok(None),
                    Some((t, sign)) => Ok(Some((t, !sign))),
                }
            }
            AcornValue::Try(_, _) => Ok(None),
            AcornValue::Bool(v) => Ok(Some((Term::new_true(), *v))),
            _ => Ok(None),
        }
    }

    /// Handles application of a function to arguments, converting to an ExtendedTerm.
    fn apply_to_extended_term(
        &mut self,
        function: &AcornValue,
        args: Vec<ExtendedTerm>,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if let AcornValue::Lambda(_, return_value) = function {
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(arg.to_term()?);
            }
            let num_args = arg_terms.len();
            // Lambda arguments are bound variables
            for arg in arg_terms {
                stack.push(TermBinding::Bound(arg));
            }
            let answer =
                self.value_to_extended_term(&return_value, stack, next_var_id, synth, context);
            stack.truncate(stack.len() - num_args);
            return answer;
        }

        // We convert f(if a then b else c, d) into if a then f(b, d) else f(c, d).
        // The "spine" logic makes branching work for f as well.
        // If we discover a branching subterm, then we set cond and spine2.
        let mut cond: Option<Literal> = None;
        let mut spine1 = vec![];
        let mut spine2 = vec![];

        // First process the function
        match self.value_to_extended_term(function, stack, next_var_id, synth, context)? {
            ExtendedTerm::Term(t) => {
                spine1.push(t);
            }
            ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                cond = Some(sub_cond);
                spine1.push(sub_then);
                spine2.push(sub_else);
            }
            ExtendedTerm::Lambda(_, _) => {
                // Can this happen?
                return Err("unhandled case: secret lambda".to_string());
            }
        }

        // Determine the result type from the original application
        let args_len = args.len();

        // Then process the arguments
        for arg in args {
            match arg {
                ExtendedTerm::Term(t) => {
                    if !spine2.is_empty() {
                        spine2.push(t.clone());
                    }
                    spine1.push(t);
                }
                ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                    if !spine2.is_empty() {
                        return Err("unhandled case: multiple if args".to_string());
                    }
                    cond = Some(sub_cond);
                    spine2.extend(spine1.iter().cloned());
                    spine1.push(sub_then);
                    spine2.push(sub_else);
                }
                ExtendedTerm::Lambda(_, _) => {
                    return Err("unhandled case: lambda arg".to_string());
                }
            }
        }
        // Validate function type
        {
            let func_type = function.get_type();
            if let AcornType::Function(fapp) = func_type {
                if args_len > fapp.arg_types.len() {
                    return Err("too many arguments".to_string());
                }
            } else {
                return Err("cannot apply non-function".to_string());
            }
        }

        match cond {
            Some(cond) => {
                assert_eq!(spine1.len(), spine2.len());
                let then_term = Term::from_spine(spine1);
                let else_term = Term::from_spine(spine2);
                Ok(ExtendedTerm::If(cond, then_term, else_term))
            }
            None => {
                assert!(spine2.is_empty());
                let term = Term::from_spine(spine1);
                Ok(ExtendedTerm::Term(term))
            }
        }
    }

    /// Synthesizes a term to represent a value by creating a synthetic atom
    /// and defining it to equal the value.
    /// This is used for values that can't be directly converted to terms,
    /// like boolean logic expressions or lambdas.
    /// If an equivalent definition already exists, reuses the existing synthetic atom.
    fn synthesize_term(
        &mut self,
        value: &AcornValue,
        value_type: &AcornType,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Term, String> {
        // Create a tentative skolem term with the value's type
        let skolem_term = self.make_skolem_term(value_type, stack, synth, context)?;
        let skolem_id = if let Atom::Symbol(Symbol::Synthetic(m, id)) = *skolem_term.get_head_atom()
        {
            (m, id)
        } else {
            return Err("internal error: skolem term is not synthetic".to_string());
        };

        // Get the type of the synthetic atom from the symbol table
        let synthetic_type = self
            .kernel_context()
            .symbol_table
            .get_type(Symbol::Synthetic(skolem_id.0, skolem_id.1))
            .clone();

        // Create the definition for this synthetic term.
        // Build a var_remapping to convert term var_ids to stack positions.
        // The stack uses 0-based position indexing, but term variables use unique IDs.
        // When denormalizing, FreeVariable(id) needs to become Variable(stack_position).
        let max_var_id = stack
            .iter()
            .filter_map(|b| b.term().as_ref().atomic_variable())
            .max()
            .unwrap_or(0) as usize;
        let mut var_remapping: Vec<Option<u16>> = vec![None; max_var_id + 1];
        for (pos, binding) in stack.iter().enumerate() {
            if let Some(var_id) = binding.term().as_ref().atomic_variable() {
                var_remapping[var_id as usize] = Some(pos as u16);
            }
        }
        let type_var_id_to_name = self.get_var_id_to_name_map();
        let skolem_value = self.as_ref().denormalize_term(
            &skolem_term,
            context,
            None,
            Some(&var_remapping),
            None,
            Some(&type_var_id_to_name),
            false, // Don't instantiate type vars for skolem definitions
        );
        let definition_cnf = self.eq_to_cnf(
            &skolem_value,
            value,
            false,
            stack,
            next_var_id,
            synth,
            context,
        )?;

        // Check if an equivalent definition already exists
        // Convert CNF to clauses for the key lookup
        let type_vars = self.get_type_var_kinds();
        let num_type_vars = type_vars.len();
        let clauses = definition_cnf
            .clone()
            .into_clauses_with_pinned(context, num_type_vars);
        let key_clauses: Vec<Clause> = clauses
            .iter()
            .map(|c| c.invalidate_synthetics(&[skolem_id]))
            .collect();
        let synthetic_types = vec![synthetic_type.clone()];

        if let Some(existing_def) = self.as_ref().synthetic_registry.lookup_by_key(
            &type_vars,
            &synthetic_types,
            &key_clauses,
        ) {
            // Reuse the existing synthetic atom
            let (existing_m, existing_id) = existing_def.atoms[0];
            let existing_atom = Atom::Symbol(Symbol::Synthetic(existing_m, existing_id));
            let reused_term = Term::new(existing_atom, skolem_term.args().to_vec());
            Ok(reused_term)
        } else {
            // Define the new synthetic atom
            // No source available here since we're synthesizing during normalization
            let clauses = definition_cnf.into_clauses_with_pinned(context, num_type_vars);
            self.as_mut()?.define_synthetic_atoms(
                vec![skolem_id],
                type_vars,
                vec![synthetic_type],
                clauses,
                None,
            )?;
            Ok(skolem_term)
        }
    }

    /// Converts a value to an ExtendedTerm when it's being used as an argument.
    /// This handles lambdas specially by synthesizing terms for them,
    /// since lambdas can't be directly converted to plain terms.
    fn arg_to_extended_term(
        &mut self,
        value: &AcornValue,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        match value {
            AcornValue::Lambda(_, _) => {
                // Synthesize a term to represent this lambda
                let lambda_type = value.get_type();
                let skolem_term =
                    self.synthesize_term(value, &lambda_type, stack, next_var_id, synth, context)?;
                Ok(ExtendedTerm::Term(skolem_term))
            }
            _ => {
                // For non-lambda values, use the standard conversion
                self.value_to_extended_term(value, stack, next_var_id, synth, context)
            }
        }
    }

    /// Synthesizes a literal from a CNF by creating a new synthetic boolean atom
    /// and adding clauses that define it to be equivalent to the CNF.
    /// This uses a Tseitin-style transformation: for CNF C and new atom s,
    /// we add clauses for s <-> C, which is (s -> C) and (C -> s).
    fn synthesize_literal_from_cnf(
        &mut self,
        cnf: Cnf,
        stack: &Vec<TermBinding>,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Literal, String> {
        // Create a new synthetic boolean atom with the appropriate function type
        // based on free variables in the stack.
        // Keep types as Terms to avoid round-trip conversion through AcornType,
        // which would lose the original type parameter names.
        let mut arg_type_terms = vec![];
        let mut args = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        for binding in stack.iter() {
            // Use collect_vars with the context to get variable types
            for (var_id, closed_type) in binding.term().collect_vars(context) {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(var_id);
                    args.push(var_term);
                    arg_type_terms.push(closed_type);
                }
            }
        }

        // Build the function type as a Term: arg1 -> arg2 -> ... -> Bool
        let mut type_term = Term::bool_type();
        for arg_type in arg_type_terms.iter().rev() {
            type_term = Term::pi(arg_type.clone(), type_term);
        }

        // Add the atom type to the symbol table and declare the synthetic atom
        let module_id = self.module_id();
        let atom_id = self
            .as_mut()?
            .declare_synthetic_atom_with_type_term(module_id, type_term)?;
        synth.push(atom_id);

        // Get the synthetic type from the symbol table
        let (m, i) = atom_id;
        let synthetic_type = self
            .kernel_context()
            .symbol_table
            .get_type(Symbol::Synthetic(m, i))
            .clone();

        let atom = Atom::Symbol(Symbol::Synthetic(m, i));
        let synth_term = Term::new(atom, args);
        let synth_lit = Literal::from_signed_term(synth_term.clone(), true);

        // Create defining CNF for: s <-> C
        // This is (s -> C) and (C -> s)
        // Which is (not s or C) and (not C or s)

        // For (not s or C): add not_s to each clause in C
        let not_s_implies_c = Cnf::from_literal(synth_lit.negate()).or(cnf.clone());

        // For (C -> s): which is (not C or s)
        let c_implies_s = cnf.negate().or(Cnf::from_literal(synth_lit.clone()));

        let defining_cnf = not_s_implies_c.and(c_implies_s);

        // Add the definition
        let type_vars = self.get_type_var_kinds();
        let num_type_vars = type_vars.len();
        let clauses = defining_cnf.into_clauses_with_pinned(context, num_type_vars);
        self.as_mut()?.define_synthetic_atoms(
            vec![atom_id],
            type_vars,
            vec![synthetic_type],
            clauses,
            None,
        )?;

        Ok(synth_lit)
    }

    /// Converts an ExtendedTerm to a plain Term.
    /// If the ExtendedTerm is an If expression, synthesizes a new atom for it.
    /// The local_context provides variable type information.
    fn extended_term_to_term(
        &mut self,
        ext_term: ExtendedTerm,
        local_context: &LocalContext,
        synth: &mut Vec<(ModuleId, AtomId)>,
    ) -> Result<Term, String> {
        match ext_term {
            ExtendedTerm::Term(t) => Ok(t),
            ExtendedTerm::If(cond_lit, then_term, else_term) => {
                // Optimization: if both branches are the same, just return that term
                if then_term == else_term {
                    return Ok(then_term);
                }
                // We need to synthesize a new atom that represents this if-expression
                // The defining clauses will be:
                // For atom s representing "if cond then then_term else else_term":
                // (cond -> s = then_term) and (not cond -> s = else_term)
                // Which is (not cond or s = then_term) and (cond or s = else_term)

                // Determine the type of the result (should be same as then_term and else_term)
                // Keep types as Terms to avoid round-trip conversion through AcornType,
                // which would lose the original type parameter names.
                let result_type_term =
                    then_term.get_type_with_context(local_context, self.kernel_context());

                // Create a new synthetic atom with the appropriate function type
                // based on free variables in the if-expression
                let mut arg_type_terms = vec![];
                let mut args = vec![];
                let mut seen_vars = std::collections::HashSet::new();

                // In polymorphic mode, include type parameters as arguments.
                // This matches how make_skolem_terms handles polymorphic synthetics.
                if let Some(type_var_map) = self.type_var_map() {
                    let mut entries: Vec<_> = type_var_map.values().collect();
                    entries.sort_by_key(|(id, _)| *id);
                    for (var_id, var_type) in entries {
                        let var_term = Term::new_variable(*var_id);
                        args.push(var_term);
                        // Type variables have their kind (TypeSort or typeclass) as their type in the Pi
                        arg_type_terms.push(var_type.clone());
                        seen_vars.insert(*var_id);
                    }
                }

                // Collect free variables from the condition literal
                // Skip type parameters (TypeSort or Typeclass) - they're not value arguments
                for (var_id, closed_type) in cond_lit.left.collect_vars(local_context) {
                    if closed_type.as_ref().is_type_param_kind() {
                        continue;
                    }
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(var_id);
                        args.push(var_term);
                        arg_type_terms.push(closed_type);
                    }
                }
                for (var_id, closed_type) in cond_lit.right.collect_vars(local_context) {
                    if closed_type.as_ref().is_type_param_kind() {
                        continue;
                    }
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(var_id);
                        args.push(var_term);
                        arg_type_terms.push(closed_type);
                    }
                }

                // Collect free variables from the then branch
                for (var_id, closed_type) in then_term.collect_vars(local_context) {
                    if closed_type.as_ref().is_type_param_kind() {
                        continue;
                    }
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(var_id);
                        args.push(var_term);
                        arg_type_terms.push(closed_type);
                    }
                }

                // Collect free variables from the else branch
                for (var_id, closed_type) in else_term.collect_vars(local_context) {
                    if closed_type.as_ref().is_type_param_kind() {
                        continue;
                    }
                    if seen_vars.insert(var_id) {
                        let var_term = Term::new_variable(var_id);
                        args.push(var_term);
                        arg_type_terms.push(closed_type);
                    }
                }

                // Convert FreeVariables in types to BoundVariables for the Pi structure.
                // This is needed because symbol types use BoundVariable for parameters.
                // Type parameter kinds (TypeSort/Typeclass) don't need conversion.
                let num_type_params = self.type_var_map().map_or(0, |m| m.len()) as u16;
                let mut non_type_param_index = 0u16;
                let arg_type_terms: Vec<Term> = arg_type_terms
                    .into_iter()
                    .map(|t| {
                        if t.as_ref().is_type_param_kind() {
                            t // Type parameter kinds don't need conversion
                        } else {
                            let depth = non_type_param_index;
                            non_type_param_index += 1;
                            t.convert_free_to_bound_with_depth(num_type_params, depth)
                        }
                    })
                    .collect();
                let non_type_param_args = arg_type_terms.len() - num_type_params as usize;
                let result_type_term = result_type_term
                    .convert_free_to_bound_with_depth(num_type_params, non_type_param_args as u16);

                // Build the function type as a Term: arg1 -> arg2 -> ... -> result_type
                let mut type_term = result_type_term;
                for arg_type in arg_type_terms.iter().rev() {
                    type_term = Term::pi(arg_type.clone(), type_term);
                }

                // Add the atom type to the symbol table and declare the synthetic atom
                let module_id = self.module_id();
                let atom_id = self
                    .as_mut()?
                    .declare_synthetic_atom_with_type_term(module_id, type_term)?;
                synth.push(atom_id);

                // Get the synthetic type from the symbol table
                let (m, i) = atom_id;
                let synthetic_type = self
                    .kernel_context()
                    .symbol_table
                    .get_type(Symbol::Synthetic(m, i))
                    .clone();

                let atom = Atom::Symbol(Symbol::Synthetic(m, i));
                let synth_term = Term::new(atom, args);

                // Create defining CNF for the if-expression
                // (not cond or synth_term = then_term) and (cond or synth_term = else_term)

                // First clause: not cond or synth_term = then_term
                let then_eq = Literal::new(true, synth_term.clone(), then_term);
                let first_clause =
                    Cnf::from_literal(cond_lit.negate()).or(Cnf::from_literal(then_eq));

                // Second clause: cond or synth_term = else_term
                let else_eq = Literal::new(true, synth_term.clone(), else_term);
                let second_clause =
                    Cnf::from_literal(cond_lit.clone()).or(Cnf::from_literal(else_eq));

                let defining_cnf = first_clause.and(second_clause);

                // Add the definition
                let type_vars = self.get_type_var_kinds();
                let num_type_vars = type_vars.len();
                let clauses = defining_cnf.into_clauses_with_pinned(local_context, num_type_vars);
                self.as_mut()?.define_synthetic_atoms(
                    vec![atom_id],
                    type_vars,
                    vec![synthetic_type],
                    clauses,
                    None,
                )?;

                Ok(synth_term)
            }
            ExtendedTerm::Lambda(_, t) => Err(format!("cannot convert lambda {} to plain term", t)),
        }
    }

    /// Converts a value to an ExtendedTerm, which can appear in places a Term does.
    fn value_to_extended_term(
        &mut self,
        value: &AcornValue,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        match value {
            AcornValue::IfThenElse(cond_val, then_value, else_value) => {
                // Convert the condition to CNF, using the main context to track variable types.
                // This is important because foralls in the condition will push variable types
                // to the context, and we need those types when creating clauses.
                let cond_cnf =
                    self.value_to_cnf(cond_val, false, stack, next_var_id, synth, context)?;
                let cond_lit = if cond_cnf.is_literal() {
                    cond_cnf.to_literal().unwrap()
                } else {
                    // For non-literal conditions, synthesize a new boolean atom
                    self.synthesize_literal_from_cnf(cond_cnf, stack, synth, context)?
                };
                let then_ext =
                    self.value_to_extended_term(then_value, stack, next_var_id, synth, context)?;
                let then_branch = self.extended_term_to_term(then_ext, context, synth)?;
                let else_ext =
                    self.value_to_extended_term(else_value, stack, next_var_id, synth, context)?;
                let else_branch = self.extended_term_to_term(else_ext, context, synth)?;
                Ok(ExtendedTerm::If(cond_lit, then_branch, else_branch))
            }
            AcornValue::Application(app) => {
                let mut arg_exts = vec![];
                for arg in &app.args {
                    arg_exts.push(self.arg_to_extended_term(
                        arg,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?);
                }
                self.apply_to_extended_term(
                    &app.function,
                    arg_exts,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )
            }
            AcornValue::Variable(i, var_type) => {
                if (*i as usize) < stack.len() {
                    Ok(ExtendedTerm::Term(stack[*i as usize].term().clone()))
                } else {
                    Err(format!(
                        "variable {} (type {}) out of range in extended term (stack len {})",
                        i,
                        var_type,
                        stack.len()
                    ))
                }
            }
            AcornValue::Constant(c) => {
                if c.params.is_empty() {
                    let Some(symbol) = self.symbol_table().get_symbol(&c.name) else {
                        return Err(format!("constant {} not found in symbol table", c));
                    };
                    Ok(ExtendedTerm::Term(Term::new(Atom::Symbol(symbol), vec![])))
                } else {
                    let term = self.symbol_table().term_from_instance_with_vars(
                        &c,
                        self.type_store(),
                        self.type_var_map(),
                    )?;
                    Ok(ExtendedTerm::Term(term))
                }
            }
            AcornValue::Not(_) => Err("negation in unexpected position".to_string()),
            AcornValue::Try(_, _) => Err("try operator not yet implemented".to_string()),
            AcornValue::Lambda(arg_types, body) => {
                // Create variable terms for each lambda argument
                // Use next_var_id to assign unique variable IDs
                let mut args = vec![];
                for arg_type in arg_types {
                    let type_term = self
                        .type_store()
                        .to_type_term_with_vars(arg_type, self.type_var_map());
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    // Add the variable type to the context
                    context.push_type(type_term.clone());
                    let var = Term::new_variable(var_id);
                    args.push((var_id, type_term));
                    stack.push(TermBinding::Free(var));
                }

                // Evaluate the body with the lambda arguments on the stack
                let body_ext =
                    self.value_to_extended_term(body, stack, next_var_id, synth, context)?;
                // Convert to Term, synthesizing if needed for If expressions
                let body_term = self.extended_term_to_term(body_ext, context, synth)?;

                // Pop the lambda arguments from the stack
                for _ in arg_types {
                    stack.pop();
                }

                Ok(ExtendedTerm::Lambda(args, body_term))
            }
            AcornValue::Bool(b) => {
                if *b {
                    Ok(ExtendedTerm::Term(Term::new_true()))
                } else {
                    Err("false literal in unexpected position".to_string())
                }
            }
            value if value.is_bool_type() => {
                // Synthesize a term to represent this boolean value.
                let skolem_term = self.synthesize_term(
                    value,
                    &AcornType::Bool,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                Ok(ExtendedTerm::Term(skolem_term))
            }
            _ => Err(format!("cannot convert '{}' to extended term", value)),
        }
    }
}

impl Normalizer {
    /// This should handle any sort of boolean value.
    /// TODO: port edge cases into the "nice" value to clauses so that we only have one of these.
    fn ugly_value_to_clauses(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        source: &Source,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        self.kernel_context.symbol_table.add_from(
            &value,
            ctype,
            &mut self.kernel_context.type_store,
        );

        // TODO: can we remove this? Expanding them doesn't really seem right.
        // Maybe we can inline lambdas instead of expanding them.
        let value = value.expand_lambdas(0);

        // Check for dropped forall variables only when normalizing negated goals.
        let mut skolem_ids = vec![];
        let mut mut_view =
            NormalizationContext::new_mut(self, type_var_map.clone(), source.module_id);
        let clauses = mut_view.nice_value_to_clauses(&value, &mut skolem_ids)?;

        // For any of the created ids that have not been defined yet, the output
        // clauses will be their definition.
        let mut output = vec![];
        let mut undefined_ids = vec![];
        for id in skolem_ids {
            if let Some(def) = self.synthetic_registry.get(&id) {
                for clause in &def.clauses {
                    output.push(clause.clone());
                }
            } else {
                undefined_ids.push(id);
            }
        }

        if !undefined_ids.is_empty() {
            // We have to define the skolem atoms that were declared during skolemization.
            // Get type_vars from the type_var_map parameter
            let type_vars: Vec<Term> = if let Some(ref tvm) = type_var_map {
                let mut entries: Vec<_> = tvm.values().collect();
                entries.sort_by_key(|(id, _)| *id);
                entries.iter().map(|(_, kind)| kind.clone()).collect()
            } else {
                vec![]
            };

            // Get the types for these synthetic atoms from the symbol table.
            let synthetic_types: Vec<Term> = undefined_ids
                .iter()
                .map(|&(m, i)| {
                    self.kernel_context
                        .symbol_table
                        .get_type(Symbol::Synthetic(m, i))
                        .clone()
                })
                .collect();

            self.define_synthetic_atoms(
                undefined_ids,
                type_vars,
                synthetic_types,
                clauses.clone(),
                Some(source.clone()),
            )?;
        }

        output.extend(clauses.into_iter());
        Ok(output)
    }

    /// Converts a value to CNF: Conjunctive Normal Form.
    /// In other words, a successfully normalized value turns into a bunch of clauses.
    /// Logically, this is an "and of ors".
    /// Each Clause represents an implicit "forall", plus an "or" of its literals.
    /// "true" is represented by an empty list, which is always satisfied.
    /// "false" is represented by a single impossible clause.
    /// This is kind of just a wrapper around convert_then_normalize which adds on
    /// some verification and a hack for functional equality.
    fn normalize_value(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        source: &Source,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        if let Err(e) = value.validate() {
            return Err(format!(
                "validation error: {} while normalizing: {}",
                e, value
            ));
        }
        assert!(value.is_bool_type());

        let clauses = self.ugly_value_to_clauses(value, ctype, source, type_var_map)?;
        Ok(clauses)
    }

    /// A single fact can turn into a bunch of proof steps.
    pub fn normalize_fact(&mut self, fact: &Fact) -> Result<NormalizedFact, BuildError> {
        let mut steps = vec![];

        // Register typeclass relationships in TypeStore
        match fact {
            Fact::Instance(datatype, typeclass, _) => {
                let acorn_type = AcornType::Data(datatype.clone(), vec![]);
                let typeclass_id = self.kernel_context.type_store.add_typeclass(typeclass);
                self.kernel_context
                    .type_store
                    .add_type_instance(&acorn_type, typeclass_id);
            }
            Fact::Extends(typeclass, base_set, provides_inhabitants, _) => {
                let tc_id = self.kernel_context.type_store.add_typeclass(typeclass);
                for base in base_set {
                    let base_id = self.kernel_context.type_store.add_typeclass(base);
                    self.kernel_context
                        .type_store
                        .add_typeclass_extends(tc_id, base_id);
                }
                // If the typeclass has a constant of the instance type (e.g., point: P),
                // mark it as providing inhabitants.
                if *provides_inhabitants {
                    self.kernel_context
                        .symbol_table
                        .mark_typeclass_inhabited(tc_id);
                }
            }
            _ => {}
        }

        let range = fact.source().range;

        {
            use crate::elaborator::acorn_type::TypeParam;

            // We keep track of type params to build the type_var_map
            let propositions: Vec<(AcornValue, Vec<TypeParam>, Source)> = match fact {
                Fact::Proposition(prop) => {
                    vec![(prop.value.clone(), prop.params.clone(), prop.source.clone())]
                }
                Fact::Definition(potential, definition, source) => {
                    let (params, constant) = match potential {
                        PotentialValue::Unresolved(u) => {
                            (u.params.clone(), u.clone().to_generic_value())
                        }
                        PotentialValue::Resolved(c) => (vec![], c.clone()),
                    };
                    let claim = constant.inflate_function_definition(definition.clone());
                    let prop = Proposition::new(claim, params, source.clone());
                    vec![(prop.value, prop.params, prop.source)]
                }
                Fact::Extends(..) | Fact::Instance(..) => {
                    // These don't produce propositions
                    vec![]
                }
            };

            for (value, type_params, source) in propositions {
                // Build type_var_map from type parameters.
                // Each type parameter gets a variable ID and a type (TypeSort or Typeclass).
                let type_var_map: HashMap<String, (AtomId, Term)> = type_params
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        let var_type = if let Some(tc) = &p.typeclass {
                            // Type parameter has a typeclass constraint
                            let tc_id = self.kernel_context.type_store.add_typeclass(tc);
                            Term::typeclass(tc_id)
                        } else {
                            // Unconstrained type parameter
                            Term::type_sort()
                        };
                        (p.name.clone(), (i as AtomId, var_type))
                    })
                    .collect();

                let type_var_map_opt = if type_var_map.is_empty() {
                    None
                } else {
                    Some(type_var_map)
                };
                let ctype = if source.truthiness() == Truthiness::Factual {
                    NewConstantType::Global
                } else {
                    NewConstantType::Local
                };
                let clauses = self
                    .normalize_value(&value, ctype, &source, type_var_map_opt.clone())
                    .map_err(|msg| BuildError::new(range, msg))?;
                for clause in &clauses {
                    trace!(clause = %clause, "normalized to clause");
                }
                for clause in clauses {
                    clause.validate(&self.kernel_context);
                    let step = ProofStep::assumption(&source, clause);
                    steps.push(step);
                }
            }
        }

        Ok(NormalizedFact { steps })
    }

    /// Normalizes a goal into proof steps that include both positive versions
    /// of the hypotheses and negated versions of the conclusion.
    pub fn normalize_goal(&mut self, goal: &Goal) -> Result<NormalizedGoal, BuildError> {
        let prop = &goal.proposition;

        let (hypo, counterfactual) = prop.value.clone().negate_goal();
        let mut steps = vec![];
        if let Some(hypo) = hypo {
            // Preserve type parameters when creating hypothesis fact
            let hypo_prop = Proposition::new(hypo, prop.params.clone(), prop.source.clone());
            let fact = Fact::Proposition(Arc::new(hypo_prop));
            steps.extend(self.normalize_fact(&fact)?.steps);
        }
        // Preserve type parameters when creating counterfactual fact
        let counterfactual_prop = Proposition::new(
            counterfactual,
            prop.params.clone(),
            prop.source.as_negated_goal(),
        );
        let fact = Fact::Proposition(Arc::new(counterfactual_prop));
        steps.extend(self.normalize_fact(&fact)?.steps);

        Ok(NormalizedGoal {
            goal: goal.clone(),
            steps,
            normalizer: self.clone(),
        })
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_remapping is provided, variable indices are remapped (used when type variables
    /// are filtered out of forall quantifiers).
    /// If type_var_id_to_name is provided, FreeVariable type variables use proper names.
    fn denormalize_atom(
        &self,
        atom_type: &Term,
        atom: &Atom,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
    ) -> AcornValue {
        let acorn_type = if let Some(name_map) = type_var_id_to_name {
            self.kernel_context
                .type_store
                .type_term_to_acorn_type_with_var_names(atom_type, name_map)
        } else {
            self.kernel_context
                .type_store
                .type_term_to_acorn_type(atom_type)
        };
        match atom {
            Atom::Symbol(Symbol::True) => AcornValue::Bool(true),
            Atom::Symbol(Symbol::False) => AcornValue::Bool(false),
            Atom::Symbol(Symbol::GlobalConstant(m, i)) => {
                let name = self
                    .kernel_context
                    .symbol_table
                    .name_for_global_id(*m, *i)
                    .clone();
                // Look up stored polymorphic info
                if let Some(poly_info) =
                    self.kernel_context.symbol_table.get_polymorphic_info(&name)
                {
                    AcornValue::constant(
                        name,
                        vec![],
                        poly_info.generic_type.clone(),
                        poly_info.generic_type.clone(),
                        poly_info.type_param_names.clone(),
                    )
                } else {
                    // Non-polymorphic constant
                    AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
                }
            }
            Atom::Symbol(Symbol::ScopedConstant(i)) => {
                let name = self
                    .kernel_context
                    .symbol_table
                    .name_for_local_id(*i)
                    .clone();
                // Look up stored polymorphic info
                if let Some(poly_info) =
                    self.kernel_context.symbol_table.get_polymorphic_info(&name)
                {
                    AcornValue::constant(
                        name,
                        vec![],
                        poly_info.generic_type.clone(),
                        poly_info.generic_type.clone(),
                        poly_info.type_param_names.clone(),
                    )
                } else {
                    // Non-polymorphic constant
                    AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
                }
            }
            Atom::FreeVariable(i) => {
                if let Some(map) = arbitrary_names {
                    if let Some(name) = map.get(atom_type) {
                        // Non-generic: generic_type equals instance_type
                        return AcornValue::constant(
                            name.clone(),
                            vec![],
                            acorn_type.clone(),
                            acorn_type,
                            vec![],
                        );
                    }
                }
                // Apply remapping if provided
                let new_i = var_remapping
                    .and_then(|mapping| mapping.get(*i as usize))
                    .and_then(|opt| *opt)
                    .unwrap_or(*i);
                AcornValue::Variable(new_i, acorn_type)
            }
            Atom::Symbol(Symbol::Synthetic(m, i)) => {
                let symbol = Symbol::Synthetic(*m, *i);
                let type_term = self.kernel_context.symbol_table.get_type(symbol);
                let acorn_type = if let Some(name_map) = type_var_id_to_name {
                    self.kernel_context
                        .type_store
                        .type_term_to_acorn_type_with_var_names(type_term, name_map)
                } else {
                    self.kernel_context
                        .type_store
                        .type_term_to_acorn_type(type_term)
                };
                let name = ConstantName::Synthetic(*m, *i);

                // In polymorphic mode, check if the type has leading type parameter Pis
                // (Pi types where the input is TypeSort or a Typeclass)
                {
                    let num_type_params = type_term.as_ref().count_type_params();
                    if num_type_params > 0 {
                        // This is a polymorphic synthetic - use provided names or generate defaults
                        let names: Vec<String> = if let Some(provided) = type_param_names {
                            // Use the provided names (computed by code_generator)
                            provided[..num_type_params].to_vec()
                        } else {
                            // Fallback to "X{i}" - intentionally different from "T{i}" so tests
                            // will fail if proper names aren't being passed when they should be
                            (0..num_type_params).map(|i| format!("X{}", i)).collect()
                        };
                        return AcornValue::constant(
                            name,
                            vec![],
                            acorn_type.clone(),
                            acorn_type,
                            names,
                        );
                    }
                }

                // Non-polymorphic: generic_type equals instance_type
                AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
            }
            Atom::Symbol(Symbol::Type(_))
            | Atom::Symbol(Symbol::Empty)
            | Atom::Symbol(Symbol::Bool)
            | Atom::Symbol(Symbol::Type0) => {
                panic!("Type symbols should not appear in open terms")
            }
            Atom::Symbol(Symbol::Typeclass(_)) => {
                panic!("Typeclass atoms should not appear in open terms")
            }
            Atom::BoundVariable(_) => {
                panic!("BoundVariable atoms should not appear in denormalize_atom")
            }
        }
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_remapping is provided, variable indices are remapped.
    /// If type_param_names is provided, it's used for polymorphic synthetic atoms.
    /// If type_var_id_to_name is provided, FreeVariable type arguments use proper names.
    /// If instantiate_type_vars is true, FreeVariable type atoms become concrete types.
    fn denormalize_term(
        &self,
        term: &Term,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        // Get the type of the head atom
        let head_type = match term.get_head_atom() {
            Atom::FreeVariable(i) => local_context
                .get_var_type(*i as usize)
                .cloned()
                .expect("Variable should have type in LocalContext"),
            Atom::Symbol(Symbol::Typeclass(_)) => {
                panic!("Typeclass atoms should not appear as head of terms")
            }
            Atom::Symbol(symbol) => self
                .kernel_context
                .symbol_table
                .get_symbol_type(*symbol, &self.kernel_context.type_store),
            Atom::BoundVariable(_) => {
                panic!("BoundVariable atoms should not appear as head of terms")
            }
        };

        // Type arguments appear as terms. Skip them in denormalization.
        // TypeSort is for unconstrained type params, Typeclass is for constrained type params.
        if head_type.as_ref().is_type_param_kind() {
            // This is a type argument - don't try to denormalize it as a value
            // Return a placeholder that won't be used (the caller should handle type args specially)
            return AcornValue::Bool(true);
        }

        let head = self.denormalize_atom(
            &head_type,
            &term.get_head_atom(),
            arbitrary_names,
            var_remapping,
            type_param_names,
            type_var_id_to_name,
        );

        // Type arguments appear as the first few arguments.
        // We need to:
        // 1. Extract type arguments and convert them to AcornTypes
        // 2. Update the head constant with those type parameters
        // 3. Apply only the value arguments

        let mut type_args: Vec<AcornType> = vec![];
        let mut value_args: Vec<AcornValue> = vec![];

        for arg in term.args().iter() {
            let arg_type = arg.get_type_with_context(local_context, &self.kernel_context);
            // TypeSort is for unconstrained type params, Typeclass is for constrained type params
            if arg_type.as_ref().is_type_param_kind() {
                // This is a type argument - convert it to an AcornType
                // Extract the typeclass constraint from arg_type if it's a Typeclass
                let typeclass = if let Atom::Symbol(Symbol::Typeclass(tc_id)) =
                    arg_type.as_ref().get_head_atom()
                {
                    self.kernel_context
                        .type_store
                        .get_typeclass_by_id(*tc_id)
                        .cloned()
                } else {
                    None
                };
                // If it's a FreeVariable and we have a name mapping, use the proper name
                let acorn_type = if let Some(var_id) = arg.as_ref().atomic_variable() {
                    if let Some(name) = type_var_id_to_name.and_then(|m| m.get(&var_id)) {
                        AcornType::Variable(TypeParam {
                            name: name.clone(),
                            typeclass,
                        })
                    } else {
                        self.kernel_context
                            .type_store
                            .type_term_to_acorn_type_with_context(
                                arg,
                                local_context,
                                instantiate_type_vars,
                            )
                    }
                } else {
                    self.kernel_context
                        .type_store
                        .type_term_to_acorn_type_with_context(
                            arg,
                            local_context,
                            instantiate_type_vars,
                        )
                };
                type_args.push(acorn_type);
            } else {
                // This is a value argument
                value_args.push(self.denormalize_term(
                    arg,
                    local_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                ));
            }
        }

        // Update the head with type parameters if needed
        let head = if !type_args.is_empty() {
            match head {
                AcornValue::Constant(c) => {
                    // Compute the instance_type by applying type args to generic_type
                    let named_params: Vec<_> = c
                        .type_param_names
                        .iter()
                        .zip(type_args.iter())
                        .map(|(name, t)| (name.clone(), t.clone()))
                        .collect();
                    let instance_type = c.generic_type.instantiate(&named_params);

                    AcornValue::Constant(ConstantInstance {
                        name: c.name.clone(),
                        params: type_args.clone(),
                        instance_type,
                        generic_type: c.generic_type.clone(),
                        type_param_names: c.type_param_names.clone(),
                    })
                }
                other => other, // Non-constant head, just keep as is
            }
        } else {
            head
        };

        AcornValue::apply(head, value_args)
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_remapping is provided, variable indices are remapped.
    /// If type_var_id_to_name is provided, FreeVariable type arguments use proper names.
    /// If instantiate_type_vars is true, FreeVariable type atoms become concrete types.
    fn denormalize_literal(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        let left = self.denormalize_term(
            &literal.left,
            local_context,
            arbitrary_names,
            var_remapping,
            type_param_names,
            type_var_id_to_name,
            instantiate_type_vars,
        );
        if literal.right.is_true() {
            if literal.positive {
                return left;
            } else {
                return AcornValue::Not(Box::new(left));
            }
        }
        let right = self.denormalize_term(
            &literal.right,
            local_context,
            arbitrary_names,
            var_remapping,
            type_param_names,
            type_var_id_to_name,
            instantiate_type_vars,
        );
        if literal.positive {
            AcornValue::equals(left, right)
        } else {
            AcornValue::not_equals(left, right)
        }
    }

    /// Converts backwards, from a clause to a value.
    /// The resulting value may have synthetic atoms in it.
    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If type_vars is provided, those variable indices are treated as type-level variables
    /// and excluded from the forall quantifier (their indices are remapped in the body).
    /// If type_param_names is provided, it's used for naming polymorphic synthetic type params.
    /// If instantiate_type_vars is true, FreeVariable type atoms become concrete types.
    /// Any remaining free variables are enclosed in a "forall" quantifier.
    pub fn denormalize(
        &self,
        clause: &Clause,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        type_param_names: Option<&[String]>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        if clause.literals.is_empty() {
            return AcornValue::Bool(false);
        }
        let local_context = clause.get_local_context();

        // Find the number of variables actually used in the clause.
        // The local_context may have more variables than are used.
        let num_vars = clause
            .literals
            .iter()
            .filter_map(|lit| {
                let left_max = lit.left.max_variable();
                let right_max = lit.right.max_variable();
                match (left_max, right_max) {
                    (Some(l), Some(r)) => Some(l.max(r)),
                    (Some(l), None) => Some(l),
                    (None, Some(r)) => Some(r),
                    (None, None) => None,
                }
            })
            .max()
            .map(|max| (max + 1) as usize)
            .unwrap_or(0);

        let var_types_raw = local_context.get_var_types();

        // Build variable remapping: for each original index, what's its new index?
        // Type variables and arbitrary variables get None (excluded from forall).
        let mut var_remapping: Vec<Option<u16>> = Vec::new();
        let mut new_index: u16 = 0;
        for i in 0..num_vars {
            let type_term = &var_types_raw[i];
            // A variable is a type variable if its kind is Type0 (unconstrained) or Typeclass (constrained)
            let is_type_var = type_term.as_ref().is_type_param_kind();
            let is_arbitrary = arbitrary_names
                .map(|m| m.contains_key(type_term))
                .unwrap_or(false);

            if is_type_var || is_arbitrary {
                var_remapping.push(None);
            } else {
                var_remapping.push(Some(new_index));
                new_index += 1;
            }
        }

        // Denormalize literals with the remapping
        let var_remapping_ref = if var_remapping.iter().any(|x| x.is_none()) {
            Some(var_remapping.as_slice())
        } else {
            None // No remapping needed if all variables are kept
        };

        let mut denormalized_literals = vec![];
        for literal in &clause.literals {
            denormalized_literals.push(self.denormalize_literal(
                literal,
                local_context,
                arbitrary_names,
                var_remapping_ref,
                type_param_names,
                None, // No type var id to name mapping needed for public denormalize
                instantiate_type_vars,
            ));
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, denormalized_literals);

        // Build var_types for the forall quantifier (only non-excluded variables)
        let var_types: Vec<AcornType> = var_types_raw
            .iter()
            .take(num_vars)
            .enumerate()
            .filter(|(i, _)| var_remapping.get(*i).copied().flatten().is_some())
            .map(|(_, type_term)| {
                self.kernel_context
                    .type_store
                    .type_term_to_acorn_type(type_term)
            })
            .collect();

        AcornValue::forall(var_types, disjunction)
    }

    /// Convert a type Term to AcornType, looking up typeclass constraints from LocalContext.
    /// If `instantiate_type_vars` is true, FreeVariable type atoms become concrete types.
    pub fn denormalize_type_with_context(
        &self,
        type_term: Term,
        local_context: &LocalContext,
        instantiate_type_vars: bool,
    ) -> AcornType {
        self.kernel_context
            .type_store
            .type_term_to_acorn_type_with_context(&type_term, local_context, instantiate_type_vars)
    }

    /// Given a list of (module_id, atom_id) for synthetic atoms that we need to define, find a set
    /// of SyntheticInfo that covers them.
    /// The output may have synthetic atoms that aren't used in the input.
    /// The input doesn't have to be in order and may contain duplicates.
    pub fn find_covering_synthetic_info(
        &self,
        ids: &[(ModuleId, AtomId)],
    ) -> Vec<Arc<SyntheticDefinition>> {
        self.synthetic_registry.find_covering_info(ids)
    }

    pub fn atom_str(&self, atom: &Atom) -> String {
        self.kernel_context.atom_str(atom)
    }

    /// When you denormalize and renormalize a clause, you should get the same thing.
    #[cfg(test)]
    fn check_denormalize_renormalize(&mut self, clause: &Clause) {
        let denormalized = self.denormalize(clause, None, None, false);
        if let Err(e) = denormalized.validate() {
            eprintln!("DEBUG: clause = {}", clause);
            eprintln!("DEBUG: clause context = {:?}", clause.get_local_context());
            eprintln!("DEBUG: denormalized = {}", denormalized);
            panic!("denormalized clause should validate: {:?}", e);
        }
        let renormalized = self
            .normalize_value(&denormalized, NewConstantType::Local, &Source::mock(), None)
            .unwrap();
        if renormalized.len() != 1 {
            // For functional equalities, we know this check doesn't work.
            // So we skip it.
            return;
        }
        if clause != &renormalized[0] {
            println!("original clause: {}", clause);
            println!("original context: {:?}", clause.get_local_context());
            println!("denormalized: {}", denormalized);
            println!("renormalized: {}", renormalized[0]);
            println!(
                "renormalized context: {:?}",
                renormalized[0].get_local_context()
            );
            if clause.get_local_context() == renormalized[0].get_local_context() {
                // Contexts match but clauses don't - might be variable ordering in literals
                for (i, (orig_lit, renorm_lit)) in clause
                    .literals
                    .iter()
                    .zip(renormalized[0].literals.iter())
                    .enumerate()
                {
                    if orig_lit != renorm_lit {
                        println!("literal {} differs: {} vs {}", i, orig_lit, renorm_lit);
                    }
                }
            }
            panic!("renormalized clause does not match original");
        }
    }

    #[cfg(test)]
    fn check_value(&mut self, value: &AcornValue, expected: &[&str]) {
        use crate::kernel::display::DisplayClause;

        let actual = self
            .normalize_value(value, NewConstantType::Local, &Source::mock(), None)
            .unwrap();
        if actual.len() != expected.len() {
            panic!(
                "expected {} clauses, got {}:\n{}",
                expected.len(),
                actual.len(),
                actual
                    .iter()
                    .map(|c| DisplayClause {
                        clause: c,
                        context: &self.kernel_context,
                    }
                    .to_string())
                    .collect::<Vec<String>>()
                    .join("\n")
            );
        }
        for (i, clause) in actual.iter().enumerate() {
            self.check_denormalize_renormalize(clause);
            let c = DisplayClause {
                clause,
                context: &self.kernel_context,
            };
            let a = c.to_string();
            if a != expected[i] {
                panic!("expected clause {} to be:\n{}\ngot:\n{}", i, expected[i], a);
            }
        }
    }

    /// Checks a theorem. Just for testing purposes.
    #[cfg(test)]
    pub fn check(
        &mut self,
        env: &crate::elaborator::environment::Environment,
        name: &str,
        expected: &[&str],
    ) {
        for node in &env.nodes {
            if let Some((theorem_name, value)) = node.as_theorem() {
                if theorem_name == name {
                    self.check_value(&value, expected);
                    return;
                }
            }
        }
        panic!("no theorem named {}", name);
    }

    /// Returns all normalized clauses from the environment. Just for testing purposes.
    #[cfg(test)]
    pub fn get_all_clauses(
        &mut self,
        env: &crate::elaborator::environment::Environment,
    ) -> Vec<crate::kernel::clause::Clause> {
        let mut clauses = vec![];
        for node in &env.nodes {
            if let Some(fact) = node.get_fact() {
                if let Ok(normalized) = self.normalize_fact(&fact) {
                    for step in normalized.steps {
                        clauses.push(step.clause);
                    }
                }
            }
        }
        clauses
    }
}
