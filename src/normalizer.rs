use std::collections::HashMap;
use std::sync::Arc;

use crate::builder::BuildError;
use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::ConstantInstance;
use crate::elaborator::acorn_value::{AcornValue, BinaryOp, MatchCase};
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::elaborator::synthetic::{SyntheticDefinition, SyntheticRegistry};
use crate::elaborator::to_term::build_type_var_map;
use crate::elaborator::to_term::elaborate_value_to_term;
use crate::elaborator::to_term::elaborate_value_to_term_existing;
use crate::kernel::atom::{Atom, AtomId, INVALID_SYNTHETIC_MODULE};
use crate::kernel::clause::Clause;
use crate::kernel::cnf::Cnf;
use crate::kernel::extended_term::ExtendedTerm;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, Truthiness};
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::module::ModuleId;
use tracing::trace;

/// A fact that has been normalized into proof steps.
#[derive(Clone)]
pub struct NormalizedFact {
    pub steps: Vec<ProofStep>,
    pub normalizer: Normalizer,
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
        &mut self,
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

        let term =
            elaborate_value_to_term_existing(&mut self.kernel_context, &alt_value, type_var_map)
                .ok()?;
        let mut view = NormalizationContext::new_mut(self, type_var_map.cloned(), ModuleId(0));
        let Ok(uninstantiated) = view.term_to_denormalized_clauses(&term) else {
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
    /// Used to combine normalized state from dependencies.
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

    /// Term-native normalization path.
    ///
    /// This normalizes an elaborated kernel `Term` directly to clauses.
    pub fn nice_term_to_clauses(
        &mut self,
        term: &Term,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
    ) -> Result<Vec<Clause>, String> {
        let mut stack = vec![];
        let mut local_context = LocalContext::empty();

        let (mut next_var_id, num_type_params) = if let Some(type_var_map) = self.type_var_map() {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (_, var_type) in entries {
                local_context.push_type(var_type.clone());
            }
            (type_var_map.len() as AtomId, type_var_map.len())
        } else {
            (0, 0)
        };

        let cnf = self.term_to_cnf(
            term,
            false,
            &mut stack,
            &mut next_var_id,
            synthesized,
            &mut local_context,
        )?;
        let clauses = cnf.into_clauses_with_pinned(&local_context, num_type_params);

        if self.has_uninhabited_existential_witness(synthesized, &clauses) {
            return Err("exists over a potentially uninhabited type".to_string());
        }

        if self.has_uninhabited_dropped_variable(&local_context, &clauses, num_type_params) {
            return Ok(vec![]);
        }

        Ok(clauses)
    }

    /// If `term` is exactly `symbol(arg1, ..., argN)`, return those arguments.
    ///
    /// We require full application so callers can rely on fixed arity for builtins.
    fn split_symbol_application(
        &self,
        term: &Term,
        symbol: Symbol,
        arity: usize,
    ) -> Option<Vec<Term>> {
        let (head, args) = term.as_ref().split_application_multi()?;
        if args.len() != arity {
            return None;
        }
        match head.get_head_atom() {
            Atom::Symbol(s) if *s == symbol => Some(args),
            _ => None,
        }
    }

    /// If `term` is a lowered datatype eliminator application (`Type.match`),
    /// return `(type_args, scrutinee, cases)` in constructor order.
    fn split_match_eliminator_application(
        &self,
        term: &Term,
    ) -> Option<(Vec<Term>, Term, Vec<(Symbol, Term)>)> {
        let (head, args) = term.as_ref().split_application_multi()?;
        let Atom::Symbol(match_symbol) = head.get_head_atom() else {
            return None;
        };
        let info = self
            .symbol_table()
            .get_match_eliminator_info(*match_symbol)?;
        let match_type = self.symbol_table().get_type(*match_symbol);
        let num_type_args = match_type.as_ref().count_type_params();
        let num_cases = info.constructor_symbols.len();
        if args.len() != num_type_args + 1 + num_cases {
            return None;
        }

        let type_args = args[..num_type_args].to_vec();
        let scrutinee = args[num_type_args].clone();
        let mut cases = Vec::with_capacity(num_cases);
        for (ctor, case_term) in info
            .constructor_symbols
            .iter()
            .zip(args[(num_type_args + 1)..].iter())
        {
            cases.push((*ctor, case_term.clone()));
        }
        Some((type_args, scrutinee, cases))
    }

    /// Open a binder body by replacing bound variable 0 with `replacement`.
    ///
    /// This is the de Bruijn "open" operation: substitute first, then shift down.
    fn open_binder_body(&self, body: &Term, replacement: &Term) -> Term {
        body.substitute_bound(0, replacement).shift_bound(0, -1)
    }

    /// Apply arguments by instantiating leading binders (lambda/forall/exists)
    /// before falling back to ordinary term application.
    ///
    /// Returns `(applied_term, consumed_count)` where `consumed_count` is the
    /// number of arguments consumed by binder instantiation.
    fn instantiate_binder_prefix(&self, function: &Term, args: &[Term]) -> (Term, usize) {
        let mut current = function.clone();
        let mut consumed = 0usize;
        while consumed < args.len() {
            match current.as_ref().decompose() {
                crate::kernel::term::Decomposition::Lambda(_, body)
                | crate::kernel::term::Decomposition::ForAll(_, body)
                | crate::kernel::term::Decomposition::Exists(_, body) => {
                    current = self.open_binder_body(&body.to_owned(), &args[consumed]);
                    consumed += 1;
                }
                _ => break,
            }
        }
        if consumed < args.len() {
            current = current.apply(&args[consumed..]);
        }
        (current, consumed)
    }

    /// Abstract a specific free variable into a new outer binder.
    ///
    /// This both:
    /// 1. Replaces `FreeVariable(var_id)` with `BoundVariable(depth)`, and
    /// 2. Shifts existing bound variables to make room for that new binder.
    fn abstract_free_var_as_bound_at_depth(&self, term: &Term, var_id: AtomId, depth: u16) -> Term {
        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::Atom(atom) => match atom {
                Atom::FreeVariable(i) if *i == var_id => Term::atom(Atom::BoundVariable(depth)),
                Atom::BoundVariable(i) if *i >= depth => Term::atom(Atom::BoundVariable(*i + 1)),
                _ => term.clone(),
            },
            crate::kernel::term::Decomposition::Application(func, arg) => {
                let new_func =
                    self.abstract_free_var_as_bound_at_depth(&func.to_owned(), var_id, depth);
                let new_arg =
                    self.abstract_free_var_as_bound_at_depth(&arg.to_owned(), var_id, depth);
                new_func.apply(&[new_arg])
            }
            crate::kernel::term::Decomposition::Pi(input, output) => {
                let new_input =
                    self.abstract_free_var_as_bound_at_depth(&input.to_owned(), var_id, depth);
                let new_output =
                    self.abstract_free_var_as_bound_at_depth(&output.to_owned(), var_id, depth + 1);
                Term::pi(new_input, new_output)
            }
            crate::kernel::term::Decomposition::Lambda(input, body) => {
                let new_input =
                    self.abstract_free_var_as_bound_at_depth(&input.to_owned(), var_id, depth);
                let new_body =
                    self.abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::lambda(new_input, new_body)
            }
            crate::kernel::term::Decomposition::ForAll(binder_type, body) => {
                let new_binder_type = self.abstract_free_var_as_bound_at_depth(
                    &binder_type.to_owned(),
                    var_id,
                    depth,
                );
                let new_body =
                    self.abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::forall(new_binder_type, new_body)
            }
            crate::kernel::term::Decomposition::Exists(binder_type, body) => {
                let new_binder_type = self.abstract_free_var_as_bound_at_depth(
                    &binder_type.to_owned(),
                    var_id,
                    depth,
                );
                let new_body =
                    self.abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::exists(new_binder_type, new_body)
            }
        }
    }

    /// Like `Term::get_type_with_context`, but supports lambda terms.
    ///
    /// Lambda type computation opens one binder at a time with a fresh free variable,
    /// computes the body type recursively, then abstracts that variable back into a Pi.
    fn term_type_for_normalization(&self, term: &Term, context: &LocalContext) -> Term {
        if let Some((input, body)) = term.as_ref().split_lambda() {
            let input_type = input.to_owned();
            let fresh_var = context.len() as AtomId;
            let mut nested_context = context.clone();
            nested_context.push_type(input_type.clone());
            let opened_body =
                self.open_binder_body(&body.to_owned(), &Term::new_variable(fresh_var));
            let body_type = self.term_type_for_normalization(&opened_body, &nested_context);
            let output_type = self.abstract_free_var_as_bound_at_depth(&body_type, fresh_var, 0);
            Term::pi(input_type, output_type)
        } else {
            term.get_type_with_context(context, self.kernel_context())
        }
    }

    /// Term-native CNF conversion.
    ///
    /// This converts an elaborated kernel `Term` into CNF.
    /// `true` is `[]`, `false` is `[[]]`, and we intentionally leave tautologies
    /// and redundancy for later clause normalization.
    ///
    /// The `stack` plays the same role as in value normalization:
    /// `TermBinding::Free` tracks forall-introduced variables and
    /// `TermBinding::Bound` tracks existential/skolem substitutions.
    fn term_to_cnf(
        &mut self,
        term: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::ForAll(binder_type, body) => {
                if !negate {
                    self.forall_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                } else {
                    self.exists_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                }
            }
            crate::kernel::term::Decomposition::Exists(binder_type, body) => {
                if !negate {
                    self.exists_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                } else {
                    self.forall_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                }
            }
            _ => {
                // Builtin logical atoms are recognized by head symbol + arity.
                if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
                    return self.term_to_cnf(&args[0], !negate, stack, next_var_id, synth, context);
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::And, 2) {
                    if !negate {
                        return self.term_and_to_cnf(
                            &args[0],
                            &args[1],
                            false,
                            false,
                            stack,
                            next_var_id,
                            synth,
                            context,
                        );
                    }
                    return self.term_or_to_cnf(
                        &args[0],
                        &args[1],
                        true,
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Or, 2) {
                    if !negate {
                        return self.term_or_to_cnf(
                            &args[0],
                            &args[1],
                            false,
                            false,
                            stack,
                            next_var_id,
                            synth,
                            context,
                        );
                    }
                    return self.term_and_to_cnf(
                        &args[0],
                        &args[1],
                        true,
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Eq, 3) {
                    return self.term_eq_to_cnf(
                        &args[1],
                        &args[2],
                        negate,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
                    let cond_cnf =
                        self.term_to_cnf(&args[1], false, stack, next_var_id, synth, context)?;
                    let Some(cond_lit) = cond_cnf.to_literal() else {
                        return Err("term 'ite' condition is too complicated".to_string());
                    };
                    let then_cnf =
                        self.term_to_cnf(&args[2], negate, stack, next_var_id, synth, context)?;
                    let else_cnf =
                        self.term_to_cnf(&args[3], negate, stack, next_var_id, synth, context)?;
                    return Ok(Cnf::cnf_if(cond_lit, then_cnf, else_cnf));
                }

                if let Some((function, args)) = term.as_ref().split_application_multi() {
                    match function.as_ref().decompose() {
                        crate::kernel::term::Decomposition::Lambda(_, _)
                        | crate::kernel::term::Decomposition::ForAll(_, _)
                        | crate::kernel::term::Decomposition::Exists(_, _) => {
                            let (applied, consumed) =
                                self.instantiate_binder_prefix(&function.to_owned(), &args);
                            for arg in args.iter().take(consumed) {
                                stack.push(TermBinding::Bound(arg.clone()));
                            }
                            let answer = self.term_to_cnf(
                                &applied,
                                negate,
                                stack,
                                next_var_id,
                                synth,
                                context,
                            );
                            stack.truncate(stack.len().saturating_sub(consumed));
                            return answer;
                        }
                        _ => {}
                    }
                }

                if term == &Term::new_true() {
                    return if negate {
                        Ok(Cnf::false_value())
                    } else {
                        Ok(Cnf::true_value())
                    };
                }
                if term == &Term::new_false() {
                    return if negate {
                        Ok(Cnf::true_value())
                    } else {
                        Ok(Cnf::false_value())
                    };
                }

                // Everything else must normalize to a single signed literal.
                let simple_term =
                    self.term_to_simple_term(term, stack, next_var_id, synth, context)?;
                let literal = Literal::from_signed_term(simple_term, !negate);
                Ok(Cnf::from_literal(literal))
            }
        }
    }

    fn forall_term_to_cnf(
        &mut self,
        binder_type: &Term,
        body: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let var_id = *next_var_id;
        *next_var_id += 1;
        context.push_type(binder_type.clone());
        let var = Term::new_variable(var_id);
        stack.push(TermBinding::Free(var.clone()));
        let opened_body = self.open_binder_body(body, &var);
        let result = self.term_to_cnf(
            &opened_body,
            negate,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        stack.pop();
        Ok(result)
    }

    fn exists_term_to_cnf(
        &mut self,
        binder_type: &Term,
        body: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let skolem_terms = self.make_skolem_terms_from_type_terms(
            std::slice::from_ref(binder_type),
            stack,
            synthesized,
            context,
        )?;
        let skolem_term = skolem_terms.into_iter().next().unwrap();
        stack.push(TermBinding::Bound(skolem_term.clone()));
        let opened_body = self.open_binder_body(body, &skolem_term);
        let result = self.term_to_cnf(
            &opened_body,
            negate,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        stack.pop();
        Ok(result)
    }

    fn make_skolem_terms_from_type_terms(
        &mut self,
        skolem_type_terms: &[Term],
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Vec<Term>, String> {
        let mut args = vec![];
        let mut arg_type_terms: Vec<Term> = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        if let Some(type_var_map) = self.type_var_map() {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (var_id, var_type) in entries {
                let var_term = Term::new_variable(*var_id);
                args.push(var_term);
                arg_type_terms.push(var_type.clone());
                seen_vars.insert(*var_id);
            }
        }

        for binding in stack.iter() {
            for (var_id, closed_type) in binding.term().collect_vars(context) {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(var_id);
                    args.push(var_term);
                    arg_type_terms.push(closed_type);
                }
            }
        }

        let num_type_params = self.type_var_map().map_or(0, |m| m.len()) as u16;
        let mut non_type_param_index = 0u16;
        let arg_type_terms: Vec<Term> = arg_type_terms
            .into_iter()
            .map(|t| {
                if t.as_ref().is_type_param_kind() {
                    t
                } else {
                    let depth = non_type_param_index;
                    non_type_param_index += 1;
                    t.convert_free_to_bound_with_depth(num_type_params, depth)
                }
            })
            .collect();

        let mut output = vec![];
        for t in skolem_type_terms {
            let non_type_param_args = arg_type_terms.len() - num_type_params as usize;
            let result_type_term =
                t.convert_free_to_bound_with_depth(num_type_params, non_type_param_args as u16);

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

    fn make_skolem_term_from_type_term(
        &mut self,
        skolem_type_term: &Term,
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Term, String> {
        let mut terms = self.make_skolem_terms_from_type_terms(
            std::slice::from_ref(skolem_type_term),
            stack,
            synthesized,
            context,
        )?;
        Ok(terms.pop().unwrap())
    }

    fn term_and_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left = self.term_to_cnf(left, negate_left, stack, next_var_id, synthesized, context)?;
        let right = self.term_to_cnf(
            right,
            negate_right,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        Ok(left.and(right))
    }

    fn term_or_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left = self.term_to_cnf(left, negate_left, stack, next_var_id, synthesized, context)?;
        let right = self.term_to_cnf(
            right,
            negate_right,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        Ok(left.or(right))
    }

    fn try_simple_term_to_term(&self, term: &Term) -> Result<Option<Term>, String> {
        match self.try_simple_term_to_signed_term(term)? {
            Some((t, true)) => Ok(Some(t)),
            Some((_t, false)) => Ok(None),
            None => Ok(None),
        }
    }

    fn try_simple_term_to_signed_term(&self, term: &Term) -> Result<Option<(Term, bool)>, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
            return match self.try_simple_term_to_signed_term(&args[0])? {
                None => Ok(None),
                Some((t, sign)) => Ok(Some((t, !sign))),
            };
        }

        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _)
            | crate::kernel::term::Decomposition::Lambda(_, _) => Ok(None),
            _ => {
                if term == &Term::new_true() {
                    return Ok(Some((Term::new_true(), true)));
                }
                if term == &Term::new_false() {
                    return Ok(Some((Term::new_true(), false)));
                }

                if self
                    .split_symbol_application(term, Symbol::And, 2)
                    .is_some()
                    || self.split_symbol_application(term, Symbol::Or, 2).is_some()
                    || self.split_symbol_application(term, Symbol::Eq, 3).is_some()
                    || self
                        .split_symbol_application(term, Symbol::Ite, 4)
                        .is_some()
                {
                    return Ok(None);
                }

                if let Some((function, arg_terms)) = term.as_ref().split_application_multi() {
                    let function = function.to_owned();
                    let func_term = match self.try_simple_term_to_term(&function)? {
                        Some(t) => t,
                        None => return Ok(None),
                    };
                    let head = *func_term.get_head_atom();
                    let mut args = func_term.args().to_vec();
                    for arg in arg_terms {
                        let arg_term = match self.try_simple_term_to_term(&arg)? {
                            Some(t) => t,
                            None => return Ok(None),
                        };
                        args.push(arg_term);
                    }
                    return Ok(Some((Term::new(head, args), true)));
                }

                Ok(Some((term.clone(), true)))
            }
        }
    }

    fn apply_term_to_cnf(
        &mut self,
        function: &Term,
        args: Vec<ExtendedTerm>,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        match function.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(_, _)
            | crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _) => {
                let mut arg_terms = Vec::with_capacity(args.len());
                for arg in args {
                    arg_terms.push(arg.to_term()?);
                }
                let (applied, consumed) = self.instantiate_binder_prefix(function, &arg_terms);
                for arg in arg_terms.iter().take(consumed) {
                    stack.push(TermBinding::Bound(arg.clone()));
                }
                let answer =
                    self.term_to_cnf(&applied, negate, stack, next_var_id, synthesized, context);
                stack.truncate(stack.len().saturating_sub(consumed));
                return answer;
            }
            _ => {}
        }

        let extended = self.apply_term_to_extended_term(
            function,
            args,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        match extended {
            ExtendedTerm::Term(term) => {
                let literal = Literal::from_signed_term(term, !negate);
                Ok(Cnf::from_literal(literal))
            }
            _ => Err("unhandled case: non-term application".to_string()),
        }
    }

    /// Convert `left = right` (or `!=` when `negate`) to CNF.
    ///
    /// For function-typed terms, this performs extensional reasoning by applying
    /// either fresh variables (`forall`-style) or skolems (`exists`-style) to both
    /// sides, then reducing to equality on results.
    fn term_eq_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        if let Some((type_args, scrutinee, cases)) = self.split_match_eliminator_application(right)
        {
            let datatype_type_args = type_args[..type_args.len().saturating_sub(1)].to_vec();
            let mut answer = Cnf::true_value();
            for (constructor_symbol, case_term) in &cases {
                let mut constructor_args = datatype_type_args.clone();
                let mut case_value = case_term.clone();
                let stack_len = stack.len();

                while let Some((input, body)) = case_value.as_ref().split_lambda() {
                    let input_type = input.to_owned();
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(input_type.clone());
                    let var = Term::new_variable(var_id);
                    constructor_args.push(var.clone());
                    stack.push(TermBinding::Free(var.clone()));
                    case_value = self.open_binder_body(&body.to_owned(), &var);
                }

                let pattern = Term::new(Atom::Symbol(*constructor_symbol), constructor_args);
                let condition = self.term_eq_to_cnf(
                    &scrutinee,
                    &pattern,
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let conclusion = self.term_eq_to_cnf(
                    left,
                    &case_value,
                    negate,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                answer = answer.and(condition.negate().or(conclusion));

                stack.truncate(stack_len);
            }
            return Ok(answer);
        }

        if let Some((type_args, scrutinee, cases)) = self.split_match_eliminator_application(left) {
            let datatype_type_args = type_args[..type_args.len().saturating_sub(1)].to_vec();
            let mut answer = Cnf::true_value();
            for (constructor_symbol, case_term) in &cases {
                let mut constructor_args = datatype_type_args.clone();
                let mut case_value = case_term.clone();
                let stack_len = stack.len();

                while let Some((input, body)) = case_value.as_ref().split_lambda() {
                    let input_type = input.to_owned();
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(input_type.clone());
                    let var = Term::new_variable(var_id);
                    constructor_args.push(var.clone());
                    stack.push(TermBinding::Free(var.clone()));
                    case_value = self.open_binder_body(&body.to_owned(), &var);
                }

                let pattern = Term::new(Atom::Symbol(*constructor_symbol), constructor_args);
                let condition = self.term_eq_to_cnf(
                    &scrutinee,
                    &pattern,
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let conclusion = self.term_eq_to_cnf(
                    right,
                    &case_value,
                    negate,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                answer = answer.and(condition.negate().or(conclusion));

                stack.truncate(stack_len);
            }
            return Ok(answer);
        }

        let left_type = self.term_type_for_normalization(left, context);
        let mut fn_arg_types = vec![];
        let mut result_type = left_type.clone();
        while let Some((input, output)) = result_type.as_ref().split_pi() {
            fn_arg_types.push(input.to_owned());
            result_type = output.to_owned();
        }

        if !fn_arg_types.is_empty() {
            if result_type == Term::bool_type() {
                if negate {
                    // f != g for Bool-valued functions:
                    // skolemize an argument tuple and assert result disagreement.
                    let arg_terms = self.make_skolem_terms_from_type_terms(
                        &fn_arg_types,
                        stack,
                        synth,
                        context,
                    )?;
                    let args: Vec<_> = arg_terms.iter().cloned().map(ExtendedTerm::Term).collect();
                    let left_pos = self.apply_term_to_cnf(
                        left,
                        args.clone(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let left_neg = self.apply_term_to_cnf(
                        left,
                        args.clone(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let right_pos = self.apply_term_to_cnf(
                        right,
                        args.clone(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let right_neg = self.apply_term_to_cnf(
                        right,
                        args,
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;

                    if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                        if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg)
                        {
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

                // f = g for Bool-valued functions:
                // introduce fresh universally-quantified arguments.
                let mut args = vec![];
                for arg_type_term in &fn_arg_types {
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(arg_type_term.clone());
                    args.push(ExtendedTerm::Term(Term::new_variable(var_id)));
                }
                let left_pos = self.apply_term_to_cnf(
                    left,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let left_neg = self.apply_term_to_cnf(
                    left,
                    args.clone(),
                    true,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let right_pos = self.apply_term_to_cnf(
                    right,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let right_neg =
                    self.apply_term_to_cnf(right, args, true, stack, next_var_id, synth, context)?;

                if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                    if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg) {
                        let positive = left_sign == right_sign;
                        let literal = Literal::new(positive, left_term.clone(), right_term.clone());
                        return Ok(Cnf::from_literal(literal));
                    }
                }

                let l_imp_r = left_neg.or(right_pos);
                let r_imp_l = left_pos.or(right_neg);
                return Ok(l_imp_r.and(r_imp_l));
            }

            let left = self.term_to_extended_term(left, stack, next_var_id, synth, context)?;
            let right = self.term_to_extended_term(right, stack, next_var_id, synth, context)?;
            if negate {
                let args =
                    self.make_skolem_terms_from_type_terms(&fn_arg_types, stack, synth, context)?;
                return left.apply(&args).eq_to_cnf(right.apply(&args), true);
            }

            let mut args = vec![];
            for arg_type_term in &fn_arg_types {
                let var_id = *next_var_id;
                *next_var_id += 1;
                context.push_type(arg_type_term.clone());
                args.push(Term::new_variable(var_id));
            }
            return left.apply(&args).eq_to_cnf(right.apply(&args), false);
        }

        if left_type == Term::bool_type() {
            if let Some((left_term, left_sign)) = self.try_simple_term_to_signed_term(left)? {
                if let Some((right_term, right_sign)) =
                    self.try_simple_term_to_signed_term(right)?
                {
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(Cnf::from_literal(literal));
                }
            }

            if negate {
                let some = self.term_or_to_cnf(
                    left,
                    right,
                    true,
                    true,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let not_both = self.term_or_to_cnf(
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

            let l_imp_r =
                self.term_or_to_cnf(left, right, true, false, stack, next_var_id, synth, context)?;
            let r_imp_l =
                self.term_or_to_cnf(left, right, false, true, stack, next_var_id, synth, context)?;
            return Ok(l_imp_r.and(r_imp_l));
        }

        let left = self.term_to_extended_term(left, stack, next_var_id, synth, context)?;
        let right = self.term_to_extended_term(right, stack, next_var_id, synth, context)?;
        left.eq_to_cnf(right, negate)
    }

    fn synthesize_term_from_term(
        &mut self,
        value: &Term,
        value_type: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Term, String> {
        let skolem_term =
            self.make_skolem_term_from_type_term(value_type, stack, synth, context)?;
        let skolem_id = if let Atom::Symbol(Symbol::Synthetic(m, id)) = *skolem_term.get_head_atom()
        {
            (m, id)
        } else {
            return Err("internal error: skolem term is not synthetic".to_string());
        };

        let synthetic_type = self
            .kernel_context()
            .symbol_table
            .get_type(Symbol::Synthetic(skolem_id.0, skolem_id.1))
            .clone();

        let definition_cnf = self.term_eq_to_cnf(
            &skolem_term,
            value,
            false,
            stack,
            next_var_id,
            synth,
            context,
        )?;

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
            let (existing_m, existing_id) = existing_def.atoms[0];
            let existing_atom = Atom::Symbol(Symbol::Synthetic(existing_m, existing_id));
            Ok(Term::new(existing_atom, skolem_term.args().to_vec()))
        } else {
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

    fn arg_term_to_extended(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if term.as_ref().is_lambda() {
            let lambda_type = self.term_type_for_normalization(term, context);
            let skolem_term = self.synthesize_term_from_term(
                term,
                &lambda_type,
                stack,
                next_var_id,
                synth,
                context,
            )?;
            return Ok(ExtendedTerm::Term(skolem_term));
        }

        // For boolean arguments, synthesize non-simple formulas
        // (and/or/eq/not/forall/exists/match/etc) into atoms.
        let term_type = self.term_type_for_normalization(term, context);
        if term_type == Term::bool_type() && self.try_simple_term_to_term(term)?.is_none() {
            let skolem_term = self.synthesize_term_from_term(
                term,
                &Term::bool_type(),
                stack,
                next_var_id,
                synth,
                context,
            )?;
            return Ok(ExtendedTerm::Term(skolem_term));
        }

        self.term_to_extended_term(term, stack, next_var_id, synth, context)
    }

    /// Apply `function` to `args`, pushing a single conditional outward when possible.
    ///
    /// This preserves the old normalization behavior where
    /// `f(if c then a else b, d)` becomes `if c then f(a, d) else f(b, d)`.
    fn apply_term_to_extended_term(
        &mut self,
        function: &Term,
        args: Vec<ExtendedTerm>,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if function.as_ref().is_lambda() {
            let func_ext =
                self.term_to_extended_term(function, stack, next_var_id, synth, context)?;
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(self.extended_term_to_term(arg, context, synth)?);
            }
            return Ok(func_ext.apply(&arg_terms));
        }

        let mut cond: Option<Literal> = None;
        let mut spine1 = vec![];
        let mut spine2 = vec![];

        match self.term_to_extended_term(function, stack, next_var_id, synth, context)? {
            ExtendedTerm::Term(t) => {
                spine1.push(t);
            }
            ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                cond = Some(sub_cond);
                spine1.push(sub_then);
                spine2.push(sub_else);
            }
            ExtendedTerm::Lambda(_, _) => {
                return Err("unhandled case: secret lambda".to_string());
            }
        }

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
                        return Err("unhandled case: multiple ite args".to_string());
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

        match cond {
            Some(cond) => {
                assert_eq!(spine1.len(), spine2.len());
                let then_term = Term::from_spine(spine1);
                let else_term = Term::from_spine(spine2);
                Ok(ExtendedTerm::If(cond, then_term, else_term))
            }
            None => {
                assert!(spine2.is_empty());
                Ok(ExtendedTerm::Term(Term::from_spine(spine1)))
            }
        }
    }

    /// Convert a term into `ExtendedTerm`, introducing synthetic atoms as needed.
    ///
    /// `ExtendedTerm::If` is used as an intermediate form to avoid losing branching
    /// structure before we synthesize a simple term.
    fn term_to_extended_term(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
            let cond_cnf = self.term_to_cnf(&args[1], false, stack, next_var_id, synth, context)?;
            let cond_lit = if cond_cnf.is_literal() {
                cond_cnf.to_literal().unwrap()
            } else {
                self.synthesize_literal_from_cnf(cond_cnf, stack, synth, context)?
            };
            let then_ext =
                self.term_to_extended_term(&args[2], stack, next_var_id, synth, context)?;
            let then_branch = self.extended_term_to_term(then_ext, context, synth)?;
            let else_ext =
                self.term_to_extended_term(&args[3], stack, next_var_id, synth, context)?;
            let else_branch = self.extended_term_to_term(else_ext, context, synth)?;
            return Ok(ExtendedTerm::If(cond_lit, then_branch, else_branch));
        }

        if let Some((function, arg_terms)) = term.as_ref().split_application_multi() {
            let mut arg_exts = vec![];
            for arg in arg_terms {
                arg_exts.push(self.arg_term_to_extended(
                    &arg,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?);
            }
            return self.apply_term_to_extended_term(
                &function,
                arg_exts,
                stack,
                next_var_id,
                synth,
                context,
            );
        }

        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(_, _) => {
                let mut args = vec![];
                let mut current = term.clone();
                while let Some((input, body)) = current.as_ref().split_lambda() {
                    let input_type = input.to_owned();
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(input_type.clone());
                    let var = Term::new_variable(var_id);
                    args.push((var_id, input_type));
                    stack.push(TermBinding::Free(var.clone()));
                    current = self.open_binder_body(&body.to_owned(), &var);
                }

                let body_ext =
                    self.term_to_extended_term(&current, stack, next_var_id, synth, context)?;
                let body_term = self.extended_term_to_term(body_ext, context, synth)?;

                for _ in 0..args.len() {
                    stack.pop();
                }
                Ok(ExtendedTerm::Lambda(args, body_term))
            }
            crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _) => {
                Err(format!("quantifier in unexpected term position: {}", term))
            }
            _ => {
                if term == &Term::new_false() {
                    return Err("false literal in unexpected position".to_string());
                }
                if term == &Term::new_true() {
                    return Ok(ExtendedTerm::Term(Term::new_true()));
                }

                let term_type = self.term_type_for_normalization(term, context);
                if term_type == Term::bool_type() {
                    if let Some(simple) = self.try_simple_term_to_term(term)? {
                        return Ok(ExtendedTerm::Term(simple));
                    }
                    let skolem_term = self.synthesize_term_from_term(
                        term,
                        &Term::bool_type(),
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    Ok(ExtendedTerm::Term(skolem_term))
                } else {
                    Ok(ExtendedTerm::Term(term.clone()))
                }
            }
        }
    }

    fn term_to_simple_term(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Term, String> {
        if let Some(simple) = self.try_simple_term_to_term(term)? {
            return Ok(simple);
        }
        let ext = self.term_to_extended_term(term, stack, next_var_id, synth, context)?;
        self.extended_term_to_term(ext, context, synth)
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
    pub fn term_to_denormalized_clauses(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
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

        let cnf = self.term_to_cnf(
            term,
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

    /// This returns clauses that are denormalized in the sense that they sort literals,
    /// but don't filter out redundant or tautological literals.
    /// This is the format that the Checker uses.
    /// If you call normalize() on the clause afterwards, you should get the normalized one.
    pub fn value_to_denormalized_clauses(
        &mut self,
        value: &AcornValue,
    ) -> Result<Vec<Clause>, String> {
        let type_var_map = self.type_var_map().cloned();
        let term = elaborate_value_to_term_existing(
            self.as_mut()?.kernel_context_mut(),
            value,
            type_var_map.as_ref(),
        )?;
        self.term_to_denormalized_clauses(&term)
    }

    /// Converts a simple value expression into a kernel term.
    ///
    /// This only succeeds for values that elaborate into a simple term form.
    pub fn value_to_simple_term(&mut self, value: &AcornValue) -> Result<Term, String> {
        let type_var_map = self.type_var_map().cloned();
        let term = elaborate_value_to_term_existing(
            self.as_mut()?.kernel_context_mut(),
            value,
            type_var_map.as_ref(),
        )?;
        match self.try_simple_term_to_signed_term(&term)? {
            Some((term, true)) => Ok(term),
            // `false` is represented as `not true` in signed-term form.
            Some((term, false)) if term == Term::new_true() => Ok(Term::new_false()),
            Some(_) | None => Err(format!(
                "value '{}' cannot be represented as a simple term",
                value
            )),
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

    /// Converts an ExtendedTerm to a simple Term.
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
                let result_type_term = self.term_type_for_normalization(&then_term, local_context);

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
            ExtendedTerm::Lambda(_, t) => {
                Err(format!("cannot convert lambda {} to simple term", t))
            }
        }
    }
}

impl Normalizer {
    /// Normalize a term-level proposition into clauses.
    ///
    /// This is the term-native backend for proposition normalization.
    fn normalize_term(
        &mut self,
        term: &Term,
        _ctype: NewConstantType,
        source: &Source,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        term.validate();

        let mut skolem_ids = vec![];
        let mut mut_view =
            NormalizationContext::new_mut(self, type_var_map.clone(), source.module_id);
        let clauses = mut_view.nice_term_to_clauses(term, &mut skolem_ids)?;

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
            let type_vars: Vec<Term> = if let Some(ref tvm) = type_var_map {
                let mut entries: Vec<_> = tvm.values().collect();
                entries.sort_by_key(|(id, _)| *id);
                entries.iter().map(|(_, kind)| kind.clone()).collect()
            } else {
                vec![]
            };

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

    /// Converts a value proposition to CNF clauses via:
    /// `AcornValue --elaborate--> Term --normalize_term--> Vec<Clause>`.
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

        let term = elaborate_value_to_term(
            &mut self.kernel_context,
            value,
            ctype,
            type_var_map.as_ref(),
        )?;
        self.normalize_term(&term, ctype, source, type_var_map)
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
                let type_var_map = build_type_var_map(&mut self.kernel_context, &type_params);

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

        Ok(NormalizedFact {
            steps,
            normalizer: self.clone(),
        })
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
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        let acorn_type = if atom_type.as_ref().is_atomic() {
            if let Atom::FreeVariable(var_id) = atom_type.as_ref().get_head_atom() {
                let typeclass = local_context
                    .get_var_type(*var_id as usize)
                    .and_then(|t| t.as_ref().as_typeclass())
                    .and_then(|tc_id| self.kernel_context.type_store.get_typeclass_by_id(tc_id))
                    .cloned();
                let name = type_var_id_to_name
                    .and_then(|m| m.get(var_id))
                    .cloned()
                    .unwrap_or_else(|| format!("T{}", var_id));
                AcornType::Variable(TypeParam { name, typeclass })
            } else if let Some(name_map) = type_var_id_to_name {
                self.kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_var_names(atom_type, name_map)
            } else {
                self.kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        atom_type,
                        local_context,
                        instantiate_type_vars,
                    )
            }
        } else if let Some(name_map) = type_var_id_to_name {
            self.kernel_context
                .type_store
                .type_term_to_acorn_type_with_var_names(atom_type, name_map)
        } else {
            self.kernel_context
                .type_store
                .type_term_to_acorn_type_with_context(
                    atom_type,
                    local_context,
                    instantiate_type_vars,
                )
        };
        match atom {
            Atom::Symbol(Symbol::True) => AcornValue::Bool(true),
            Atom::Symbol(Symbol::False) => AcornValue::Bool(false),
            Atom::Symbol(Symbol::Not)
            | Atom::Symbol(Symbol::And)
            | Atom::Symbol(Symbol::Or)
            | Atom::Symbol(Symbol::Eq)
            | Atom::Symbol(Symbol::Ite) => {
                panic!("logical symbols should be handled in denormalize_term")
            }
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
                // Apply remapping if provided. A mapped `None` means this variable should have
                // been eliminated (e.g., type-level variable), so seeing it in a value position
                // indicates a denormalization bug.
                let new_i = if let Some(mapping) = var_remapping {
                    match mapping.get(*i as usize) {
                        Some(Some(mapped)) => *mapped,
                        Some(None) => panic!(
                            "denormalize_atom saw excluded variable x{} in value position",
                            i
                        ),
                        None => *i,
                    }
                } else {
                    *i
                };
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
                panic!(
                    "Type symbols should not appear in open terms (atom={:?}, atom_type={})",
                    atom, atom_type
                )
            }
            Atom::Symbol(Symbol::Typeclass(_)) => {
                panic!("Typeclass atoms should not appear in open terms")
            }
            Atom::BoundVariable(_) => {
                panic!("BoundVariable atoms should not appear in denormalize_atom")
            }
        }
    }

    fn apply_type_args_to_constant(
        constant: &ConstantInstance,
        type_args: &[AcornType],
    ) -> AcornValue {
        if type_args.is_empty() {
            return AcornValue::Constant(constant.clone());
        }
        let params_to_apply = constant.type_param_names.len().min(type_args.len());
        let params: Vec<AcornType> = type_args.iter().take(params_to_apply).cloned().collect();
        let named_params: Vec<_> = constant
            .type_param_names
            .iter()
            .take(params_to_apply)
            .zip(params.iter())
            .map(|(name, ty)| (name.clone(), ty.clone()))
            .collect();
        let instance_type = constant.generic_type.instantiate(&named_params);
        AcornValue::Constant(ConstantInstance {
            name: constant.name.clone(),
            params,
            instance_type,
            generic_type: constant.generic_type.clone(),
            type_param_names: constant.type_param_names.clone(),
        })
    }

    fn instantiate_symbol_for_match(
        &self,
        symbol: Symbol,
        type_args: &[AcornType],
    ) -> Option<AcornValue> {
        let name = match symbol {
            Symbol::GlobalConstant(module_id, atom_id) => self
                .kernel_context
                .symbol_table
                .name_for_global_id(module_id, atom_id)
                .clone(),
            Symbol::ScopedConstant(atom_id) => self
                .kernel_context
                .symbol_table
                .name_for_local_id(atom_id)
                .clone(),
            _ => return None,
        };

        if let Some(poly) = self.kernel_context.symbol_table.get_polymorphic_info(&name) {
            let params_to_apply = poly.type_param_names.len().min(type_args.len());
            let params: Vec<AcornType> = type_args.iter().take(params_to_apply).cloned().collect();
            let named_params: Vec<_> = poly
                .type_param_names
                .iter()
                .take(params_to_apply)
                .zip(params.iter())
                .map(|(param_name, ty)| (param_name.clone(), ty.clone()))
                .collect();
            let instance_type = poly.generic_type.instantiate(&named_params);
            return Some(AcornValue::constant(
                name.clone(),
                params,
                instance_type,
                poly.generic_type.clone(),
                poly.type_param_names.clone(),
            ));
        }

        let symbol_type = self
            .kernel_context
            .symbol_table
            .get_symbol_type(symbol, &self.kernel_context.type_store);
        let acorn_type = self
            .kernel_context
            .type_store
            .type_term_to_acorn_type(&symbol_type);
        Some(AcornValue::constant(
            name.clone(),
            vec![],
            acorn_type.clone(),
            acorn_type,
            vec![],
        ))
    }

    fn maybe_reconstruct_match(
        &self,
        head: &AcornValue,
        type_args: &[AcornType],
        value_args: &[AcornValue],
        local_context: &LocalContext,
        var_remapping: Option<&[Option<u16>]>,
    ) -> Option<AcornValue> {
        let AcornValue::Constant(constant) = head else {
            return None;
        };
        let match_symbol = self
            .kernel_context
            .symbol_table
            .get_symbol(&constant.name)?;
        let info = self
            .kernel_context
            .symbol_table
            .get_match_eliminator_info(match_symbol)?;
        if value_args.len() != info.constructor_symbols.len() + 1 {
            return None;
        }

        let scrutinee = value_args[0].clone();
        let constructor_total = u16::try_from(info.constructor_symbols.len()).ok()?;
        let first_new_var_id = local_context.len() as AtomId;
        let mut cases = vec![];

        for (constructor_index, (constructor_symbol, branch_value)) in info
            .constructor_symbols
            .iter()
            .zip(value_args.iter().skip(1))
            .enumerate()
        {
            let (new_vars, result) = match branch_value.clone() {
                AcornValue::Lambda(args, body) => (args, *body),
                other => (vec![], other),
            };

            let constructor = self.instantiate_symbol_for_match(*constructor_symbol, type_args)?;
            let pattern = if new_vars.is_empty() {
                constructor
            } else {
                let mut pattern_args = vec![];
                for (i, var_type) in new_vars.iter().enumerate() {
                    let original_var_id = first_new_var_id + i as AtomId;
                    let remapped_id = var_remapping
                        .and_then(|mapping| mapping.get(original_var_id as usize))
                        .and_then(|mapped| *mapped)
                        .unwrap_or(original_var_id);
                    pattern_args.push(AcornValue::Variable(remapped_id, var_type.clone()));
                }
                AcornValue::apply(constructor, pattern_args)
            };

            cases.push(MatchCase {
                new_vars,
                pattern,
                result,
                constructor_index: constructor_index as u16,
                constructor_total,
            });
        }

        Some(AcornValue::Match(Box::new(scrutinee), cases))
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
        fn reduce_head_lambda_application(term: &Term) -> Option<Term> {
            use crate::kernel::term::Decomposition;

            match term.as_ref().decompose() {
                Decomposition::Application(func, arg) => match func.decompose() {
                    Decomposition::Lambda(_, body) => Some(
                        body.to_owned()
                            .substitute_bound(0, &arg.to_owned())
                            .shift_bound(0, -1),
                    ),
                    _ => reduce_head_lambda_application(&func.to_owned())
                        .map(|reduced_func| reduced_func.apply(&[arg.to_owned()])),
                },
                _ => None,
            }
        }

        if let Some(reduced) = reduce_head_lambda_application(term) {
            return self.denormalize_term(
                &reduced,
                local_context,
                arbitrary_names,
                var_remapping,
                type_param_names,
                type_var_id_to_name,
                instantiate_type_vars,
            );
        }

        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(input, body) => {
                let input_term = input.to_owned();
                let input_type = self
                    .kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        &input_term,
                        local_context,
                        instantiate_type_vars,
                    );

                let mut next_context = local_context.clone();
                let fresh_var = next_context.push_type(input_term) as AtomId;
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                );
                return match body_value {
                    AcornValue::Lambda(mut args, body) => {
                        args.insert(0, input_type);
                        AcornValue::Lambda(args, body)
                    }
                    other => AcornValue::Lambda(vec![input_type], Box::new(other)),
                };
            }
            crate::kernel::term::Decomposition::ForAll(binder_type, body) => {
                let binder_type_term = binder_type.to_owned();
                let binder_acorn_type = self
                    .kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        &binder_type_term,
                        local_context,
                        instantiate_type_vars,
                    );

                let mut next_context = local_context.clone();
                let fresh_var = next_context.push_type(binder_type_term) as AtomId;
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                );
                return match body_value {
                    AcornValue::ForAll(mut quants, body) => {
                        quants.insert(0, binder_acorn_type);
                        AcornValue::ForAll(quants, body)
                    }
                    other => AcornValue::ForAll(vec![binder_acorn_type], Box::new(other)),
                };
            }
            crate::kernel::term::Decomposition::Exists(binder_type, body) => {
                let binder_type_term = binder_type.to_owned();
                let binder_acorn_type = self
                    .kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        &binder_type_term,
                        local_context,
                        instantiate_type_vars,
                    );

                let mut next_context = local_context.clone();
                let fresh_var = next_context.push_type(binder_type_term) as AtomId;
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                );
                return match body_value {
                    AcornValue::Exists(mut quants, body) => {
                        quants.insert(0, binder_acorn_type);
                        AcornValue::Exists(quants, body)
                    }
                    other => AcornValue::Exists(vec![binder_acorn_type], Box::new(other)),
                };
            }
            crate::kernel::term::Decomposition::Atom(_)
            | crate::kernel::term::Decomposition::Application(_, _)
            | crate::kernel::term::Decomposition::Pi(_, _) => {}
        }

        let logical_head_symbol = match term.get_head_atom() {
            Atom::Symbol(Symbol::Not) => Some(Symbol::Not),
            Atom::Symbol(Symbol::And) => Some(Symbol::And),
            Atom::Symbol(Symbol::Or) => Some(Symbol::Or),
            Atom::Symbol(Symbol::Eq) => Some(Symbol::Eq),
            Atom::Symbol(Symbol::Ite) => Some(Symbol::Ite),
            _ => None,
        };

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

        let head = logical_head_symbol.map_or_else(
            || {
                Some(self.denormalize_atom(
                    &head_type,
                    &term.get_head_atom(),
                    local_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                ))
            },
            |_| None,
        );

        // Type arguments appear as the first few arguments.
        // We need to:
        // 1. Extract type arguments and convert them to AcornTypes
        // 2. Update the head constant with those type parameters
        // 3. Apply only the value arguments

        let mut type_args: Vec<AcornType> = vec![];
        let mut value_args: Vec<AcornValue> = vec![];
        let mut remaining_head_type = head_type.clone();

        fn is_syntactic_type_term(term: &Term, local_context: &LocalContext) -> bool {
            fn go(term: crate::kernel::term::TermRef<'_>, local_context: &LocalContext) -> bool {
                use crate::kernel::term::Decomposition;
                match term.decompose() {
                    Decomposition::Atom(atom) => match atom {
                        Atom::Symbol(Symbol::Type(_))
                        | Atom::Symbol(Symbol::Bool)
                        | Atom::Symbol(Symbol::Empty)
                        | Atom::Symbol(Symbol::Type0)
                        | Atom::Symbol(Symbol::Typeclass(_)) => true,
                        Atom::FreeVariable(i) => local_context
                            .get_var_type(*i as usize)
                            .is_some_and(|t| t.as_ref().is_type_param_kind()),
                        Atom::BoundVariable(_) => true,
                        _ => false,
                    },
                    Decomposition::Application(func, arg) => {
                        go(func, local_context) && go(arg, local_context)
                    }
                    Decomposition::Pi(_, _) => true,
                    Decomposition::Lambda(_, _)
                    | Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _) => false,
                }
            }
            go(term.as_ref(), local_context)
        }

        fn is_syntactic_kind_term(term: &Term) -> bool {
            fn go(term: crate::kernel::term::TermRef<'_>) -> bool {
                use crate::kernel::term::Decomposition;
                match term.decompose() {
                    Decomposition::Atom(atom) => matches!(
                        atom,
                        Atom::Symbol(Symbol::Type0) | Atom::Symbol(Symbol::Typeclass(_))
                    ),
                    Decomposition::Pi(input, output) => go(input) && go(output),
                    Decomposition::Application(_, _)
                    | Decomposition::Lambda(_, _)
                    | Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _) => false,
                }
            }
            go(term.as_ref())
        }

        for arg in term.args().iter() {
            // Classify arguments from the function type spine instead of arg.get_type_with_context().
            // This avoids panicking on lambda arguments (their type is not inferable this late).
            let expected_input_type = remaining_head_type
                .as_ref()
                .split_pi()
                .map(|(input, _)| input.to_owned());
            let is_type_arg = expected_input_type
                .as_ref()
                .is_some_and(is_syntactic_kind_term)
                && is_syntactic_type_term(arg, local_context);

            if is_type_arg {
                // This is a type argument - convert it to an AcornType
                // Extract the typeclass constraint from the expected input kind.
                let typeclass = expected_input_type
                    .as_ref()
                    .and_then(|input| input.as_ref().as_typeclass())
                    .and_then(|tc_id| self.kernel_context.type_store.get_typeclass_by_id(tc_id))
                    .cloned();
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

            if let Some(next_type) = remaining_head_type.type_apply_with_arg(arg) {
                remaining_head_type = next_type;
            }
        }

        if let Some(symbol) = logical_head_symbol {
            match symbol {
                Symbol::Not => {
                    if !type_args.is_empty() || value_args.len() != 1 {
                        panic!("malformed not term during denormalization: {}", term);
                    }
                    return AcornValue::Not(Box::new(value_args.into_iter().next().unwrap()));
                }
                Symbol::And => {
                    if !type_args.is_empty() || value_args.len() != 2 {
                        panic!("malformed and term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::and(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Or => {
                    if !type_args.is_empty() || value_args.len() != 2 {
                        panic!("malformed or term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::or(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Eq => {
                    // Eq may carry one explicit type argument in term form.
                    if type_args.len() > 1 || value_args.len() != 2 {
                        panic!("malformed eq term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::equals(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Ite => {
                    // Ite may carry one explicit type argument in term form.
                    if type_args.len() > 1 || value_args.len() != 3 {
                        panic!("malformed ite term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::IfThenElse(
                        Box::new(args.next().unwrap()),
                        Box::new(args.next().unwrap()),
                        Box::new(args.next().unwrap()),
                    );
                }
                _ => unreachable!("unexpected logical symbol: {}", symbol),
            }
        }

        let head = head.expect("non-logical terms should have a denormalized head");

        if let Some(match_value) = self.maybe_reconstruct_match(
            &head,
            &type_args,
            &value_args,
            local_context,
            var_remapping,
        ) {
            return match_value;
        }

        let head = match head {
            AcornValue::Constant(c) => Self::apply_type_args_to_constant(&c, &type_args),
            other => other,
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
        // Type variables, arbitrary variables, and Empty placeholder variables
        // get None (excluded from forall).
        let mut var_remapping: Vec<Option<u16>> = Vec::new();
        let mut new_index: u16 = 0;
        for i in 0..num_vars {
            let type_term = &var_types_raw[i];
            // A variable is a type variable if its kind is Type0 (unconstrained) or Typeclass (constrained)
            let is_type_var = type_term.as_ref().is_type_param_kind();
            let is_arbitrary = arbitrary_names
                .map(|m| m.contains_key(type_term))
                .unwrap_or(false);
            let is_empty_placeholder = type_term.as_ref().is_empty_type();

            if is_type_var || is_arbitrary || is_empty_placeholder {
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

    /// Converts a single term to an AcornValue using the provided LocalContext.
    /// This is equivalent to the term-level work done by `denormalize(...)`,
    /// but avoids wrapping the term into a synthetic clause first.
    pub fn denormalize_term_with_context(
        &self,
        term: &Term,
        local_context: &LocalContext,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        self.denormalize_term(
            term,
            local_context,
            None,
            None,
            None,
            None,
            instantiate_type_vars,
        )
    }

    /// Converts a single term to an AcornValue using the provided LocalContext.
    /// If `arbitrary_names` is provided, matching free variables are converted to constants.
    pub fn denormalize_term_with_context_and_arbitrary(
        &self,
        term: &Term,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        self.denormalize_term(
            term,
            local_context,
            arbitrary_names,
            None,
            None,
            None,
            instantiate_type_vars,
        )
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
