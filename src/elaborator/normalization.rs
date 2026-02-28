use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

use crate::builder::BuildError;
use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::elaborator::term_bridge::TermBridge;
use crate::elaborator::to_term::build_type_var_map;
use crate::elaborator::to_term::elaborate_value_to_term;
use crate::elaborator::to_term::elaborate_value_to_term_existing;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::clausifier::Clausifier;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, Truthiness};
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::synthetic::SyntheticDefinition;
use crate::kernel::term::Term;
use crate::module::ModuleId;
use tracing::trace;

/// A fact that has been normalized into proof steps.
#[derive(Clone)]
pub struct NormalizedFact {
    pub steps: Vec<ProofStep>,
    pub kernel_context: KernelContext,
}

/// A goal that has been normalized into proof steps.
/// Includes the kernel_context state after normalizing this goal.
#[derive(Clone)]
pub struct NormalizedGoal {
    pub goal: Goal,
    pub steps: Vec<ProofStep>,
    /// The kernel context state after normalizing this goal (with negated goal added).
    pub kernel_context: KernelContext,
}

/// Normalize one fact using kernel context state.
pub fn normalize_fact(
    kernel_context: &mut KernelContext,
    fact: &Fact,
) -> Result<NormalizedFact, BuildError> {
    kernel_context.normalize_fact(fact)
}

/// Normalize one goal using kernel context state.
pub fn normalize_goal(
    kernel_context: &mut KernelContext,
    goal: &Goal,
) -> Result<NormalizedGoal, BuildError> {
    kernel_context.normalize_goal(goal)
}
impl KernelContext {
    pub fn get_synthetic_type(&self, module_id: ModuleId, local_id: AtomId) -> AcornType {
        let symbol = Symbol::Synthetic(module_id, local_id);
        let type_term = self.symbol_table.get_type(symbol);
        self.type_store.type_term_to_acorn_type(type_term)
    }

    /// Returns all synthetic atom IDs that have been defined.
    #[cfg(test)]
    pub fn get_synthetic_ids(&self) -> Vec<(ModuleId, AtomId)> {
        self.synthetic_registry.get_ids()
    }

    /// Registers an arbitrary type with the type store.
    /// This is needed for certificate checking where type parameters defined
    /// in a let...satisfy statement need to be available for subsequent steps.
    pub fn register_arbitrary_type(&mut self, param: &TypeParam) {
        let arb_type = AcornType::Arbitrary(param.clone());
        self.type_store.add_type(&arb_type);

        // If the type param has a typeclass constraint, ensure the typeclass is registered.
        if let Some(typeclass) = &param.typeclass {
            self.type_store.add_typeclass(typeclass);
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

        let term = elaborate_value_to_term_existing(self, &alt_value, type_var_map).ok()?;
        let term_for_clausify: Cow<'_, Term> = {
            #[cfg(feature = "canonicalization")]
            {
                Cow::Owned(crate::kernel::canonicalize::canonicalize_term(&term))
            }
            #[cfg(not(feature = "canonicalization"))]
            {
                Cow::Borrowed(&term)
            }
        };
        let mut view = Clausifier::new_mut(self, type_var_map.cloned(), ModuleId(0));
        let Ok(uninstantiated) =
            view.clausify_term_to_denormalized_clauses(term_for_clausify.as_ref())
        else {
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
                let mut type_term = self.type_store.to_type_term_with_vars(t, type_var_map);
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

    pub fn add_scoped_constant(
        &mut self,
        cname: ConstantName,
        acorn_type: &AcornType,
        type_var_map: Option<&HashMap<String, (AtomId, Term)>>,
    ) -> Atom {
        let type_term = self
            .type_store
            .to_type_term_with_vars(acorn_type, type_var_map);
        Atom::Symbol(
            self.symbol_table
                .add_constant(cname, NewConstantType::Local, type_term),
        )
    }
}

impl KernelContext {
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
        let term_for_clausify: Cow<'_, Term> = {
            #[cfg(feature = "canonicalization")]
            {
                Cow::Owned(crate::kernel::canonicalize::canonicalize_term(term))
            }
            #[cfg(not(feature = "canonicalization"))]
            {
                Cow::Borrowed(term)
            }
        };
        term_for_clausify.validate();

        let mut skolem_ids = vec![];
        let mut mut_view = Clausifier::new_mut(self, type_var_map.clone(), source.module_id);
        let clauses = mut_view.clausify_term(term_for_clausify.as_ref(), &mut skolem_ids)?;

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
                .map(|&(m, i)| self.symbol_table.get_type(Symbol::Synthetic(m, i)).clone())
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

        let term = elaborate_value_to_term(self, value, ctype, type_var_map.as_ref())?;
        self.normalize_term(&term, ctype, source, type_var_map)
    }

    /// A single fact can turn into a bunch of proof steps.
    pub fn normalize_fact(&mut self, fact: &Fact) -> Result<NormalizedFact, BuildError> {
        let mut steps = vec![];

        // Register typeclass relationships in TypeStore
        match fact {
            Fact::Instance(datatype, typeclass, _) => {
                let acorn_type = AcornType::Data(datatype.clone(), vec![]);
                let typeclass_id = self.type_store.add_typeclass(typeclass);
                self.type_store.add_type_instance(&acorn_type, typeclass_id);
            }
            Fact::Extends(typeclass, base_set, provides_inhabitants, _) => {
                let tc_id = self.type_store.add_typeclass(typeclass);
                for base in base_set {
                    let base_id = self.type_store.add_typeclass(base);
                    self.type_store.add_typeclass_extends(tc_id, base_id);
                }
                // If the typeclass has a constant of the instance type (e.g., point: P),
                // mark it as providing inhabitants.
                if *provides_inhabitants {
                    self.symbol_table.mark_typeclass_inhabited(tc_id);
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
                let type_var_map = build_type_var_map(self, &type_params);

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
                    clause.validate(self);
                    let step = ProofStep::assumption(&source, clause);
                    steps.push(step);
                }
            }
        }

        Ok(NormalizedFact {
            steps,
            kernel_context: self.clone(),
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
            kernel_context: self.clone(),
        })
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
        TermBridge::new(self).denormalize(
            clause,
            arbitrary_names,
            type_param_names,
            instantiate_type_vars,
        )
    }

    /// Convert a type Term to AcornType, looking up typeclass constraints from LocalContext.
    /// If `instantiate_type_vars` is true, FreeVariable type atoms become concrete types.
    pub fn denormalize_type_with_context(
        &self,
        type_term: Term,
        local_context: &LocalContext,
        instantiate_type_vars: bool,
    ) -> AcornType {
        TermBridge::new(self).denormalize_type_with_context(
            type_term,
            local_context,
            instantiate_type_vars,
        )
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
        TermBridge::new(self).denormalize_term_with_context(
            term,
            local_context,
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
        TermBridge::new(self).denormalize_term_with_context_and_arbitrary(
            term,
            local_context,
            arbitrary_names,
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
                        context: self,
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
                context: self,
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
