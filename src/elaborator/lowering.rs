//! Elaborator-side lowering from user propositions to kernel proof inputs.
//!
//! This module orchestrates:
//! `AcornValue -> Term -> kernel term normalization -> theorem/clause lowering`.
//!
//! The elaborator does not define the normalization policy. Kernel term normalization
//! lives in `kernel::term_normalization`, and clause/theorem lowering lives in the
//! kernel clause/clausifier layers.

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
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::clausifier::TermLoweringMode;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, Truthiness};
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_term;
#[cfg(test)]
use crate::module::ModuleId;
use std::collections::HashMap;
use std::sync::Arc;
use tracing::trace;

/// A fact that has been lowered into proof steps.
#[derive(Clone)]
pub struct LoweredFact {
    pub steps: Vec<ProofStep>,
    pub kernel_context: KernelContext,
}

/// A goal that has been lowered into proof steps.
/// Includes the kernel_context state after lowering this goal.
#[derive(Clone)]
pub struct LoweredGoal {
    pub goal: Goal,
    pub steps: Vec<ProofStep>,
    /// The kernel context state after lowering this goal (with negated goal added).
    pub kernel_context: KernelContext,
}

/// Lower one fact using kernel context state.
pub fn lower_fact(
    kernel_context: &mut KernelContext,
    fact: &Fact,
) -> Result<LoweredFact, BuildError> {
    kernel_context.lower_fact(fact)
}

/// Lower one goal using kernel context state.
pub fn lower_goal(
    kernel_context: &mut KernelContext,
    goal: &Goal,
) -> Result<LoweredGoal, BuildError> {
    kernel_context.lower_goal(goal)
}

impl KernelContext {
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
    fn source_term_lowering_mode(source: &Source) -> TermLoweringMode {
        if source.should_clausify_shallowly() {
            TermLoweringMode::ClausifyShallowly
        } else {
            TermLoweringMode::PreserveAsLiteral
        }
    }

    /// Lower a term-level proposition into clauses.
    ///
    /// This is the term-native backend for proposition lowering.
    fn lower_term_to_clauses(
        &mut self,
        term: &Term,
        source: &Source,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        term.validate();
        self.lower_normalized_term_to_clauses(
            term,
            type_var_map,
            Self::source_term_lowering_mode(source),
        )
    }

    /// Lowers a value proposition to clauses via:
    /// `AcornValue --elaborate--> Term --kernel normalize--> clauses`.
    fn lower_value_to_clauses(
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
        let term = normalize_term(&term);
        self.lower_term_to_clauses(&term, source, type_var_map)
    }

    /// A single fact can turn into a bunch of proof steps.
    pub fn lower_fact(&mut self, fact: &Fact) -> Result<LoweredFact, BuildError> {
        let mut steps = vec![];

        // Register typeclass relationships in TypeStore
        match fact {
            Fact::Instance(datatype, typeclass, _) => {
                let acorn_type = AcornType::Data(datatype.clone(), vec![]);
                let typeclass_id = self.type_store.add_typeclass(typeclass);
                self.type_store.add_type_instance(&acorn_type, typeclass_id);
            }
            Fact::Extends(typeclass, base_set, inhabitant_provider, _) => {
                let tc_id = self.type_store.add_typeclass(typeclass);
                for base in base_set {
                    let base_id = self.type_store.add_typeclass(base);
                    self.type_store.add_typeclass_extends(tc_id, base_id);
                }
                // If we have an explicit provider constant `forall(P: Tc). P`, register it
                // in the kernel symbol table so inhabitedness can be constructive.
                if let Some(provider) = inhabitant_provider {
                    self.symbol_table.add_from(
                        &provider.clone().to_generic_value(),
                        NewConstantType::Global,
                        &mut self.type_store,
                    );
                }
            }
            _ => {}
        }

        let source = fact.source().clone();
        let range = source.range;

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
                    .lower_value_to_clauses(&value, ctype, &source, type_var_map_opt.clone())
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

        if let Some((constant_instance, alias_name, constant_type)) = fact.as_instance_alias() {
            // Normalize the bridge fact first so proof search still gets the explicit equality
            // between the public typeclass constant and the instance-only implementation symbol.
            // After that, register the alias so all later elaboration and certificate replay can
            // treat the public spelling as the same kernel symbol.
            let local = source.truthiness() != Truthiness::Factual;
            self.symbol_table.alias_instance(
                constant_instance,
                alias_name,
                &constant_type,
                local,
                &mut self.type_store,
            );
        }

        Ok(LoweredFact {
            steps,
            kernel_context: self.clone(),
        })
    }

    /// Lowers a goal into proof steps that include both positive versions
    /// of the hypotheses and negated versions of the conclusion.
    pub fn lower_goal(&mut self, goal: &Goal) -> Result<LoweredGoal, BuildError> {
        let prop = &goal.proposition;

        let (hypo, counterfactual) = prop.value.clone().negate_goal();
        let mut steps = vec![];
        if let Some(hypo) = hypo {
            // Preserve type parameters when creating hypothesis fact
            let hypo_prop = Proposition::new(hypo, prop.params.clone(), prop.source.clone())
                .with_arg_count(prop.arg_count);
            let fact = Fact::Proposition(Arc::new(hypo_prop));
            steps.extend(self.lower_fact(&fact)?.steps);
        }
        // Preserve type parameters when creating counterfactual fact
        let counterfactual_prop = Proposition::new(
            counterfactual,
            prop.params.clone(),
            prop.source.as_negated_goal(),
        )
        .with_arg_count(prop.arg_count);
        let fact = Fact::Proposition(Arc::new(counterfactual_prop));
        steps.extend(self.lower_fact(&fact)?.steps);

        Ok(LoweredGoal {
            goal: goal.clone(),
            steps,
            kernel_context: self.clone(),
        })
    }

    /// Converts backwards, from a clause to a value.
    /// The resulting value may include generated `choose(...)` witnesses or other
    /// normalized boolean structure that did not appear verbatim in the source.
    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If type_vars is provided, those variable indices are treated as type-level variables
    /// and excluded from the forall quantifier (their indices are remapped in the body).
    /// If type_param_names is provided, it's used for naming denormalized type params in
    /// polymorphic clauses.
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
    /// but avoids wrapping the term into a temporary one-literal clause first.
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
            .lower_value_to_clauses(
                &denormalized,
                NewConstantType::Local,
                &Source::theorem(false, ModuleId(0), Default::default(), true, 0, None),
                None,
            )
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
    fn clause_multiset(clauses: &[String]) -> std::collections::BTreeMap<String, usize> {
        let mut counts = std::collections::BTreeMap::new();
        for clause in clauses {
            *counts.entry(clause.clone()).or_insert(0) += 1;
        }
        counts
    }

    #[cfg(test)]
    fn format_clause_multiset(counts: &std::collections::BTreeMap<String, usize>) -> String {
        counts
            .iter()
            .map(|(clause, count)| {
                if *count == 1 {
                    clause.clone()
                } else {
                    format!("{}x {}", count, clause)
                }
            })
            .collect::<Vec<String>>()
            .join("\n")
    }

    #[cfg(test)]
    fn assert_clauses_match_unordered(actual: &[String], expected: &[String]) {
        let actual_counts = Self::clause_multiset(actual);
        let expected_counts = Self::clause_multiset(expected);
        if actual_counts == expected_counts {
            return;
        }

        let mut missing = vec![];
        for (clause, expected_count) in &expected_counts {
            let actual_count = actual_counts.get(clause).copied().unwrap_or(0);
            for _ in 0..expected_count.saturating_sub(actual_count) {
                missing.push(clause.clone());
            }
        }

        let mut unexpected = vec![];
        for (clause, actual_count) in &actual_counts {
            let expected_count = expected_counts.get(clause).copied().unwrap_or(0);
            for _ in 0..actual_count.saturating_sub(expected_count) {
                unexpected.push(clause.clone());
            }
        }

        panic!(
            "normalized clauses differ (order-insensitive)\n\
             expected multiset:\n{}\n\
             actual multiset:\n{}\n\
             missing:\n{}\n\
             unexpected:\n{}\n\
             actual clause order:\n{}",
            Self::format_clause_multiset(&expected_counts),
            Self::format_clause_multiset(&actual_counts),
            missing.join("\n"),
            unexpected.join("\n"),
            actual.join("\n")
        );
    }

    #[cfg(test)]
    fn check_value(&mut self, value: &AcornValue, expected: &[&str]) {
        use crate::kernel::display::DisplayClause;

        let actual = self
            .lower_value_to_clauses(
                value,
                NewConstantType::Local,
                &Source::theorem(false, ModuleId(0), Default::default(), true, 0, None),
                None,
            )
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
        for clause in &actual {
            self.check_denormalize_renormalize(clause);
        }

        let actual_strings: Vec<String> = actual
            .iter()
            .map(|clause| DisplayClause {
                clause,
                context: self,
            })
            .map(|c| c.to_string())
            .collect();
        let expected_strings: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        Self::assert_clauses_match_unordered(&actual_strings, &expected_strings);
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
                if let Ok(normalized) = self.lower_fact(&fact) {
                    for step in normalized.steps {
                        clauses.push(step.clause);
                    }
                }
            }
        }
        clauses
    }
}
