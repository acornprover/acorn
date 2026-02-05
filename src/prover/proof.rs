use std::collections::{HashMap, HashSet};

use crate::certificate::Certificate;
use crate::code_generator::Error;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::Term;
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, ProofStepId, Rule};

/// Trait for types that can resolve proof step IDs to clauses.
/// Used by reconstruct_step to look up premises.
///
/// This abstraction allows the same reconstruction logic to be used for:
/// - Full proof reconstruction (via Proof)
/// - Validation at creation time (via ActiveSet)
pub trait ProofResolver {
    fn get_clause(&self, id: ProofStepId) -> Result<&Clause, Error>;
    fn kernel_context(&self) -> &KernelContext;
}

/// A proof that was successfully found by the prover.
///
/// This is the internal form of the proof. The exportable form is a Certificate,
/// which can always be created and is fast to check.
///
/// We store each step of the proof in the order we found them, in `steps`.
/// This represents a proof by contradiction, with each step depending only on
/// previous steps.
pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    // Steps of the proof that can be directly verified.
    // Represents a proof by contradiction, with each step depending only on
    // previous steps.
    pub steps: Vec<(ProofStepId, &'a ProofStep)>,

    // Same data as steps, but indexed.
    step_map: HashMap<ProofStepId, &'a ProofStep>,
}

impl<'a> Proof<'a> {
    /// Creates a new proof.
    pub fn new(normalizer: &'a Normalizer) -> Proof<'a> {
        Proof {
            normalizer,
            steps: vec![],
            step_map: HashMap::new(),
        }
    }

    /// Add a new step to the proof.
    pub fn add_step(&mut self, id: ProofStepId, step: &'a ProofStep) {
        self.step_map.insert(id.clone(), step);
        self.steps.push((id, step));
    }
}

impl ProofResolver for Proof<'_> {
    fn get_clause(&self, id: ProofStepId) -> Result<&Clause, Error> {
        let step = self.step_map.get(&id).ok_or_else(|| {
            Error::internal(format!(
                "no node found for proof step {:?} in proof graph",
                id
            ))
        })?;
        Ok(&step.clause)
    }

    fn kernel_context(&self) -> &KernelContext {
        self.normalizer.kernel_context()
    }
}

// Each step in the ConcreteProof is associated with a ConcreteStepId.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConcreteStepId {
    // This concrete step matches the *output* of a proof step.
    ProofStep(ProofStepId),

    // This concrete step matches the *input* of an assumption.
    // The assumption is a proof step, but its output is simplified, and this represents
    // the original assumption.
    Assumption(ProofStepId),
}

// In the order that they are logically deduced, because the assumption comes first.
fn concrete_ids_for(ps_id: ProofStepId) -> [ConcreteStepId; 2] {
    let assumption_id = ConcreteStepId::Assumption(ps_id);
    let concrete_id = ConcreteStepId::ProofStep(ps_id);
    [assumption_id, concrete_id]
}

/// A concrete version of a proof step that has been reconstructed from the proof.
/// Also used when converting ConcreteProof to Certificate.
pub struct ConcreteStep {
    // The generic clause for this proof step.
    pub generic: Clause,

    // All of the ways to map the generic variables to concrete ones.
    // Each var_map is paired with the context that its replacement terms reference.
    // This context is needed to look up variable types when specializing.
    pub var_maps: Vec<(VariableMap, LocalContext)>,
}

impl ConcreteStep {
    fn new(generic: Clause, var_map: VariableMap, replacement_context: LocalContext) -> Self {
        ConcreteStep {
            generic,
            var_maps: vec![(var_map, replacement_context)],
        }
    }

    /// Convert this ConcreteStep to specialized clauses.
    fn to_clauses(&self, kernel_context: &KernelContext) -> Vec<Clause> {
        self.var_maps
            .iter()
            .map(|(var_map, replacement_context)| {
                let mut clause = var_map.specialize_clause_with_replacement_context(
                    &self.generic,
                    replacement_context,
                    kernel_context,
                );
                // Normalize variable IDs to ensure they are in order (0, 1, 2, ...) with no gaps.
                clause.normalize_var_ids_no_flip();
                clause
            })
            .collect()
    }
}

// Adds a var map for a non-assumption proof step.
fn add_var_map<R: ProofResolver>(
    resolver: &R,
    id: ProofStepId,
    var_map: VariableMap,
    replacement_context: LocalContext,
    concrete_steps: &mut HashMap<ConcreteStepId, ConcreteStep>,
) {
    let generic = resolver.get_clause(id).unwrap();
    let replacement_context = if var_map.len() == 0 && replacement_context.len() == 0 {
        generic.get_local_context().clone()
    } else {
        replacement_context
    };
    match concrete_steps.entry(ConcreteStepId::ProofStep(id)) {
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            let concrete_step = entry.get_mut();
            concrete_step.var_maps.push((var_map, replacement_context));
        }
        std::collections::hash_map::Entry::Vacant(entry) => {
            let concrete_step = ConcreteStep::new(generic.clone(), var_map, replacement_context);
            entry.insert(concrete_step);
        }
    }
}

impl<'a> Proof<'a> {
    /// Create a certificate for this proof.
    pub fn make_cert(&self, goal: String, bindings: &BindingMap) -> Result<Certificate, Error> {
        #[cfg(feature = "bigcert")]
        {
            let concrete_steps = self.collect_concrete_steps()?;
            return Certificate::from_concrete_steps(
                goal,
                &concrete_steps,
                self.normalizer,
                bindings,
            );
        }

        #[cfg(not(feature = "bigcert"))]
        {
            let concrete_proof = self.make_concrete_proof(goal)?;
            Certificate::from_concrete_proof(&concrete_proof, self.normalizer, bindings)
        }
    }

    /// Reconstruct concrete specialization steps in claim order, skipping clauses
    /// that we intentionally omit from certificates.
    fn collect_concrete_steps(&self) -> Result<Vec<ConcreteStep>, Error> {
        let kernel_context = self.normalizer.kernel_context();

        // First, reconstruct all the steps, working backwards.
        let mut concrete_steps: HashMap<ConcreteStepId, ConcreteStep> = HashMap::new();
        for (id, step) in self.steps.iter().rev() {
            if *id == ProofStepId::Final {
                // Empty map has no replacement terms, so empty context is fine
                reconstruct_step(
                    self,
                    *id,
                    step,
                    VariableMap::new(),
                    &LocalContext::empty(),
                    &mut concrete_steps,
                )?;
                continue;
            }
            // Multiple concrete instantiations are possible
            let concrete_id = ConcreteStepId::ProofStep(*id);
            let var_maps_with_context = match concrete_steps.get(&concrete_id) {
                Some(concrete_step) => concrete_step.var_maps.clone(),
                None => continue,
            };
            for (var_map, context) in var_maps_with_context {
                reconstruct_step(self, *id, step, var_map, &context, &mut concrete_steps)?;
            }
        }

        // Skip clauses from concrete assumptions
        let mut skip_clauses: HashSet<Clause> = HashSet::new();
        for (ps_id, step) in &self.steps {
            let concrete_id = ConcreteStepId::ProofStep(*ps_id);
            let has_type_params = step
                .clause
                .get_local_context()
                .get_var_types()
                .iter()
                .any(|t| t.as_ref().is_type_param_kind());
            if step.rule.is_underlying_assumption()
                && !step.clause.has_any_variable()
                && !has_type_params
            {
                let Some(cs) = concrete_steps.remove(&concrete_id) else {
                    continue;
                };
                for clause in cs.to_clauses(kernel_context) {
                    skip_clauses.insert(clause);
                }
            }
        }

        // Collect all concrete specializations in order.
        let mut claims = Vec::new();
        let mut steps_in_order = Vec::new();
        for (ps_id, _) in &self.steps {
            for concrete_id in concrete_ids_for(*ps_id) {
                let Some(cs) = concrete_steps.remove(&concrete_id) else {
                    continue;
                };
                let ConcreteStep { generic, var_maps } = cs;
                for (var_map, replacement_context) in var_maps {
                    let concrete_step = ConcreteStep {
                        generic: generic.clone(),
                        var_maps: vec![(var_map, replacement_context)],
                    };
                    let Some(clause) = concrete_step.to_clauses(kernel_context).into_iter().next()
                    else {
                        continue;
                    };
                    if !claims.contains(&clause) && !skip_clauses.contains(&clause) {
                        claims.push(clause);
                        steps_in_order.push(concrete_step);
                    }
                }
            }
        }

        Ok(steps_in_order)
    }

    /// Create a concrete proof from this proof.
    /// This is an intermediate representation between Proof and Certificate.
    pub fn make_concrete_proof(&self, goal: String) -> Result<ConcreteProof, Error> {
        let kernel_context = self.normalizer.kernel_context();
        let steps_in_order = self.collect_concrete_steps()?;
        let mut claims = Vec::new();
        for step in &steps_in_order {
            for clause in step.to_clauses(kernel_context) {
                claims.push(clause);
            }
        }

        Ok(ConcreteProof { goal, claims })
    }
}

// Given a varmap for the conclusion of a proof step, reconstruct varmaps for
// all of its inputs.
// The varmaps represent a concrete clause, in the sense that they provide a mapping to specialize
// the clause into something concrete.
//
// Reconstructed varmaps are added to concrete_steps.
// If the step cannot be reconstructed, we return an error.
//
// The conclusion_map_context is the context that conclusion_map's replacement terms reference.
// This is needed to look up variable types when building output contexts.
pub fn reconstruct_step<R: ProofResolver>(
    resolver: &R,
    id: ProofStepId,
    step: &ProofStep,
    conclusion_map: VariableMap,
    conclusion_map_context: &LocalContext,
    concrete_steps: &mut HashMap<ConcreteStepId, ConcreteStep>,
) -> Result<(), Error> {
    // Some rules we can handle without the traces.
    match &step.rule {
        Rule::PassiveContradiction(_) | Rule::MultipleRewrite(_) => {
            // These rules use premises that may have free variables.
            // We pass empty map + empty context; add_var_map will automatically
            // use the clause's context when both are empty.
            for id in step.rule.premises() {
                let map = VariableMap::new();
                add_var_map(resolver, id, map, LocalContext::empty(), concrete_steps);
            }
            return Ok(());
        }

        // Rules with populated PremiseMaps: compose raw inference maps with conclusion_map
        // to get concrete var maps. No re-unification needed.
        Rule::Extensionality(_) => {
            // No reconstruction needed - extensionality is sound on universally
            // quantified clauses without instantiation.
            return Ok(());
        }

        Rule::EqualityResolution(_)
        | Rule::EqualityFactoring(_)
        | Rule::Injectivity(_)
        | Rule::BooleanReduction(_)
        | Rule::Rewrite(_)
        | Rule::Resolution(_)
        | Rule::Specialization(_)
        | Rule::Simplification(_)
            if !step.premise_map.is_empty() =>
        {
            let premise_ids = step.rule.premises();
            let mut premise_contexts: Vec<&LocalContext> = Vec::new();
            for premise_id in &premise_ids {
                let premise_clause = resolver.get_clause(*premise_id)?;
                premise_contexts.push(premise_clause.get_local_context());
            }
            let concrete_premises = step.premise_map.concretize_premises(
                &conclusion_map,
                conclusion_map_context,
                &premise_contexts,
            );
            for (premise_id, (mut var_map, mut context)) in
                premise_ids.into_iter().zip(concrete_premises)
            {
                // Fill in any remaining unmapped premise variables with fresh output variables
                let premise_clause = resolver.get_clause(premise_id)?;
                let premise_context = premise_clause.get_local_context();
                let mut next_var = context.len();
                for var_id in 0..premise_context.len() {
                    if !var_map.has_mapping(var_id as AtomId) {
                        if let Some(var_type) = premise_context.get_var_type(var_id) {
                            var_map.set(var_id as AtomId, Term::new_variable(next_var as AtomId));
                            // Apply var_map to remap variable references from premise to output context
                            let remapped_type = apply_to_term(var_type.as_ref(), &var_map);
                            context.set_type(next_var, remapped_type);
                            next_var += 1;
                        }
                    }
                }
                add_var_map(resolver, premise_id, var_map, context, concrete_steps);
            }

            // For Simplification, also reconstruct the inner step
            if let Rule::Simplification(info) = &step.rule {
                let (inner_map, inner_context) = step.premise_map.inner_step_map(
                    &conclusion_map,
                    conclusion_map_context,
                    info.original.clause.get_local_context(),
                );
                reconstruct_step(
                    resolver,
                    id,
                    &info.original,
                    inner_map,
                    &inner_context,
                    concrete_steps,
                )?;
            }
            return Ok(());
        }

        _ => {}
    }

    match &step.rule {
        Rule::Assumption(info) => {
            if conclusion_map.len() == 0 {
                // No concrete instantiation needed.
                return Ok(());
            }
            // The assumption trace is always identity (each literal maps to itself),
            // so reconstruction just passes through the conclusion_map directly.
            let assumption_id = ConcreteStepId::Assumption(id);
            match concrete_steps.entry(assumption_id) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry
                        .get_mut()
                        .var_maps
                        .push((conclusion_map, conclusion_map_context.clone()));
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let generic =
                        Clause::from_literals_unnormalized(info.literals.clone(), &info.context);
                    entry.insert(ConcreteStep::new(
                        generic,
                        conclusion_map,
                        conclusion_map_context.clone(),
                    ));
                }
            }
        }
        rule => {
            return Err(Error::internal(format!(
                "missing reconstruction method for rule {}",
                rule.name()
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::kernel::clause::Clause;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::variable_map::VariableMap;
    use crate::proof_step::ProofStepId;
    use crate::proof_step::{ProofStep, Rule, Truthiness};
    use crate::prover::active_set::ActiveSet;
    use crate::prover::proof::{add_var_map, ProofResolver};
    use std::collections::HashMap;

    /// Test that resolution followed by simplification produces correct results.
    ///
    /// The scenario:
    /// - Long clause: not g0(x) or g1(x) = c0  (x is a variable)
    /// - Short clause: g0(g2(c1))  (concrete, resolves with first literal, binds x->g2(c1))
    /// - Resolution gives: g1(g2(c1)) = c0
    /// - Simplification clause: g1(g2(x)) != c0  (eliminates g1(g2(c1)) = c0)
    /// - Result: empty clause (contradiction)
    #[test]
    fn test_resolution_with_simplification() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool")
            .parse_constant("g2", "Bool -> Bool")
            .parse_constant("c0", "Bool")
            .parse_constant("c1", "Bool");

        let long_clause = kctx.parse_clause("not g0(x0) or g1(x0) = c0", &["Bool"]);
        let long_step = ProofStep::mock_from_clause(long_clause);

        let short_clause = kctx.parse_clause("g0(g2(c1))", &[]);
        let mut short_step = ProofStep::mock_from_clause(short_clause);
        short_step.truthiness = Truthiness::Hypothetical;

        let simp_clause = kctx.parse_clause("g1(g2(x0)) != c0", &["Bool"]);
        let simp_step = ProofStep::mock_from_clause(simp_clause);

        let mut active_set = ActiveSet::new();
        active_set.activate(long_step.clone(), &kctx);
        active_set.activate(simp_step.clone(), &kctx);

        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);
        active_set.activate(short_step.clone(), &kctx);

        assert!(!resolution_results.is_empty());

        let resolution_step = resolution_results.into_iter().next().unwrap();
        let simplified_step = active_set.simplify(resolution_step.clone(), &kctx);
        let final_step = simplified_step.unwrap_or(resolution_step);

        assert!(
            final_step.clause.is_impossible(),
            "Expected empty clause, got: {}",
            final_step.clause
        );

        let simp_info = match &final_step.rule {
            Rule::Simplification(info) => info,
            other => panic!("Expected Simplification rule, got {:?}", other),
        };

        match &simp_info.original.rule {
            Rule::Resolution(_) => {}
            other => panic!("Expected inner Resolution rule, got {:?}", other),
        };

        assert!(!simp_info.simplifying_ids.is_empty());
    }

    struct TestResolver {
        clause: Clause,
        kernel_context: KernelContext,
    }

    impl ProofResolver for TestResolver {
        fn get_clause(&self, id: ProofStepId) -> Result<&Clause, crate::code_generator::Error> {
            match id {
                ProofStepId::Active(0) => Ok(&self.clause),
                _ => Err(crate::code_generator::Error::internal(
                    "unexpected proof step id",
                )),
            }
        }

        fn kernel_context(&self) -> &KernelContext {
            &self.kernel_context
        }
    }

    #[test]
    fn test_add_var_map_defaults_context_for_empty_map() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool");

        let clause = kctx.parse_clause("g0(x0)", &["Bool"]);
        let resolver = TestResolver {
            clause: clause.clone(),
            kernel_context: kctx,
        };

        let mut concrete_steps = HashMap::new();
        add_var_map(
            &resolver,
            ProofStepId::Active(0),
            VariableMap::new(),
            LocalContext::empty(),
            &mut concrete_steps,
        );

        let entry = concrete_steps
            .get(&crate::prover::proof::ConcreteStepId::ProofStep(
                ProofStepId::Active(0),
            ))
            .expect("concrete step");
        let (_, replacement_context) = entry.var_maps.first().expect("replacement context");
        assert_eq!(replacement_context.len(), clause.get_local_context().len());
    }

    /// Test that resolution with polymorphic simplification works correctly.
    ///
    /// The scenario:
    /// - Long clause: not g0(x0) or not g1(x0, g2(x0))
    /// - Short clause: g0(c0)  (resolves with first literal, binds x0->c0)
    /// - Resolution gives: not g1(c0, g2(c0))
    /// - Simplification clause: g1(x0, g2(x0))  (eliminates the neg lit)
    /// - Result: empty clause (contradiction)
    #[test]
    fn test_resolution_simplification_with_polymorphic_flip() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("g1", "(Bool, Bool) -> Bool")
            .parse_constant("g2", "Bool -> Bool")
            .parse_constant("c0", "Bool");

        let long_clause = kctx.parse_clause("not g0(x0) or not g1(x0, g2(x0))", &["Bool"]);
        let mut long_step = ProofStep::mock_from_clause(long_clause);
        long_step.truthiness = Truthiness::Factual;

        let simp_clause = kctx.parse_clause("g1(x0, g2(x0))", &["Bool"]);
        let simp_step = ProofStep::mock_from_clause(simp_clause);

        let short_clause = kctx.parse_clause("g0(c0)", &[]);
        let mut short_step = ProofStep::mock_from_clause(short_clause);
        short_step.truthiness = Truthiness::Hypothetical;

        let mut active_set = ActiveSet::new();
        active_set.activate(long_step.clone(), &kctx);
        active_set.activate(simp_step.clone(), &kctx);

        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);
        active_set.activate(short_step.clone(), &kctx);

        assert!(!resolution_results.is_empty());

        let resolution_step = resolution_results.into_iter().next().unwrap();
        let simplified_step = active_set.simplify(resolution_step.clone(), &kctx);
        let final_step = simplified_step.unwrap_or(resolution_step);

        assert!(
            final_step.clause.is_impossible(),
            "Expected empty clause, got: {}",
            final_step.clause
        );

        let simp_info = match &final_step.rule {
            Rule::Simplification(info) => info,
            other => panic!("Expected Simplification rule, got {:?}", other),
        };

        match &simp_info.original.rule {
            Rule::Resolution(_) => {}
            other => panic!("Expected inner Resolution rule, got {:?}", other),
        };
    }

    /// Test that simplification with multiple eliminated literals includes all instantiations.
    ///
    /// This reproduces a bug from nat.nat_combo:197 where:
    /// - Long clause: g0(x0, x1) != c0 or x0 = c0 or x1 = c0
    /// - Short clause: g0(g1(c1), g1(c2)) = c0  (concrete)
    /// - Resolution gives: g1(c1) = c0 or g1(c2) = c0  (2 literals)
    /// - Simplification clause: g1(x0) != c0
    /// - Both literals should be eliminated, requiring TWO instantiations of the simp clause
    /// - Bug: only one instantiation was included in the concrete proof
    #[test]
    fn test_simplification_multiple_eliminated_literals() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g1", "Bool -> Bool")
            .parse_constant("c0", "Bool")
            .parse_constant("c1", "Bool")
            .parse_constant("c2", "Bool");

        // Long clause: g0(x0, x1) != c0 or x0 = c0 or x1 = c0
        // (if g0 returns c0, one of its arguments is c0)
        let long_clause =
            kctx.parse_clause("g0(x0, x1) != c0 or x0 = c0 or x1 = c0", &["Bool", "Bool"]);
        let long_step = ProofStep::mock_from_clause(long_clause);

        // Short clause: g0(g1(c1), g1(c2)) = c0 (negated goal)
        let short_clause = kctx.parse_clause("g0(g1(c1), g1(c2)) = c0", &[]);
        let mut short_step = ProofStep::mock_from_clause(short_clause);
        short_step.truthiness = Truthiness::Counterfactual;

        // Simplification clause: g1(x0) != c0 (g1 never returns c0)
        let simp_clause = kctx.parse_clause("g1(x0) != c0", &["Bool"]);
        let simp_step = ProofStep::mock_from_clause(simp_clause);

        let mut active_set = ActiveSet::new();
        active_set.activate(long_step.clone(), &kctx);
        active_set.activate(simp_step.clone(), &kctx);

        // Find resolution between long and short
        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);
        active_set.activate(short_step.clone(), &kctx);

        assert!(
            !resolution_results.is_empty(),
            "Should find at least one resolution"
        );

        // The resolution result should have 2 literals: g1(c1) = c0 or g1(c2) = c0
        let resolution_step = resolution_results.into_iter().next().unwrap();
        assert_eq!(
            resolution_step.clause.literals.len(),
            2,
            "Resolution should produce 2 literals, got: {}",
            resolution_step.clause
        );

        // Simplify - this should eliminate BOTH literals
        let simplified_step = active_set.simplify(resolution_step.clone(), &kctx);
        let final_step = simplified_step.unwrap_or(resolution_step);

        assert!(
            final_step.clause.is_impossible(),
            "Expected empty clause (contradiction), got: {}",
            final_step.clause
        );

        // Verify the simplification used the simp clause twice (for both literals)
        let simp_info = match &final_step.rule {
            Rule::Simplification(info) => info,
            other => panic!("Expected Simplification rule, got {:?}", other),
        };

        // The bug: simplifying_ids only has 1 entry when it should have 2
        assert_eq!(
            simp_info.simplifying_ids.len(),
            2,
            "Should have 2 simplifying clause uses (one for each eliminated literal), got {}",
            simp_info.simplifying_ids.len()
        );
    }
}
