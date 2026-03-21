use std::collections::{HashMap, HashSet};

use crate::certificate::Certificate;
use crate::code_generator::Error;
use crate::elaborator::binding_map::BindingMap;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, ProofStepId, Rule};
use crate::kernel::term::Term;
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::prover::synthetic::WitnessRegistry;

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
    kernel_context: &'a KernelContext,
    #[cfg_attr(not(feature = "nwit"), allow(dead_code))]
    witness_registry: Option<&'a WitnessRegistry>,

    // Steps of the proof that can be directly verified.
    // Represents a proof by contradiction, with each step depending only on
    // previous steps.
    pub steps: Vec<(ProofStepId, &'a ProofStep)>,

    // Same data as steps, but indexed.
    step_map: HashMap<ProofStepId, &'a ProofStep>,
}

impl<'a> Proof<'a> {
    /// Creates a new proof.
    pub fn new(kernel_context: &'a KernelContext) -> Proof<'a> {
        Self::new_with_witnesses(kernel_context, None)
    }

    /// Create a proof that can optionally remember prover-generated witness metadata for certs.
    pub fn new_with_witnesses(
        kernel_context: &'a KernelContext,
        witness_registry: Option<&'a WitnessRegistry>,
    ) -> Proof<'a> {
        Proof {
            kernel_context,
            witness_registry,
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
        self.kernel_context
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

/// A reconstructed proof step together with the environments needed to specialize it.
///
/// By contract, each `(VariableMap, LocalContext)` pair must fully instantiate `generic`.
/// That means `to_clauses()` is expected to produce ground clauses with no free variables and
/// an empty local context. Validate mode checks this invariant.
///
/// Also used when converting ConcreteProof to Certificate.
#[derive(Clone)]
pub struct ConcreteStep {
    // The generic clause for this proof step.
    pub generic: Clause,

    // All of the ways to fully instantiate the generic variables.
    // Each var_map is paired with the context that its replacement terms reference while
    // specializing. After specialization, no locals should remain in the output clause.
    pub var_maps: Vec<(VariableMap, LocalContext)>,
}

impl ConcreteStep {
    fn new(generic: Clause, var_map: VariableMap, replacement_context: LocalContext) -> Self {
        ConcreteStep {
            generic,
            var_maps: vec![(var_map, replacement_context)],
        }
    }

    #[cfg(any(test, feature = "validate"))]
    fn validate_specialized_clause_is_concrete(
        &self,
        clause: &Clause,
        var_map: &VariableMap,
        replacement_context: &LocalContext,
    ) {
        if clause.has_any_variable() || !clause.get_local_context().is_empty() {
            panic!(
                "ConcreteStep invariant violated: specializing `{}` with var_map {:?} and replacement context {:?} produced non-concrete clause `{}` with context {:?}",
                self.generic,
                var_map,
                replacement_context,
                clause,
                clause.get_local_context(),
            );
        }
    }

    #[cfg(any(test, feature = "validate"))]
    pub(crate) fn validate_specializes_to_concrete_clauses(&self, kernel_context: &KernelContext) {
        for (var_map, replacement_context) in &self.var_maps {
            let clause = var_map.specialize_clause_with_replacement_context_and_compact_vars(
                &self.generic,
                replacement_context,
                kernel_context,
            );
            self.validate_specialized_clause_is_concrete(&clause, var_map, replacement_context);
        }
    }

    /// Convert this `ConcreteStep` to the ground clauses it represents.
    ///
    /// By contract, every returned clause must be fully instantiated, with no free variables and
    /// an empty local context.
    fn to_clauses(&self, kernel_context: &KernelContext) -> Vec<Clause> {
        self.var_maps
            .iter()
            .map(|(var_map, replacement_context)| {
                let clause = var_map.specialize_clause_with_replacement_context_and_compact_vars(
                    &self.generic,
                    replacement_context,
                    kernel_context,
                );
                #[cfg(feature = "validate")]
                self.validate_specialized_clause_is_concrete(&clause, var_map, replacement_context);
                clause
            })
            .collect()
    }
}

fn push_concrete_step_if_new(
    concrete_step: ConcreteStep,
    claim_index: &mut HashMap<Clause, usize>,
    steps_in_order: &mut Vec<ConcreteStep>,
    skip_clauses: &HashSet<Clause>,
    kernel_context: &KernelContext,
) {
    let Some(clause) = concrete_step.to_clauses(kernel_context).into_iter().next() else {
        return;
    };
    if skip_clauses.contains(&clause) {
        return;
    }
    if claim_index.contains_key(&clause) {
        return;
    }
    claim_index.insert(clause, steps_in_order.len());
    steps_in_order.push(concrete_step);
}

fn append_inline_simplification_originals(
    step: &ProofStep,
    reconstructed_steps: &HashMap<ConcreteStepId, ConcreteStep>,
    claim_index: &mut HashMap<Clause, usize>,
    steps_in_order: &mut Vec<ConcreteStep>,
    skip_clauses: &HashSet<Clause>,
    kernel_context: &KernelContext,
) {
    let Rule::Simplification(info) = &step.rule else {
        return;
    };

    if !step.clause.is_impossible() {
        return;
    }

    append_inline_simplification_originals(
        &info.original,
        reconstructed_steps,
        claim_index,
        steps_in_order,
        skip_clauses,
        kernel_context,
    );

    if info.original.rule.is_assumption() {
        return;
    }

    if !matches!(info.original.rule, Rule::BooleanReduction(_))
        || !info.original.clause.has_any_variable()
    {
        return;
    }

    for premise_id in step.rule.premises() {
        for premise_key in [
            ConcreteStepId::ProofStep(premise_id),
            ConcreteStepId::Assumption(premise_id),
        ] {
            let Some(concrete_premise) = reconstructed_steps.get(&premise_key) else {
                continue;
            };
            for (var_map, replacement_context) in &concrete_premise.var_maps {
                push_concrete_step_if_new(
                    ConcreteStep {
                        generic: info.original.clause.clone(),
                        var_maps: vec![(var_map.clone(), replacement_context.clone())],
                    },
                    claim_index,
                    steps_in_order,
                    skip_clauses,
                    kernel_context,
                );
            }
        }
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

fn passive_contradiction_var_map<R: ProofResolver>(
    resolver: &R,
    clause: &Clause,
) -> Result<(VariableMap, LocalContext), Error> {
    let local_context = clause.get_local_context().clone();
    let mut used_vars = HashSet::new();
    for atom in clause.iter_atoms() {
        if let crate::kernel::atom::Atom::FreeVariable(var_id) = atom {
            used_vars.insert(*var_id);
        }
    }

    let mut var_map = VariableMap::new();
    for var_id in used_vars {
        let Some(var_type) = local_context.get_var_type(var_id as usize) else {
            continue;
        };
        let witness = resolver
            .kernel_context()
            .find_inhabitant(var_type, Some(&local_context))
            .ok_or_else(|| {
                Error::internal(format!(
                    "missing inhabitant while reconstructing passive contradiction for {} at x{}: {}",
                    clause, var_id, var_type
                ))
            })?;
        var_map.set(var_id, witness);
    }

    Ok((var_map, local_context))
}

impl<'a> Proof<'a> {
    /// Create a certificate for this proof.
    pub fn make_cert(&self, goal: String, bindings: &BindingMap) -> Result<Certificate, Error> {
        let concrete_steps = self.collect_concrete_steps()?;
        #[cfg(feature = "nwit")]
        let witness_registry = self.witness_registry;
        #[cfg(not(feature = "nwit"))]
        let witness_registry = None;
        Certificate::from_concrete_steps_with_witnesses(
            goal,
            &concrete_steps,
            self.kernel_context,
            bindings,
            witness_registry,
        )
    }

    /// Reconstruct concrete specialization steps in claim order, skipping clauses
    /// that we intentionally omit from certificates.
    fn collect_concrete_steps(&self) -> Result<Vec<ConcreteStep>, Error> {
        let kernel_context = self.kernel_context;

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

        // Keep a snapshot for any synthesized certificate steps that need to inspect
        // reconstructed premise instantiations after the main collection pass.
        let reconstructed_steps = concrete_steps.clone();

        // Skip direct concrete assumptions because the checker already has them.
        // Do not skip simplified outputs of assumptions: those are derived clauses,
        // and later certificate steps may depend on them as prerequisites.
        let mut skip_clauses: HashSet<Clause> = HashSet::new();
        for (ps_id, step) in &self.steps {
            let concrete_id = ConcreteStepId::ProofStep(*ps_id);
            let has_type_params = step
                .clause
                .get_local_context()
                .get_var_types()
                .iter()
                .any(|t| t.as_ref().is_some_and(|t| t.as_ref().is_type_param_kind()));
            let should_skip = step.rule.is_assumption();

            if should_skip && !step.clause.has_any_variable() && !has_type_params {
                let Some(cs) = concrete_steps.remove(&concrete_id) else {
                    continue;
                };
                for clause in cs.to_clauses(kernel_context) {
                    skip_clauses.insert(clause);
                }
            }
        }

        // Collect all concrete specializations in order.
        //
        // Emit specialized assumptions before derived proof-step claims.
        // The checker cannot instantiate generic assumptions on its own, so a derived
        // concrete clause like `not bar[Bool](foo)` must come after the concrete
        // specialization of the source assumption it depends on, such as
        // `not bar[Bool](foo) or baz`.
        let mut claim_index: HashMap<Clause, usize> = HashMap::new();
        let mut steps_in_order: Vec<ConcreteStep> = Vec::new();
        for assumption_phase in [true, false] {
            for (ps_id, _) in &self.steps {
                let concrete_ids = if assumption_phase {
                    [ConcreteStepId::Assumption(*ps_id)]
                } else {
                    [ConcreteStepId::ProofStep(*ps_id)]
                };
                for concrete_id in concrete_ids {
                    let Some(cs) = concrete_steps.remove(&concrete_id) else {
                        continue;
                    };
                    let ConcreteStep {
                        generic, var_maps, ..
                    } = cs;
                    for (var_map, replacement_context) in var_maps {
                        push_concrete_step_if_new(
                            ConcreteStep {
                                generic: generic.clone(),
                                var_maps: vec![(var_map, replacement_context)],
                            },
                            &mut claim_index,
                            &mut steps_in_order,
                            &skip_clauses,
                            kernel_context,
                        );
                    }
                }
            }
        }

        for (_, step) in &self.steps {
            append_inline_simplification_originals(
                step,
                &reconstructed_steps,
                &mut claim_index,
                &mut steps_in_order,
                &skip_clauses,
                kernel_context,
            );
        }

        Ok(steps_in_order)
    }

    /// Create a concrete proof from this proof.
    /// This is an intermediate representation between Proof and Certificate.
    pub fn make_concrete_proof(&self, goal: String) -> Result<ConcreteProof, Error> {
        let kernel_context = self.kernel_context;
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
// The varmaps should fully instantiate the clause into a ground clause with no free variables.
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
        Rule::PassiveContradiction(_) => {
            // Passive contradictions rely on inhabited instances of the contradictory
            // passive clauses, so reconstruct those concrete specializations explicitly.
            for id in step.rule.premises() {
                let premise_clause = resolver.get_clause(id)?;
                let (var_map, context) = passive_contradiction_var_map(resolver, premise_clause)?;
                add_var_map(resolver, id, var_map, context, concrete_steps);
            }
            return Ok(());
        }

        Rule::MultipleRewrite(_) => {
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
    use crate::kernel::proof_step::ProofStepId;
    use crate::kernel::proof_step::{PremiseMap, ProofStep, Rule, Truthiness};
    use crate::kernel::proof_step::{SimplificationInfo, SingleSourceInfo};
    use crate::kernel::term::Term;
    use crate::kernel::variable_map::VariableMap;
    use crate::module::ModuleId;
    use crate::prover::active_set::ActiveSet;
    use crate::prover::proof::{
        add_var_map, append_inline_simplification_originals, ConcreteStep, ConcreteStepId, Proof,
        ProofResolver,
    };
    use crate::prover::synthetic::WitnessRegistry;
    use std::collections::{HashMap, HashSet};

    /// Test helper that threads synthetic witness state through active-set activation.
    fn activate_test(
        active_set: &mut ActiveSet,
        step: ProofStep,
        kernel_context: &mut KernelContext,
        synthetic_witnesses: &mut WitnessRegistry,
    ) -> (usize, Vec<ProofStep>) {
        active_set.activate(
            step,
            kernel_context,
            synthetic_witnesses,
            ModuleId::default(),
        )
    }

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
        let mut synthetic_witnesses = WitnessRegistry::new();
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
        activate_test(
            &mut active_set,
            long_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        activate_test(
            &mut active_set,
            simp_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);
        activate_test(
            &mut active_set,
            short_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

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

    #[test]
    fn test_collect_concrete_steps_preserves_proof_step_specialization_maps() {
        let mut kernel_context = KernelContext::new();
        let (base_step, mid_step, final_step, mid_clause, c1_term) = {
            let kernel = &mut kernel_context;
            kernel
                .parse_constant("g0", "(Bool, Bool) -> Bool")
                .parse_constant("c0", "Bool")
                .parse_constant("c1", "Bool");

            let base_clause = kernel.parse_clause("g0(x0, x1)", &["Bool", "Bool"]);
            let base_step = ProofStep::mock_from_clause(base_clause.clone());

            let mid_clause = kernel.parse_clause("g0(c0, x0)", &["Bool"]);
            let mut base_map = VariableMap::new();
            base_map.set(0, kernel.parse_term("c0"));
            base_map.set(1, Term::new_variable(0));
            let mid_step = ProofStep::specialization(
                0,
                0,
                &base_step,
                mid_clause.clone(),
                PremiseMap::new(
                    vec![base_map],
                    vec![0],
                    mid_clause.get_local_context().clone(),
                ),
            );

            let final_clause = kernel.parse_clause("g0(c0, c1)", &[]);
            let mut mid_map = VariableMap::new();
            mid_map.set(0, kernel.parse_term("c1"));
            let final_step = ProofStep::specialization(
                1,
                1,
                &mid_step,
                final_clause,
                PremiseMap::new(vec![mid_map], vec![], LocalContext::empty()),
            );

            (
                base_step,
                mid_step,
                final_step,
                mid_clause,
                kernel.parse_term("c1"),
            )
        };

        // Add Active(1) before Active(0) so the first emitted concrete step is from Active(1).
        let mut proof = Proof::new(&kernel_context);
        proof.add_step(ProofStepId::Active(1), &mid_step);
        proof.add_step(ProofStepId::Active(0), &base_step);
        proof.add_step(ProofStepId::Final, &final_step);

        let steps = proof
            .collect_concrete_steps()
            .expect("concrete step collection should succeed");

        let has_mid_specialization = steps.iter().any(|step| {
            if step.generic != mid_clause {
                return false;
            }
            step.var_maps
                .iter()
                .any(|(var_map, _)| var_map.get_mapping(0) == Some(&c1_term))
        });

        assert!(
            has_mid_specialization,
            "expected to keep Active(1)'s generic clause with specialization x0 -> c1"
        );
    }

    #[test]
    fn test_collect_concrete_steps_keeps_simplified_concrete_assumption_output() {
        use crate::kernel::literal::Literal;

        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2"], "Bool");

        let not_b_step = ProofStep::mock_from_clause(kctx.parse_clause("not c1", &[]));

        let and_term = Term::and(kctx.parse_term("c0"), kctx.parse_term("c2"));
        let original_step = ProofStep::mock_from_clause(Clause::new(
            vec![
                Literal::positive(and_term.clone()),
                Literal::positive(kctx.parse_term("c1")),
            ],
            &LocalContext::empty(),
        ));

        let simplified_clause =
            Clause::new(vec![Literal::positive(and_term)], &LocalContext::empty());
        let simplified_step = ProofStep {
            clause: simplified_clause.clone(),
            truthiness: original_step.truthiness,
            rule: Rule::Simplification(SimplificationInfo {
                original: Box::new(original_step),
                simplifying_ids: vec![0],
            }),
            proof_size: 1,
            depth: 0,
            premise_map: PremiseMap::new(vec![VariableMap::new()], vec![], LocalContext::empty()),
        };

        let reduced_clause = simplified_clause
            .boolean_reductions(&kctx)
            .into_iter()
            .next()
            .expect("expected conjunction to boolean-reduce");
        let final_step = ProofStep::direct(
            &simplified_step,
            Rule::BooleanReduction(SingleSourceInfo { id: 1 }),
            reduced_clause,
            PremiseMap::new(vec![VariableMap::new()], vec![], LocalContext::empty()),
        );

        let mut proof = Proof::new(&kctx);
        proof.add_step(ProofStepId::Active(0), &not_b_step);
        proof.add_step(ProofStepId::Active(1), &simplified_step);
        proof.add_step(ProofStepId::Final, &final_step);

        let concrete_clauses: Vec<_> = proof
            .collect_concrete_steps()
            .expect("concrete step reconstruction should succeed")
            .into_iter()
            .flat_map(|step| step.to_clauses(&kctx))
            .collect();

        assert!(
            concrete_clauses.contains(&simplified_clause),
            "expected reconstructed clauses to keep simplified assumption output {}\nactual clauses:\n{}",
            simplified_clause,
            concrete_clauses
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    #[test]
    fn test_append_inline_simplification_originals_replays_concrete_specialization() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constant("c0", "Bool");

        let simplifying_clause = kctx.parse_clause("g0(x0)", &["Bool"]);
        let source_clause = kctx.parse_clause("g0(c0)", &[]);
        let reduced_clause = kctx.parse_clause("not g0(x0)", &["Bool"]);

        let source_step = ProofStep::mock_from_clause(source_clause);
        let original_step = ProofStep::direct(
            &source_step,
            Rule::BooleanReduction(SingleSourceInfo { id: 1 }),
            reduced_clause.clone(),
            PremiseMap::empty(),
        );
        let simplification_step = ProofStep {
            clause: Clause::impossible(),
            truthiness: original_step.truthiness,
            rule: Rule::Simplification(SimplificationInfo {
                original: Box::new(original_step),
                simplifying_ids: vec![0],
            }),
            proof_size: 1,
            depth: 0,
            premise_map: PremiseMap::empty(),
        };

        let mut premise_map = VariableMap::new();
        premise_map.set(0, kctx.parse_term("c0"));
        let reconstructed_steps = HashMap::from([(
            ConcreteStepId::ProofStep(ProofStepId::Active(0)),
            ConcreteStep {
                generic: simplifying_clause,
                var_maps: vec![(premise_map, LocalContext::empty())],
            },
        )]);
        let mut claim_index = HashMap::new();
        let mut steps_in_order = Vec::new();

        append_inline_simplification_originals(
            &simplification_step,
            &reconstructed_steps,
            &mut claim_index,
            &mut steps_in_order,
            &HashSet::new(),
            &kctx,
        );

        let concrete_clauses: Vec<_> = steps_in_order
            .into_iter()
            .flat_map(|step| step.to_clauses(&kctx))
            .collect();
        let expected = kctx.parse_clause("not g0(c0)", &[]);

        assert!(
            concrete_clauses.contains(&expected),
            "expected inline simplification original to specialize to {}\nactual clauses:\n{}",
            expected,
            concrete_clauses
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        );
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
        let mut synthetic_witnesses = WitnessRegistry::new();
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
        activate_test(
            &mut active_set,
            long_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        activate_test(
            &mut active_set,
            simp_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);
        activate_test(
            &mut active_set,
            short_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

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
        let mut synthetic_witnesses = WitnessRegistry::new();
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
        activate_test(
            &mut active_set,
            long_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        activate_test(
            &mut active_set,
            simp_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        // Find resolution between long and short
        let mut resolution_results = vec![];
        active_set.find_resolutions(&short_step, &mut resolution_results, &kctx);
        activate_test(
            &mut active_set,
            short_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

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

    /// Regression test for certificate generation with named witnesses:
    /// a replacement-context witness for `Bool -> Bool` is lambda-shaped (identity),
    /// so cert generation must compute lambda types without panicking.
    #[test]
    fn test_make_cert_handles_lambda_witness_in_replacement_context() {
        let kctx = KernelContext::new();
        let generic_clause = kctx.parse_clause("x0", &["Bool", "Bool -> Bool"]);
        let base_step = ProofStep::mock_from_clause(generic_clause.clone());

        // Keep x0 as a replacement-context variable so cert generation must materialize
        // a witness for its type (which is lambda-shaped in this mode).
        let mut premise_var_map = VariableMap::new();
        premise_var_map.set(0, Term::new_variable(0));
        let replacement_context = generic_clause.get_local_context().clone();

        let final_clause = premise_var_map
            .specialize_clause_with_replacement_context_and_compact_vars(
                &generic_clause,
                &replacement_context,
                &kctx,
            );

        let final_step = ProofStep::specialization(
            0,
            0,
            &base_step,
            final_clause,
            PremiseMap::new(vec![premise_var_map], vec![], replacement_context),
        );

        let mut proof = Proof::new(&kctx);
        proof.add_step(ProofStepId::Active(0), &base_step);
        proof.add_step(ProofStepId::Final, &final_step);

        let bindings =
            crate::elaborator::binding_map::BindingMap::new(crate::module::ModuleId::default());
        let cert = proof
            .make_cert("goal".to_string(), &bindings)
            .expect("certificate generation should succeed");
        let lines = cert.proof.expect("proof lines should exist");
        assert!(
            !lines.is_empty(),
            "expected at least one generated certificate line"
        );
    }

    /// Regression: cert parsing must accept constant-lambda claim arguments.
    /// This shape is produced by explicit inhabitant witnesses for function types.
    #[test]
    fn test_make_cert_constant_lambda_claim_arg_roundtrip() {
        use crate::certificate::Certificate;
        use crate::elaborator::binding_map::BindingMap;
        use crate::module::ModuleId;
        use crate::project::Project;
        use std::borrow::Cow;

        let kctx = KernelContext::new();
        let generic_clause = kctx.parse_clause("x0(x1)", &["Bool -> Bool", "Bool"]);
        let mut var_map = VariableMap::new();
        // Constant lambda: binder exists, but the body ignores it.
        var_map.set(0, Term::lambda(Term::bool_type(), Term::new_true()));
        var_map.set(1, Term::new_true());
        let concrete_steps = vec![crate::prover::proof::ConcreteStep {
            generic: generic_clause,
            var_maps: vec![(var_map, LocalContext::empty())],
        }];

        let bindings = BindingMap::new(ModuleId::default());
        let cert =
            Certificate::from_concrete_steps("goal".to_string(), &concrete_steps, &kctx, &bindings)
                .expect("certificate generation should succeed");
        let lines = cert.proof.expect("proof lines should exist");

        // Repro assertion: currently this generated cert does not round-trip through parser.
        let project = Project::new_mock();
        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Borrowed(&kctx);
        let steps = Certificate::parse_cert_steps(
            &lines,
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        )
        .expect("constant-lambda claim argument should parse");
        assert_eq!(steps.len(), 1, "expected one claim step");
    }

    #[test]
    #[should_panic(expected = "ConcreteStep invariant violated")]
    fn test_concrete_step_validation_rejects_live_locals() {
        let kctx = KernelContext::new();
        let generic_clause = kctx.parse_clause("x0", &["Bool"]);
        let step = crate::prover::proof::ConcreteStep {
            generic: generic_clause,
            var_maps: vec![(VariableMap::new(), LocalContext::empty())],
        };

        step.validate_specializes_to_concrete_clauses(&kctx);
    }

    #[test]
    fn test_exists_conjunction_reconstruction_preserves_concrete_simplifying_instantiation() {
        use crate::kernel::literal::Literal;
        use crate::kernel::proof_step::Truthiness;

        let mut kctx = KernelContext::new();
        let mut synthetic_witnesses = WitnessRegistry::new();
        kctx.parse_type_constructor("Foo", 0);
        kctx.parse_constant("c0", "Foo")
            .parse_constant("g0", "Foo -> Bool")
            .parse_constant("g1", "Foo -> Bool")
            .parse_constant("g2", "(Foo, Foo) -> Bool")
            .parse_constant("g3", "(Foo, Foo) -> Bool");

        let neg_goal = {
            let clause = kctx.parse_clause("not g2(c0, x0) or not g3(x0, x1)", &["Foo", "Foo"]);
            let mut step = ProofStep::mock_from_clause(clause);
            step.truthiness = Truthiness::Counterfactual;
            step
        };
        let axiom1 = {
            let clause = kctx.parse_clause("not g0(x0) or g1(x0)", &["Foo"]);
            let mut step = ProofStep::mock_from_clause(clause);
            step.truthiness = Truthiness::Factual;
            step
        };
        let axiom2 = {
            let foo_type = kctx.parse_type("Foo");
            let exists_body =
                Term::and(kctx.parse_term("g2(x0, b1)"), kctx.parse_term("g3(b1, b0)"));
            let exists_term = Term::exists(
                foo_type.clone(),
                Term::exists(foo_type.clone(), exists_body),
            );
            let clause = Clause::new(
                vec![
                    Literal::negative(kctx.parse_term("g1(x0)")),
                    Literal::positive(exists_term),
                ],
                &LocalContext::from_types(vec![foo_type]),
            );
            let mut step = ProofStep::mock_from_clause(clause);
            step.truthiness = Truthiness::Factual;
            step
        };
        let hyp = {
            let clause = kctx.parse_clause("g0(c0)", &[]);
            let mut step = ProofStep::mock_from_clause(clause);
            step.truthiness = Truthiness::Hypothetical;
            step
        };

        let mut active = ActiveSet::new();
        let (_neg_goal_id, _) = activate_test(
            &mut active,
            neg_goal.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        let (_axiom1_id, _) = activate_test(
            &mut active,
            axiom1.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        let (_axiom2_id, _) = activate_test(
            &mut active,
            axiom2.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        let (_hyp_id, hyp_outputs) = activate_test(
            &mut active,
            hyp.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let g_clause = kctx.parse_clause("g1(c0)", &[]);
        let g_step = hyp_outputs
            .into_iter()
            .find(|step| step.clause == g_clause)
            .expect("expected g0(c0) to resolve to g1(c0)");
        let (_g_id, g_outputs) = activate_test(
            &mut active,
            g_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let foo_type = kctx.parse_type("Foo");
        let exists_body = Term::and(kctx.parse_term("g2(c0, b1)"), kctx.parse_term("g3(b1, b0)"));
        let exists_clause = Clause::new(
            vec![Literal::positive(Term::exists(
                foo_type.clone(),
                Term::exists(foo_type, exists_body),
            ))],
            &LocalContext::empty(),
        );
        let exists_step = g_outputs
            .into_iter()
            .find(|step| step.clause == exists_clause)
            .expect("expected g(a) to resolve to existential");
        let (exists_id, exists_outputs) = activate_test(
            &mut active,
            exists_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        assert_eq!(exists_id, 5);

        let inner_exists_step = exists_outputs
            .into_iter()
            .find(|step| step.clause.to_string().starts_with("exists("))
            .expect("expected inner existential after the first witness reduction");
        let (_inner_exists_id, inner_exists_outputs) = activate_test(
            &mut active,
            inner_exists_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let conjunction_step = inner_exists_outputs
            .iter()
            .find(|step| step.clause.to_string().starts_with("and("))
            .cloned()
            .expect("expected conjunction after the second witness reduction");
        let (_conjunction_id, conjunction_outputs) = activate_test(
            &mut active,
            conjunction_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let h1_step = conjunction_outputs
            .iter()
            .find(|step| step.clause.to_string().starts_with("g0_2("))
            .cloned()
            .expect("expected first conjunct");
        let h2_step = conjunction_outputs
            .iter()
            .find(|step| step.clause.to_string().starts_with("g0_3("))
            .cloned()
            .expect("expected second conjunct");

        let (_h1_id, h1_outputs) = activate_test(
            &mut active,
            h1_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let (_h2_id, _h2_outputs) = activate_test(
            &mut active,
            h2_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );

        let not_h2_step = h1_outputs
            .iter()
            .find(|step| step.clause.to_string().starts_with("not g0_3("))
            .cloned()
            .expect("expected negative g3 clause");
        let (not_h2_id, _not_h2_outputs) = activate_test(
            &mut active,
            not_h2_step.clone(),
            &mut kctx,
            &mut synthetic_witnesses,
        );
        assert_eq!(not_h2_id, 10);

        let simplified_h2 = active
            .simplify(h2_step.clone(), &kctx)
            .expect("expected h2 step to simplify");
        assert!(
            simplified_h2.clause.is_impossible(),
            "expected contradiction, got {}",
            simplified_h2.clause
        );

        let mut proof = Proof::new(&kctx);
        for id in 0..=10 {
            proof.add_step(ProofStepId::Active(id), active.get_step(id));
        }
        proof.add_step(ProofStepId::Final, &simplified_h2);

        let concrete_clauses: Vec<_> = proof
            .collect_concrete_steps()
            .expect("concrete step reconstruction should succeed")
            .into_iter()
            .flat_map(|step| step.to_clauses(&kctx))
            .collect();

        let expected_negative_h2 = Clause::new(
            vec![Literal::negative(h2_step.clause.literals[0].left.clone())],
            &LocalContext::empty(),
        );
        assert!(
            concrete_clauses.contains(&expected_negative_h2),
            "expected reconstructed clauses to include the concrete simplifying clause {}\nactual clauses:\n{}",
            expected_negative_h2,
            concrete_clauses
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}
