use std::cmp::Ordering;
use std::fmt;

use crate::elaborator::source::{Source, SourceType};
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{Decomposition, PathStep, Term, TermRef};
use crate::kernel::variable_map::{self, VariableMap};

/// The different sorts of proof steps.
#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub enum ProofStepId {
    /// A proof step that was activated and exists in the active set.
    Active(usize),

    /// A proof step that was never activated, but was used to find a contradiction.
    Passive(u32),

    /// The final step of a proof.
    /// No active id because it never gets inserted into the active set.
    Final,
}

impl ProofStepId {
    pub fn active_id(&self) -> Option<usize> {
        match self {
            ProofStepId::Active(id) => Some(*id),
            _ => None,
        }
    }
}

/// The "truthiness" categorizes the different types of true statements, relative to a proof.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Truthiness {
    /// A "factual" truth is true globally, regardless of this particular proof.
    Factual,

    /// A "hypothetical" truth is something that we are assuming true in the context of this proof.
    /// For example, we might assume that a and b are nonzero, and then prove that a * b != 0.
    Hypothetical,

    /// When we want to prove a goal G, we tell the prover that !G is true, and search
    /// for contradictions.
    /// A "counterfactual" truth is this negated goal, or something derived from it, that we expect
    /// to lead to a contradiction.
    Counterfactual,
}

impl Truthiness {
    /// When combining truthinesses, the result is the "most untruthy" of the two.
    pub fn combine(&self, other: Truthiness) -> Truthiness {
        match (self, other) {
            (Truthiness::Counterfactual, _) => Truthiness::Counterfactual,
            (_, Truthiness::Counterfactual) => Truthiness::Counterfactual,
            (Truthiness::Hypothetical, _) => Truthiness::Hypothetical,
            (_, Truthiness::Hypothetical) => Truthiness::Hypothetical,
            (Truthiness::Factual, Truthiness::Factual) => Truthiness::Factual,
        }
    }
}

/// Information about a resolution inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionInfo {
    /// Which clauses were used as the sources.
    /// The short clause must have only one literal.
    pub short_id: usize,

    /// The long clause will usually have more than one literal. It can have just one literal
    /// if we're finding a contradiction.
    pub long_id: usize,
}

/// Information about a specialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecializationInfo {
    /// The specialization is taking the pattern and substituting in particular values.
    pub pattern_id: usize,

    /// The inspiration isn't mathematically necessary for the specialization to be true,
    /// but we used it to decide which substitutions to make.
    pub inspiration_id: usize,
}

/// Information about a rewrite inference.
/// Rewrites have two parts, the "pattern" that determines what gets rewritten into what,
/// and the "target" which contains the subterm that gets rewritten.
/// Both of these parts are single-literal clauses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteInfo {
    /// Which clauses were used as the sources.
    pub pattern_id: usize,
    pub target_id: usize,
}

/// Information about a contradiction found by rewriting one side of an inequality into the other.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MultipleRewriteInfo {
    /// The id of the inequality clause.
    pub inequality_id: usize,
    /// The ids of active clauses used in the rewrite chain.
    pub active_ids: Vec<usize>,
    /// The ids of passive clauses used in the rewrite chain.
    pub passive_ids: Vec<u32>,
}

/// Information about an assumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssumptionInfo {
    /// The source of the assumption.
    pub source: Source,

    /// The literals of the assumption before any simplification.
    pub literals: Vec<Literal>,

    /// The local context for the literals (variable types).
    pub context: LocalContext,
}

/// Information about an inference rule with a single source clause.
/// Used for equality factoring, equality resolution, injectivity,
/// boolean reduction, and extensionality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleSourceInfo {
    /// The id of the source clause.
    pub id: usize,
}

/// Information about a simplification step.
/// The original step is stored inline (not referenced by ID) because it was never activated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimplificationInfo {
    /// The original proof step before simplification.
    pub original: Box<ProofStep>,
    /// Active IDs of clauses used for this simplification.
    pub simplifying_ids: Vec<usize>,
}

/// The rules that can generate new clauses, along with the clause ids used to generate.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Rule {
    Assumption(AssumptionInfo),

    /// Rules based on multiple source clauses
    Resolution(ResolutionInfo),
    Rewrite(RewriteInfo),
    Specialization(SpecializationInfo),

    /// Rules with only one source clause
    EqualityFactoring(SingleSourceInfo),
    EqualityResolution(SingleSourceInfo),
    Injectivity(SingleSourceInfo),
    BooleanReduction(SingleSourceInfo),
    Extensionality(SingleSourceInfo),

    /// A contradiction found by repeatedly rewriting identical terms.
    MultipleRewrite(MultipleRewriteInfo),

    /// A contradiction between a number of passive clauses.
    PassiveContradiction(u32),

    /// Simplification of a proof step using existing single-literal clauses.
    /// Can nest: a Simplification can wrap another Simplification.
    Simplification(SimplificationInfo),
}

impl Rule {
    /// The ids of the clauses that this rule mathematically depends on.
    pub fn premises(&self) -> Vec<ProofStepId> {
        match self {
            Rule::Assumption(_) => vec![],
            Rule::Resolution(info) => vec![
                ProofStepId::Active(info.short_id),
                ProofStepId::Active(info.long_id),
            ],
            Rule::Rewrite(info) => vec![
                ProofStepId::Active(info.pattern_id),
                ProofStepId::Active(info.target_id),
            ],
            Rule::EqualityFactoring(info) => vec![ProofStepId::Active(info.id)],
            Rule::EqualityResolution(info) => vec![ProofStepId::Active(info.id)],
            Rule::Injectivity(info) => vec![ProofStepId::Active(info.id)],
            Rule::BooleanReduction(info) => vec![ProofStepId::Active(info.id)],
            Rule::Extensionality(info) => vec![ProofStepId::Active(info.id)],
            Rule::Specialization(info) => vec![ProofStepId::Active(info.pattern_id)],
            Rule::MultipleRewrite(multi_rewrite_info) => {
                let mut answer = vec![ProofStepId::Active(multi_rewrite_info.inequality_id)];
                for id in &multi_rewrite_info.active_ids {
                    answer.push(ProofStepId::Active(*id));
                }
                for id in &multi_rewrite_info.passive_ids {
                    answer.push(ProofStepId::Passive(*id));
                }
                answer
            }
            Rule::PassiveContradiction(n) => (0..*n).map(|id| ProofStepId::Passive(id)).collect(),
            Rule::Simplification(info) => info
                .simplifying_ids
                .iter()
                .map(|id| ProofStepId::Active(*id))
                .collect(),
        }
    }

    /// Returns a human-readable name for this rule.
    pub fn name(&self) -> &str {
        match self {
            Rule::Assumption(_) => "Assumption",
            Rule::Resolution(_) => "Resolution",
            Rule::Rewrite(_) => "Rewrite",
            Rule::EqualityFactoring(_) => "Equality Factoring",
            Rule::EqualityResolution(_) => "Equality Resolution",
            Rule::Injectivity(_) => "Injectivity",
            Rule::BooleanReduction(_) => "Boolean Reduction",
            Rule::Extensionality(_) => "Extensionality",
            Rule::Specialization(_) => "Specialization",
            Rule::MultipleRewrite(..) => "Multiple Rewrite",
            Rule::PassiveContradiction(..) => "Passive Contradiction",
            Rule::Simplification(..) => "Simplification",
        }
    }

    pub fn is_rewrite(&self) -> bool {
        matches!(self, Rule::Rewrite(_))
    }

    pub fn is_assumption(&self) -> bool {
        matches!(self, Rule::Assumption(_))
    }

    pub fn is_negated_goal(&self) -> bool {
        match self {
            Rule::Assumption(info) => matches!(info.source.source_type, SourceType::NegatedGoal),
            _ => false,
        }
    }

    /// Whether this rule is, or wraps, an assumption (following through Simplification layers).
    pub fn is_underlying_assumption(&self) -> bool {
        match self {
            Rule::Assumption(_) => true,
            Rule::Simplification(info) => info.original.rule.is_underlying_assumption(),
            _ => false,
        }
    }

    /// Whether this rule is, or wraps, a negated goal (following through Simplification layers).
    pub fn is_underlying_negated_goal(&self) -> bool {
        match self {
            Rule::Assumption(info) => matches!(info.source.source_type, SourceType::NegatedGoal),
            Rule::Simplification(info) => info.original.rule.is_underlying_negated_goal(),
            _ => false,
        }
    }
}

/// Stores the inference variable bindings needed to reconstruct proof premises.
///
/// Built at step creation time from the raw unification results and normalization trace.
/// At reconstruction time, these are composed with a conclusion_map to produce
/// concrete variable maps for each premise.
///
/// Stores raw inference var maps (premise vars → pre-norm terms) rather than
/// pre-composed maps, because inference bindings may reference variables that
/// are eliminated during normalization. These eliminated variables still encode
/// structural relationships needed for correct reconstruction (e.g., if ER
/// resolves x2 = List.cons(x0, x1), then x2 must map to the same concrete term
/// as List.cons(x0, x1), even if x1 is eliminated from the output clause).
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct PremiseMap {
    /// One entry per premise, parallel to Rule::premises().
    /// Maps premise vars → pre-normalization output terms.
    /// An empty VariableMap means the premise is concrete (no variables to map).
    raw_maps: Vec<VariableMap>,

    /// Normalization trace: var_ids[new_sequential_id] = old_pre_norm_id.
    /// Used to map between pre-norm and post-norm variable namespaces.
    var_ids: Vec<AtomId>,

    /// The local context for the pre-normalization output variables.
    /// Used to look up types for eliminated variables when assigning fresh IDs.
    pre_norm_context: LocalContext,
}

impl PremiseMap {
    pub fn empty() -> PremiseMap {
        PremiseMap {
            raw_maps: vec![],
            var_ids: vec![],
            pre_norm_context: LocalContext::empty(),
        }
    }

    pub fn new(
        raw_maps: Vec<VariableMap>,
        var_ids: Vec<AtomId>,
        pre_norm_context: LocalContext,
    ) -> PremiseMap {
        PremiseMap {
            raw_maps,
            var_ids,
            pre_norm_context,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.raw_maps.is_empty()
    }

    /// Compute the inner step's conclusion map for Simplification reconstruction.
    /// Maps pre-norm variables to concrete terms using var_ids and the outer conclusion_map.
    ///
    /// For surviving variables (in var_ids): maps through conclusion_map.
    /// For eliminated variables (not in var_ids): assigns fresh variable IDs.
    ///
    /// Returns (pre_norm_map, concrete_context) where concrete_context has types
    /// for all variables referenced by pre_norm_map's replacement terms.
    pub fn inner_step_map(
        &self,
        conclusion_map: &VariableMap,
        conclusion_context: &LocalContext,
        inner_step_context: &LocalContext,
    ) -> (VariableMap, LocalContext) {
        let mut map = VariableMap::new();
        let mut context = conclusion_context.clone();

        // Map surviving pre-norm vars through conclusion_map
        for (new_id, &old_id) in self.var_ids.iter().enumerate() {
            if let Some(concrete_term) = conclusion_map.get_mapping(new_id as AtomId) {
                map.set(old_id, concrete_term.clone());
            } else {
                // Variable not in conclusion_map: keep as identity.
                // Ensure the output context has the type for this variable.
                map.set(old_id, Term::atom(Atom::FreeVariable(new_id as AtomId)));
                if let Some(var_type) = inner_step_context.get_var_type(old_id as usize) {
                    context.set_type(new_id, var_type.clone());
                }
            }
        }

        // Assign fresh IDs for eliminated variables in the inner step
        let mut next_fresh = self.var_ids.len().max(conclusion_context.len());
        for var_id in 0..inner_step_context.len() {
            if !map.has_mapping(var_id as AtomId) {
                if let Some(var_type) = inner_step_context.get_var_type(var_id) {
                    let fresh_id = next_fresh as AtomId;
                    map.set(var_id as AtomId, Term::atom(Atom::FreeVariable(fresh_id)));
                    context.set_type(next_fresh, var_type.clone());
                    next_fresh += 1;
                }
            }
        }

        (map, context)
    }

    /// Given how the conclusion was concretized, produce how each premise
    /// should be concretized.
    ///
    /// conclusion_map maps output clause vars → concrete terms.
    /// premise_contexts provides the LocalContext for each premise clause,
    /// needed to look up types for eliminated variables.
    ///
    /// Returns one (VariableMap, LocalContext) per premise.
    pub fn concretize_premises(
        &self,
        conclusion_map: &VariableMap,
        conclusion_context: &LocalContext,
        premise_contexts: &[&LocalContext],
    ) -> Vec<(VariableMap, LocalContext)> {
        // Step 1: Build pre-norm → concrete mapping.
        // For surviving pre-norm vars (in var_ids): compose with conclusion_map.
        // For eliminated pre-norm vars: assign fresh concrete variable IDs.
        let mut pre_norm_concrete = VariableMap::new();

        // Start with all types from conclusion_context, since composed terms
        // may reference any variable in the conclusion_map's replacement terms.
        let mut concrete_context = conclusion_context.clone();

        // Map surviving pre-norm vars to concrete terms
        for (new_id, &old_id) in self.var_ids.iter().enumerate() {
            if let Some(concrete_term) = conclusion_map.get_mapping(new_id as AtomId) {
                pre_norm_concrete.set(old_id, concrete_term.clone());
            } else {
                // Output var not in conclusion_map: keep as identity
                pre_norm_concrete.set(old_id, Term::atom(Atom::FreeVariable(new_id as AtomId)));
            }
        }

        // Find eliminated pre-norm vars referenced in any raw map and assign fresh IDs.
        // Fresh IDs must not collide with existing variables in the conclusion context.
        // We collect from ALL premises first to ensure consistency (same eliminated
        // pre-norm var gets the same fresh ID across all premises).
        let mut next_fresh = self.var_ids.len().max(conclusion_context.len());
        for raw_map in &self.raw_maps {
            for (_, term) in raw_map.iter() {
                self.assign_fresh_for_eliminated(
                    term.as_ref(),
                    &mut pre_norm_concrete,
                    &mut concrete_context,
                    &mut next_fresh,
                );
            }
        }

        // Step 2: For each premise, compose raw_map with pre_norm_concrete.
        self.raw_maps
            .iter()
            .enumerate()
            .map(|(premise_idx, raw_map)| {
                let mut result = VariableMap::new();

                // Handle explicitly bound premise vars
                for (var_id, term) in raw_map.iter() {
                    result.set(
                        var_id as AtomId,
                        variable_map::apply_to_term(term.as_ref(), &pre_norm_concrete),
                    );
                }

                // Handle identity pass-through for unmapped premise vars.
                // These are premise vars that weren't bound by unification and
                // correspond to pre-norm vars (same ID in the premise = same ID pre-norm).
                if let Some(premise_ctx) = premise_contexts.get(premise_idx) {
                    for var_id in 0..premise_ctx.len() {
                        let var_id_atom = var_id as AtomId;
                        if !raw_map.has_mapping(var_id_atom) {
                            if let Some(concrete_term) = pre_norm_concrete.get_mapping(var_id_atom)
                            {
                                result.set(var_id_atom, concrete_term.clone());
                            }
                        }
                    }
                }

                // Use concrete_context which has types for both conclusion vars
                // and fresh extended vars (for eliminated pre-norm variables).
                let output_ctx = result.build_output_context(&concrete_context);
                (result, output_ctx)
            })
            .collect()
    }

    /// Recursively find eliminated pre-norm variables in a term and assign fresh IDs.
    fn assign_fresh_for_eliminated(
        &self,
        term: TermRef,
        pre_norm_concrete: &mut VariableMap,
        concrete_context: &mut LocalContext,
        next_fresh: &mut usize,
    ) {
        match term.decompose() {
            Decomposition::Atom(Atom::FreeVariable(var_id)) => {
                if !pre_norm_concrete.has_mapping(*var_id) {
                    let fresh_id = *next_fresh as AtomId;
                    pre_norm_concrete.set(*var_id, Term::atom(Atom::FreeVariable(fresh_id)));
                    // Get type from the pre-normalization context
                    if let Some(ty) = self.pre_norm_context.get_var_type(*var_id as usize) {
                        concrete_context.set_type(*next_fresh, ty.clone());
                    }
                    *next_fresh += 1;
                }
            }
            Decomposition::Atom(_) => {}
            Decomposition::Application(func, arg) => {
                self.assign_fresh_for_eliminated(
                    func,
                    pre_norm_concrete,
                    concrete_context,
                    next_fresh,
                );
                self.assign_fresh_for_eliminated(
                    arg,
                    pre_norm_concrete,
                    concrete_context,
                    next_fresh,
                );
            }
            Decomposition::Pi(input, output) => {
                self.assign_fresh_for_eliminated(
                    input,
                    pre_norm_concrete,
                    concrete_context,
                    next_fresh,
                );
                self.assign_fresh_for_eliminated(
                    output,
                    pre_norm_concrete,
                    concrete_context,
                    next_fresh,
                );
            }
        }
    }
}

/// A proof is made up of ProofSteps.
/// Each ProofStep contains an output clause, plus a bunch of information we track about it.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ProofStep {
    /// The proof step is primarily defined by a clause that it proves.
    /// Semantically, this clause is implied by the input clauses (activated and existing).
    pub clause: Clause,

    /// Whether this clause is the normal sort of true, or just something we're hypothesizing for
    /// the sake of the proof.
    pub truthiness: Truthiness,

    /// How this clause was generated.
    pub rule: Rule,

    /// The number of proof steps that this proof step depends on.
    /// The size includes this proof step itself, but does not count assumptions and definitions.
    /// So the size for any assumption or definition is zero.
    /// This does not deduplicate among different branches, so it may be an overestimate.
    pub proof_size: u32,

    /// Not every proof step counts toward depth.
    /// When we use a new long clause to resolve against, that counts toward depth, because
    /// it roughly corresponds to "using a theorem".
    /// When we use a rewrite backwards, increasing KBO, that also counts toward depth.
    pub depth: u32,

    /// Maps each premise's variables to this step's clause variables.
    /// Used during proof reconstruction to avoid re-unification.
    pub premise_map: PremiseMap,
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ; rule = {:?}", self.clause, self.rule)
    }
}

impl ProofStep {
    /// Construct a new assumption ProofStep that is not dependent on any other steps.
    /// Assumptions are always depth zero, but eventually we may have to revisit that.
    pub fn assumption(source: &Source, clause: Clause) -> ProofStep {
        let source = source.clone();
        let truthiness = source.truthiness();
        let literals = clause.literals.clone();
        let context = clause.get_local_context().clone();
        let rule = Rule::Assumption(AssumptionInfo {
            source,
            literals,
            context,
        });

        ProofStep {
            clause,
            truthiness,
            rule,
            proof_size: 0,
            depth: 0,
            premise_map: PremiseMap::empty(),
        }
    }

    /// Construct a new ProofStep that is a direct implication of a single activated step,
    /// not requiring any other clauses.
    pub fn direct(
        activated_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        premise_map: PremiseMap,
    ) -> ProofStep {
        // Direct implication does not add to depth.
        let depth = activated_step.depth;

        ProofStep {
            clause,
            truthiness: activated_step.truthiness,
            rule,
            proof_size: activated_step.proof_size + 1,
            depth,
            premise_map,
        }
    }

    /// Construct a ProofStep that is a specialization of a general pattern.
    pub fn specialization(
        pattern_id: usize,
        inspiration_id: usize,
        pattern_step: &ProofStep,
        clause: Clause,
        premise_map: PremiseMap,
    ) -> ProofStep {
        let info = SpecializationInfo {
            pattern_id,
            inspiration_id,
        };
        ProofStep {
            clause,
            truthiness: pattern_step.truthiness,
            rule: Rule::Specialization(info),
            proof_size: pattern_step.proof_size + 1,
            depth: pattern_step.depth,
            premise_map,
        }
    }

    /// Construct a new ProofStep via resolution.
    pub fn resolution(
        long_id: usize,
        long_step: &ProofStep,
        short_id: usize,
        short_step: &ProofStep,
        clause: Clause,
        premise_map: PremiseMap,
    ) -> ProofStep {
        let rule = Rule::Resolution(ResolutionInfo { short_id, long_id });

        let truthiness = short_step.truthiness.combine(long_step.truthiness);
        let proof_size = short_step.proof_size + long_step.proof_size + 1;

        let depth = if long_step.depth <= short_step.depth {
            if long_step.clause.contains(&clause) {
                // This is just a simplification
                short_step.depth
            } else {
                // This resolution is a new "theorem" that we are using.
                // So we need to add one to depth.
                short_step.depth + 1
            }
        } else {
            // This resolution is essentially continuing to resolve a theorem
            // statement that we have already fetched.
            long_step.depth
        };

        ProofStep {
            clause,
            truthiness,
            rule,
            proof_size,
            depth,
            premise_map,
        }
    }

    /// Construct a new ProofStep via rewriting.
    /// We are replacing a subterm of the target literal with a new subterm.
    /// Note that the target step will always be a concrete single literal.
    /// The pattern and the output may have variables in them.
    ///
    /// A "forwards" rewrite goes left-to-right in the pattern.
    pub fn rewrite(
        pattern_id: usize,
        pattern_step: &ProofStep,
        target_id: usize,
        target_step: &ProofStep,
        target_left: bool,
        path: &[PathStep],
        new_subterm: &Term,
        new_subterm_context: &LocalContext,
        pattern_var_map: VariableMap,
    ) -> ProofStep {
        assert_eq!(target_step.clause.literals.len(), 1);

        let target_literal = &target_step.clause.literals[0];
        let (new_literal, _flipped) =
            target_literal.replace_at_path(target_left, path, new_subterm.clone());

        let simplifying = new_literal.extended_kbo_cmp(&target_literal) == Ordering::Less;

        // Build the context from the rewritten literal.
        // Combine the target's context with the new_subterm's context.
        // The rewritten literal's variables come from both the target and the new_subterm.
        let rewritten_context = {
            let target_context = target_step.clause.get_local_context();
            let mut var_types = target_context.get_var_types().to_vec();
            let empty_type = Term::empty_type();
            for (i, vt) in new_subterm_context.get_var_types().iter().enumerate() {
                if i >= var_types.len() {
                    var_types.resize(i + 1, empty_type.clone());
                    var_types[i] = vt.clone();
                } else if var_types[i] == empty_type {
                    var_types[i] = vt.clone();
                }
            }
            LocalContext::from_types(var_types)
        };

        let (clause, var_ids) =
            Clause::normalize_with_var_ids(vec![new_literal], &rewritten_context);

        // Build premise map: pattern gets raw var map, target is concrete (empty map)
        let premise_map = PremiseMap::new(
            vec![pattern_var_map.clone(), VariableMap::new()],
            var_ids,
            rewritten_context,
        );

        let truthiness = pattern_step.truthiness.combine(target_step.truthiness);

        let rule = Rule::Rewrite(RewriteInfo {
            pattern_id,
            target_id,
        });

        let proof_size = pattern_step.proof_size + target_step.proof_size + 1;

        let dependency_depth = std::cmp::max(pattern_step.depth, target_step.depth);
        let depth = if simplifying {
            dependency_depth
        } else {
            dependency_depth + 1
        };

        ProofStep {
            clause,
            truthiness,
            rule,
            proof_size,
            depth,
            premise_map,
        }
    }

    /// A proof step for finding a contradiction via a series of rewrites.
    pub fn multiple_rewrite(
        inequality_id: usize,
        active_ids: Vec<usize>,
        passive_ids: Vec<u32>,
        truthiness: Truthiness,
        depth: u32,
    ) -> ProofStep {
        let rule = Rule::MultipleRewrite(MultipleRewriteInfo {
            inequality_id,
            active_ids,
            passive_ids,
        });

        // proof size is wrong but we don't use it for a contradiction.
        ProofStep {
            clause: Clause::impossible(),
            truthiness,
            rule,
            proof_size: 0,
            depth,
            premise_map: PremiseMap::empty(),
        }
    }

    /// Assumes the provided steps are indexed by passive id, and that we use all of them.
    pub fn passive_contradiction(passive_steps: &[ProofStep]) -> ProofStep {
        let rule = Rule::PassiveContradiction(passive_steps.len() as u32);
        let mut truthiness = Truthiness::Factual;
        let mut depth = 0;
        let mut proof_size = 0;
        for step in passive_steps {
            truthiness = truthiness.combine(step.truthiness);
            depth = std::cmp::max(depth, step.depth);
            proof_size += step.proof_size;
        }

        ProofStep {
            clause: Clause::impossible(),
            truthiness,
            rule,
            proof_size,
            depth,
            premise_map: PremiseMap::empty(),
        }
    }

    /// Construct a ProofStep with fake heuristic data for testing/profiling.
    /// Uses an empty context (no variables).
    pub fn mock(s: &str, kernel: &KernelContext) -> ProofStep {
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;

        let local = LocalContext::empty();
        let literals: Vec<Literal> = s
            .split(" or ")
            .map(|part| Literal::parse(part.trim()))
            .collect();
        let clause = Clause::new(literals, &local);
        clause.validate(kernel);
        Self::mock_from_clause(clause)
    }

    /// Construct a ProofStep with properly typed terms for testing.
    /// var_types[i] is the type string for variable x_i.
    #[cfg(test)]
    pub fn mock_with_types(s: &str, var_types: &[&str], kernel: &KernelContext) -> ProofStep {
        let clause = kernel.parse_clause(s, var_types);
        Self::mock_from_clause(clause)
    }

    pub fn mock_from_clause(clause: Clause) -> ProofStep {
        let truthiness = Truthiness::Factual;
        let literals = clause.literals.clone();
        let context = clause.get_local_context().clone();
        let rule = Rule::Assumption(AssumptionInfo {
            source: Source::mock(),
            literals,
            context,
        });
        ProofStep {
            clause,
            truthiness,
            rule,
            proof_size: 0,
            depth: 0,
            premise_map: PremiseMap::empty(),
        }
    }

    /// The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> Vec<ProofStepId> {
        let mut answer = self.rule.premises();
        if let Rule::Simplification(info) = &self.rule {
            // Include the inline original step's dependencies recursively
            answer.extend(info.original.dependencies());
        }
        answer
    }

    /// include_inspiration is whether we should include the inspiration clause in the dependencies.
    pub fn active_dependencies(&self, include_inspiration: bool) -> Vec<usize> {
        let mut answer: Vec<_> = self
            .dependencies()
            .iter()
            .filter_map(|id| match id {
                ProofStepId::Active(id) => Some(*id),
                _ => None,
            })
            .collect();
        if include_inspiration {
            self.collect_inspiration_ids(&mut answer);
        }
        answer
    }

    /// Collects inspiration IDs from this step and any inline original steps.
    fn collect_inspiration_ids(&self, answer: &mut Vec<usize>) {
        if let Rule::Specialization(info) = &self.rule {
            answer.push(info.inspiration_id);
        }
        if let Rule::Simplification(info) = &self.rule {
            info.original.collect_inspiration_ids(answer);
        }
    }

    pub fn depends_on_active(&self, id: usize) -> bool {
        self.dependencies()
            .iter()
            .any(|i| *i == ProofStepId::Active(id))
    }

    /// Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    pub fn automatic_reject(&self) -> bool {
        // We have to strictly limit deduction that happens between two library facts, because
        // the plan is for the library to grow very large.
        if self.truthiness == Truthiness::Factual && self.proof_size > 2 {
            // Only do one step of deduction with global facts.
            return true;
        }

        // In some degenerate cases going very deep can crash the prover.
        if self.depth >= 30 {
            return true;
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::kernel_context::KernelContext;

    /// Test that the rewritten clause has correct variable types in its context.
    ///
    /// This tests a bug where ProofStep::rewrite used pattern_step's context for
    /// from_literal_traced, but the rewritten literal has variables from both the
    /// target and the new_subterm. This caused variable type lookups to fail
    /// because the pattern's context doesn't have types for variables from the target.
    ///
    /// The specific failure was:
    /// "failed to unify base literal ... with trace literal ..."
    /// because the clause's context didn't match the literal's variables.
    #[test]
    fn test_rewrite_clause_context_matches_variables() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constant("g1", "Bool -> Bool")
            .parse_constant("c0", "Bool");

        // Pattern: g0(x0, x1) = x1
        // Context: [Bool, Bool]
        let pattern_clause = kctx.parse_clause("g0(x0, x1) = x1", &["Bool", "Bool"]);
        let pattern_context = pattern_clause.get_local_context().clone();
        let pattern_step = ProofStep::mock_from_clause(pattern_clause);

        // Target: g1(c0) = c0 (no variables)
        let target_clause = kctx.parse_clause("g1(c0) = c0", &[]);
        let target_step = ProofStep::mock_from_clause(target_clause);

        // new_subterm: g0(x0, c0)
        // This introduces a variable x0 that's NOT in the pattern_step's context
        // (well, it is in this case, but in general it might have different types)
        let new_subterm = Term::parse("g0(x0, c0)");

        let rewrite_step = ProofStep::rewrite(
            0,
            &pattern_step,
            1,
            &target_step,
            true, // target_left - replace g1(c0)
            &[],  // path - at root
            &new_subterm,
            &pattern_context,   // context for new_subterm's variables
            VariableMap::new(), // mock test - empty var map
        );

        // The clause should have all variables in its context
        // In this case, the rewritten literal is g0(x0, c0) = c0
        // which has variable x0
        let clause_context = rewrite_step.clause.get_local_context();
        for lit in &rewrite_step.clause.literals {
            for atom in lit.iter_atoms() {
                if let Atom::FreeVariable(var_id) = atom {
                    let var_type = clause_context.get_var_type(*var_id as usize);
                    assert!(
                        var_type.is_some(),
                        "Variable x{} in clause has no type in context (context len: {}). \
                         This indicates that from_literal_traced was called with the wrong context.",
                        var_id,
                        clause_context.len()
                    );
                }
            }
        }
    }
}
