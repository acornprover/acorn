use super::active_set::ActiveSet;
use super::features::Features;
use super::score::Score;
use super::scorer::{default_scorer, Scorer};
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::fingerprint::FingerprintSpecializer;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{PremiseMap, ProofStep, Rule, SimplificationInfo};
use crate::kernel::term::Term;
use crate::kernel::variable_map::VariableMap;
use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

// The PassiveSet stores a bunch of clauses.
// A clause in the passive set can be activated, and it can be simplified, but to do
// anything more complicated it needs to be activated first.
#[derive(Clone)]
pub struct PassiveSet {
    // Stores clauses in the passive set, along with their score.
    // We never shrink this vector, we just replace its entries with None.
    // The index into clauses acts like an id, but that id doesn't mean anything outside of the
    // PassiveSet.
    clauses: Vec<Option<(ProofStep, Score)>>,

    // Stores (score, clause id).
    // The queue lets us pick the highest-scoring clause to activate next.
    queue: BTreeSet<(Score, usize)>,

    // Stores (clause id, literal index) for each literal in each passive clause.
    // We currently don't clean this up by removing old clause ids, so when we retrieve from
    // it we need to check that the clause is still in the passive set.
    literals: FingerprintSpecializer<(usize, usize)>,

    // Stores every clause in clauses that is just a single literal, along with its index.
    // The format is
    // (left, right) -> (positive, index into clauses)
    singles: HashMap<(Term, Term), (bool, usize)>,

    // Set if we ever discover a contradiction between two members of the passive set.
    contradiction: Option<(usize, usize)>,

    // Whether every step we have activated is shallow.
    // This flag starts as true and flips to false once we activate a non-shallow step.
    pub all_shallow: bool,

    // We do reference counting so that we don't have to clone the scorer when we clone the prover.
    // For now this doesn't really matter, but maybe in the future the scorer will have a large model,
    // some affiliated GPU state, something like that.
    scorer: Arc<dyn Scorer + Send + Sync>,
}

// Whether (left1, right1) can be mapped to (left2, right2) through variable substitution.
// Only tries this direction.
// Terms do not have to have variables normalized.
// general_context is for left1/right1, special_context is for left2/right2.
fn pair_specializes(
    general_context: &LocalContext,
    special_context: &LocalContext,
    kernel_context: &KernelContext,
    left1: &Term,
    right1: &Term,
    left2: &Term,
    right2: &Term,
) -> bool {
    // Note: type checking is done inside match_terms when matching variables,
    // so we don't need a separate top-level type check here.
    let mut var_map = VariableMap::new();
    var_map.match_terms(
        left1.as_ref(),
        left2.as_ref(),
        general_context,
        special_context,
        kernel_context,
    ) && var_map.match_terms(
        right1.as_ref(),
        right2.as_ref(),
        general_context,
        special_context,
        kernel_context,
    )
}

// Makes a new clause by simplifying a bunch of literals with respect to a given literal.
// left and right do not have to have variables normalized.
// We only check against the left->right direction.
// We already know literals[index] can be obtained from the given literal through variable substitution.
// Returns None if the clause is tautologically implied by the literal we are simplifying with.
// activated_context is for left/right, passive_context is for literals.
fn make_simplified(
    activated_context: &LocalContext,
    activated_literal: &Literal,
    passive_context: &LocalContext,
    kernel_context: &KernelContext,
    left: &Term,
    right: &Term,
    positive: bool,
    caller_flipped: bool,
    literals: Vec<Literal>,
) -> Option<(Clause, Vec<AtomId>, Vec<VariableMap>)> {
    // Note: When caller_flipped is true, left and right have already been swapped
    // by the caller. So any flip we compute here is relative to the swapped order.
    // The final flip must be XORed with caller_flipped to get the flip relative
    // to the original activating literal orientation.
    let mut new_literals = vec![];
    let mut simp_var_maps = vec![];
    for literal in literals.into_iter() {
        // Check both directions consistently for all literals.
        // The flip value must be determined by which direction actually matches,
        // not by which direction was used to find the initial match.
        let (eliminated, match_flipped) = if pair_specializes(
            activated_context,
            passive_context,
            kernel_context,
            left,
            right,
            &literal.left,
            &literal.right,
        ) {
            if literal.positive == positive {
                // The whole clause is implied by the literal we are simplifying with.
                return None;
            }
            // This specific literal is unsatisfiable.
            (true, false)
        } else if pair_specializes(
            activated_context,
            passive_context,
            kernel_context,
            left,
            right,
            &literal.right,
            &literal.left,
        ) {
            if literal.positive == positive {
                // The whole clause is implied by the literal we are simplifying with.
                return None;
            }
            // This specific literal is unsatisfiable with flipped matching.
            (true, true)
        } else {
            (false, false)
        };
        if eliminated {
            // XOR with caller_flipped to get the flip relative to original orientation
            let literal_flipped = match_flipped != caller_flipped;
            // Extract var_map for the simplifying clause
            let mut var_map = VariableMap::new();
            var_map.match_literal(activated_literal, &literal, literal_flipped);
            simp_var_maps.push(var_map);
        } else {
            new_literals.push(literal);
        }
    }
    let (clause, var_ids) = Clause::normalize_with_var_ids(new_literals, passive_context);
    Some((clause, var_ids, simp_var_maps))
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: vec![],
            queue: BTreeSet::new(),
            literals: FingerprintSpecializer::new(),
            singles: HashMap::new(),
            contradiction: None,
            all_shallow: true,
            scorer: default_scorer().into(),
        }
    }

    // Adding many new steps at once.
    pub fn push_batch(&mut self, steps: Vec<ProofStep>, kernel_context: &KernelContext) {
        if steps.is_empty() {
            return;
        }
        let features = steps.iter().map(Features::new).collect::<Vec<_>>();
        let scores = Score::batch(self.scorer.as_ref(), &features);
        for (step, score) in steps.into_iter().zip(scores.into_iter()) {
            self.push_with_score(step, score, kernel_context);
        }
    }

    // Adding a new step when we have already scored it.
    fn push_with_score(&mut self, step: ProofStep, score: Score, kernel_context: &KernelContext) {
        let id = self.clauses.len();
        let local_context = step.clause.get_local_context();

        for (i, literal) in step.clause.literals.iter().enumerate() {
            self.literals
                .insert(literal, (id, i), local_context, kernel_context);
        }
        if step.clause.literals.len() == 1 {
            let literal = &step.clause.literals[0];
            match self
                .singles
                .entry((literal.left.clone(), literal.right.clone()))
            {
                Entry::Occupied(e) => {
                    let (existing_positive, existing_id) = e.get();
                    if *existing_positive != literal.positive {
                        // Potential contradiction - but only valid if all types are inhabited.
                        // If any type might be empty, both foralls could be vacuously true.
                        let new_context = step.clause.get_local_context();
                        let existing_context = self.clauses[*existing_id]
                            .as_ref()
                            .map(|(s, _)| s.clause.get_local_context());

                        let all_inhabited = if let Some(existing_ctx) = existing_context {
                            // Check all types in both contexts are provably inhabited
                            let new_inhabited = (0..new_context.len()).all(|i| {
                                new_context.get_var_type(i).is_none_or(|t| {
                                    kernel_context.provably_inhabited(t, Some(new_context))
                                })
                            });
                            let existing_inhabited = (0..existing_ctx.len()).all(|i| {
                                existing_ctx.get_var_type(i).is_none_or(|t| {
                                    kernel_context.provably_inhabited(t, Some(existing_ctx))
                                })
                            });
                            new_inhabited && existing_inhabited
                        } else {
                            false
                        };

                        if all_inhabited {
                            self.contradiction = Some((*existing_id, id));
                        }
                    }
                }
                Entry::Vacant(entry) => {
                    entry.insert((literal.positive, id));
                }
            }
        }
        self.clauses.push(Some((step, score)));
        self.queue.insert((score, id));
    }

    // Whether we can pop another proof step from the passive set and still use a resulting
    // proof for verification.
    pub fn can_pop_for_verification(&self) -> bool {
        if !self.all_shallow {
            return false;
        }
        if let Some((score, _)) = self.queue.iter().next_back() {
            score.is_shallow()
        } else {
            false
        }
    }

    pub fn pop(&mut self) -> Option<ProofStep> {
        // Remove the largest entry from queue
        let (score, id) = self.queue.pop_last()?;
        if !score.is_shallow() {
            self.all_shallow = false;
        }
        match self.clauses[id].take() {
            Some((step, _)) => Some(step),
            None => panic!("Queue and clauses are out of sync"),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    // Simplifies any literals in the passive set that can be eliminated by this activated literal.
    // Checks just the left->right direction for simplification.
    fn simplify_one_direction(
        &mut self,
        activated_id: usize,
        activated_step: &ProofStep,
        local_context: &LocalContext,
        #[cfg_attr(not(any(test, feature = "validate")), allow(unused_variables))]
        active_set: &ActiveSet,
        kernel_context: &KernelContext,
        left: &Term,
        right: &Term,
        positive: bool,
        flipped: bool,
    ) {
        let mut new_steps = vec![];
        for &(clause_id, literal_index) in
            self.literals
                .find_specializing(left, right, local_context, kernel_context)
        {
            let step = match &self.clauses[clause_id] {
                Some((step, _)) => step,
                None => {
                    // The clause was already removed, so this is a dead reference.
                    // Maybe we could more actively clean these up.
                    continue;
                }
            };

            let literal = &step.clause.literals[literal_index];
            let literal_positive = literal.positive;
            let passive_context = step.clause.get_local_context();

            // We've only checked fingerprints. We need to check if they actually match.
            if !pair_specializes(
                local_context,
                passive_context,
                kernel_context,
                left,
                right,
                &literal.left,
                &literal.right,
            ) {
                continue;
            }

            if step.rule.is_assumption() && positive == literal_positive {
                // This assumption is redundant, implied by an existing clause.
                // But, let's keep it, because we might use it for rewrite inspiration.
                continue;
            }

            // It matches. So we're definitely removing the existing clause.
            let passive_context = step.clause.get_local_context().clone();
            let (step, score) = self.clauses[clause_id].take().unwrap();
            self.queue.remove(&(score, clause_id));

            if positive == literal_positive {
                // The whole passive clause is implied by the activated clause.
                // So it's just redundant. We can forget about it.
                continue;
            }
            let activated_literal = &activated_step.clause.literals[0];
            let Some((new_clause, var_ids, simp_var_maps)) = make_simplified(
                local_context,
                activated_literal,
                &passive_context,
                kernel_context,
                left,
                right,
                positive,
                flipped,
                step.clause.literals.clone(),
            ) else {
                continue;
            };

            // If simplification produced an impossible (empty) clause, we need to verify
            // that all variable types are provably inhabited before accepting it as a
            // real contradiction. When types might be empty, both forall clauses could
            // be vacuously true with no actual contradiction.
            if new_clause.is_impossible() {
                let activated_inhabited = (0..local_context.len()).all(|i| {
                    local_context
                        .get_var_type(i)
                        .is_none_or(|t| kernel_context.provably_inhabited(t, Some(&local_context)))
                });
                let passive_inhabited = (0..passive_context.len()).all(|i| {
                    passive_context.get_var_type(i).is_none_or(|t| {
                        kernel_context.provably_inhabited(t, Some(&passive_context))
                    })
                });
                if !activated_inhabited || !passive_inhabited {
                    // Type might be empty, so this isn't a real contradiction.
                    continue;
                }
            }

            let truthiness = step.truthiness.combine(activated_step.truthiness);
            let proof_size = step.proof_size + activated_step.proof_size;
            let depth = u32::max(step.depth, activated_step.depth);

            let pre_norm_context = step.clause.get_local_context().clone();
            // simplifying_ids needs one entry per eliminated literal (same as simp_var_maps)
            let simplifying_ids = vec![activated_id; simp_var_maps.len()];
            let premise_map = PremiseMap::new(simp_var_maps, var_ids, pre_norm_context);
            let simplified = ProofStep {
                clause: new_clause,
                truthiness,
                rule: Rule::Simplification(SimplificationInfo {
                    original: Box::new(step),
                    simplifying_ids,
                }),
                proof_size,
                depth,
                premise_map,
            };

            // Validate the simplified step when the validate feature is enabled
            #[cfg(any(test, feature = "validate"))]
            if let Err(e) = active_set.validate_step_with_pending(
                &simplified,
                kernel_context,
                activated_id,
                &activated_step.clause,
            ) {
                panic!(
                    "Invalid proof step after passive simplification: {}\nStep clause: {}\nStep rule: {}",
                    e,
                    simplified.clause,
                    simplified.rule.name()
                );
            }

            new_steps.push(simplified);
        }

        self.push_batch(new_steps, kernel_context);
    }

    // If we don't have both of the clauses, we just return the ones we have.
    // This is wrong but I'm not sure if we'll ever run into it.
    pub fn get_contradiction(&self) -> Option<Vec<ProofStep>> {
        match self.contradiction {
            None => None,
            Some((id1, id2)) => {
                let mut steps = vec![];
                for id in &[id1, id2] {
                    if let Some((step, _)) = &self.clauses[*id] {
                        steps.push(step.clone());
                    }
                }
                Some(steps)
            }
        }
    }

    // Called when we activate a new true literal.
    // Simplifies the passive set by removing literals that are now known to be true.
    // Checks both directions.
    pub fn simplify(
        &mut self,
        activated_id: usize,
        step: &ProofStep,
        active_set: &ActiveSet,
        kernel_context: &KernelContext,
    ) {
        assert!(step.clause.literals.len() == 1);
        let local_context = step.clause.get_local_context();
        let literal = &step.clause.literals[0];
        self.simplify_one_direction(
            activated_id,
            &step,
            local_context,
            active_set,
            kernel_context,
            &literal.left,
            &literal.right,
            literal.positive,
            false,
        );
        if !literal.strict_kbo() {
            let (right, left, reversed_context) = literal.normalized_reversed(local_context);
            self.simplify_one_direction(
                activated_id,
                &step,
                &reversed_context,
                active_set,
                kernel_context,
                &right,
                &left,
                literal.positive,
                true,
            );
        }
    }

    // The number of clauses remaining in the passive set.
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    // Iterates over the steps from highest-scoring to lowest-scoring.
    pub fn iter_steps(&self) -> impl Iterator<Item = &ProofStep> {
        self.queue
            .iter()
            .rev()
            .map(|(_, id)| match &self.clauses[*id] {
                Some((step, _)) => step,
                None => panic!("Queue and clauses are out of sync"),
            })
    }

    // Finds the proof steps that are consequences of the given clause.
    // Sorts from best to worst, which is highest to lowest for ProofSteps.
    pub fn find_consequences<'a>(&'a self, id: usize) -> Vec<&'a ProofStep> {
        self.iter_steps()
            .filter(|step| step.depends_on_active(id))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_passive_set_simplification() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c0", "c1", "c2"], "Bool");

        let mut passive_set = PassiveSet::new();
        let clause1 = kctx.parse_clause("g0(c0, c1) or g0(c0, c2)", &[]);
        passive_set.push_batch(vec![ProofStep::mock_from_clause(clause1)], &kctx);

        // This should match *both* the literals in our existing clause.
        // x0 is a Bool variable that matches both c1 and c2.
        let clause2 = kctx.parse_clause("not g0(c0, x0)", &["Bool"]);
        let active_set = ActiveSet::new();
        passive_set.simplify(3, &ProofStep::mock_from_clause(clause2), &active_set, &kctx);

        let step = passive_set.pop().unwrap();
        assert_eq!(step.clause.to_string(), "<empty>");
    }
}
