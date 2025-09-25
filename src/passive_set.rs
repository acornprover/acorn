use crate::clause::{Clause, ClauseTrace, LiteralTrace};
use crate::features::Features;
use crate::fingerprint::FingerprintSpecializer;
use crate::literal::Literal;
use crate::proof_step::ProofStep;
use crate::score::Score;
use crate::scorer::{default_scorer, Scorer};
use crate::term::Term;
use crate::variable_map::VariableMap;
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
fn pair_specializes(left1: &Term, right1: &Term, left2: &Term, right2: &Term) -> bool {
    if left1.term_type != left2.term_type {
        return false;
    }
    let mut var_map = VariableMap::new();
    var_map.match_terms(left1, left2) && var_map.match_terms(right1, right2)
}

// Makes a new clause by simplifying a bunch of literals with respect to a given literal.
// left and right do not have to have variables normalized.
// We only check against the left->right direction.
// We already know literals[index] can be obtained from the given literal through variable substitution.
// Returns None if the clause is tautologically implied by the literal we are simplifying with.
fn make_simplified(
    activated_id: usize,
    left: &Term,
    right: &Term,
    positive: bool,
    flipped: bool,
    index: usize,
    literals: Vec<Literal>,
    traces: Option<ClauseTrace>,
) -> Option<(Clause, Option<ClauseTrace>)> {
    if literals[index].positive == positive {
        return None;
    }
    let mut new_literals = vec![];
    let mut incremental_trace = vec![];
    for (i, literal) in literals.into_iter().enumerate() {
        let (eliminated, literal_flipped) = if i == index {
            (true, flipped)
        } else if pair_specializes(left, right, &literal.left, &literal.right) {
            if literal.positive == positive {
                // The whole clause is implied by the literal we are simplifying with.
                return None;
            }
            // This specific literal is unsatisfiable.
            (true, false)
        } else if pair_specializes(left, right, &literal.right, &literal.left) {
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
            incremental_trace.push(LiteralTrace::Eliminated {
                step: activated_id,
                flipped: literal_flipped,
            });
        } else {
            let index = new_literals.len();
            incremental_trace.push(LiteralTrace::Output {
                index,
                flipped: false,
            });
            new_literals.push(literal);
        }
    }
    Some(Clause::new_composing_traces(
        new_literals,
        traces,
        &ClauseTrace::new(incremental_trace),
    ))
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
    pub fn push_batch(&mut self, steps: Vec<ProofStep>) {
        if steps.is_empty() {
            return;
        }
        let features = steps.iter().map(Features::new).collect::<Vec<_>>();
        let scores = Score::batch(self.scorer.as_ref(), &features);
        for (step, score) in steps.into_iter().zip(scores.into_iter()) {
            self.push_with_score(step, score);
        }
    }

    // Adding a new step when we have already scored it.
    fn push_with_score(&mut self, step: ProofStep, score: Score) {
        let id = self.clauses.len();

        for (i, literal) in step.clause.literals.iter().enumerate() {
            self.literals.insert(literal, (id, i));
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
                        // We have a contradiction.
                        self.contradiction = Some((*existing_id, id));
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
        left: &Term,
        right: &Term,
        positive: bool,
        flipped: bool,
    ) {
        let mut new_steps = vec![];
        for &(clause_id, literal_index) in self.literals.find_specializing(left, right) {
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

            // We've only checked fingerprints. We need to check if they actually match.
            if !pair_specializes(left, right, &literal.left, &literal.right) {
                continue;
            }

            if step.rule.is_assumption() && positive == literal_positive {
                // This assumption is redundant, implied by an existing clause.
                // But, let's keep it, because we might use it for rewrite inspiration.
                continue;
            }

            // It matches. So we're definitely removing the existing clause.
            let (mut step, score) = self.clauses[clause_id].take().unwrap();
            self.queue.remove(&(score, clause_id));

            if positive == literal_positive {
                // The whole passive clause is implied by the activated clause.
                // So it's just redundant. We can forget about it.
                continue;
            }
            let Some((new_clause, traces)) = make_simplified(
                activated_id,
                left,
                right,
                positive,
                flipped,
                literal_index,
                std::mem::take(&mut step.clause.literals),
                std::mem::take(&mut step.traces),
            ) else {
                continue;
            };
            let short_steps = &[(activated_id, activated_step)];
            new_steps.push(ProofStep::simplified(step, short_steps, new_clause, traces));
        }

        self.push_batch(new_steps);
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
    pub fn simplify(&mut self, activated_id: usize, step: &ProofStep) {
        assert!(step.clause.literals.len() == 1);
        let literal = &step.clause.literals[0];
        self.simplify_one_direction(
            activated_id,
            &step,
            &literal.left,
            &literal.right,
            literal.positive,
            false,
        );
        if !literal.strict_kbo() {
            let (right, left) = literal.normalized_reversed();
            self.simplify_one_direction(activated_id, &step, &right, &left, literal.positive, true);
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
        let mut passive_set = PassiveSet::new();
        passive_set.push_batch(vec![ProofStep::mock("c0(c1) or c0(c2)")]);
        // This should match *both* the literals in our existing clause
        passive_set.simplify(3, &ProofStep::mock("not c0(x0)"));
        let step = passive_set.pop().unwrap();
        assert_eq!(step.clause.to_string(), "<empty>");
    }
}
