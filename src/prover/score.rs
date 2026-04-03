use ordered_float::OrderedFloat;

use super::features::Features;
use super::scorer::Scorer;
use crate::kernel::proof_step::ShallowStatus;

// Each proof step has a score, which encapsulates all heuristic judgments about
// the proof step.
// The better the score, the more we want to activate this proof step.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Score {
    // Contradictions are the most important thing
    contradiction: bool,

    // Among non-contradictions, activate the shallowest steps first.
    shallow_status: ShallowStatus,

    // Higher scores are preferred.
    score: OrderedFloat<f32>,
}

impl Score {
    // The logic here is logic that we want to use regardless of the policy.
    pub fn new(scorer: &dyn Scorer, features: &Features) -> Score {
        if features.is_contradiction {
            return Score {
                contradiction: true,
                shallow_status: features.shallow_status,
                score: OrderedFloat(0.0),
            };
        }
        let score = scorer.score(features).unwrap();
        Score {
            contradiction: false,
            shallow_status: features.shallow_status,
            score: OrderedFloat(score),
        }
    }

    // Do a whole batch of scoring at once.
    pub fn batch(scorer: &dyn Scorer, features: &[Features]) -> Vec<Score> {
        let floats = scorer.score_batch(features).unwrap();
        features
            .iter()
            .zip(floats.iter())
            .map(|(f, &s)| Score {
                contradiction: f.is_contradiction,
                shallow_status: f.shallow_status,
                score: OrderedFloat(s),
            })
            .collect()
    }

    pub fn is_shallow(&self) -> bool {
        self.shallow_status.is_shallow()
    }
}
