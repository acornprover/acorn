use ordered_float::OrderedFloat;
use std::cmp::Ordering;

use super::features::Features;
use super::scorer::{Scorer, ScoringPolicy};
use crate::kernel::proof_step::ShallowStatus;

// Each proof step has a score, which encapsulates all heuristic judgments about
// the proof step.
// The better the score, the more we want to activate this proof step.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct ScoreKey {
    contradiction: bool,
    shallow_status: ShallowStatus,
    score: OrderedFloat<f32>,
}

#[derive(Debug, Clone, Copy)]
pub struct Score {
    key: ScoreKey,
    is_shallow: bool,
}

impl Score {
    fn shallow_order(policy: ScoringPolicy, features: &Features) -> ShallowStatus {
        if policy.uses_shallow_ordering() {
            features.shallow_status
        } else {
            ShallowStatus::Unspent
        }
    }

    pub fn new(policy: ScoringPolicy, scorer: &dyn Scorer, features: &Features) -> Score {
        if features.is_contradiction {
            return Score {
                key: ScoreKey {
                    contradiction: true,
                    shallow_status: Self::shallow_order(policy, features),
                    score: OrderedFloat(0.0),
                },
                is_shallow: features.is_shallow,
            };
        }
        let score = scorer.score(features).unwrap();
        Score {
            key: ScoreKey {
                contradiction: false,
                shallow_status: Self::shallow_order(policy, features),
                score: OrderedFloat(score),
            },
            is_shallow: features.is_shallow,
        }
    }

    // Do a whole batch of scoring at once.
    pub fn batch(policy: ScoringPolicy, scorer: &dyn Scorer, features: &[Features]) -> Vec<Score> {
        let floats = scorer.score_batch(features).unwrap();
        features
            .iter()
            .zip(floats.iter())
            .map(|(f, &s)| Score {
                key: ScoreKey {
                    contradiction: f.is_contradiction,
                    shallow_status: Self::shallow_order(policy, f),
                    score: OrderedFloat(s),
                },
                is_shallow: f.is_shallow,
            })
            .collect()
    }

    pub fn is_shallow(&self) -> bool {
        self.is_shallow
    }

    pub fn raw_score(&self) -> f32 {
        self.key.score.0
    }

    pub fn prioritizes_contradiction(&self) -> bool {
        self.key.contradiction
    }

    pub fn ordered_shallow_status(&self) -> ShallowStatus {
        self.key.shallow_status
    }
}

impl PartialEq for Score {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for Score {}

impl PartialOrd for Score {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Score {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ConstantScorer;

    impl Scorer for ConstantScorer {
        fn score(&self, _features: &Features) -> Result<f32, Box<dyn std::error::Error>> {
            Ok(1.0)
        }
    }

    fn features(shallow_status: ShallowStatus) -> Features {
        Features {
            is_contradiction: false,
            is_shallow: shallow_status.is_shallow(),
            shallow_status,
            atom_count: 1,
            is_counterfactual: false,
            is_hypothetical: false,
            is_factual: true,
            is_assumption: true,
            is_negated_goal: false,
            proof_size: 1,
            depth: 0,
            ..Features::default()
        }
    }

    #[test]
    fn shallow_status_orders_scores_by_default() {
        let scorer = ConstantScorer;
        let deep = Score::new(
            ScoringPolicy::Legacy,
            &scorer,
            &features(ShallowStatus::Deep),
        );
        let shallow = Score::new(
            ScoringPolicy::Legacy,
            &scorer,
            &features(ShallowStatus::Unspent),
        );

        assert!(shallow > deep);
        assert!(!deep.is_shallow());
        assert!(shallow.is_shallow());
    }

    #[test]
    fn legacy_no_shallow_keeps_shallow_status_out_of_ordering() {
        let scorer = ConstantScorer;
        let deep = Score::new(
            ScoringPolicy::LegacyNoShallow,
            &scorer,
            &features(ShallowStatus::Deep),
        );
        let shallow = Score::new(
            ScoringPolicy::LegacyNoShallow,
            &scorer,
            &features(ShallowStatus::Unspent),
        );

        assert_eq!(deep.cmp(&shallow), Ordering::Equal);
        assert!(!deep.is_shallow());
        assert!(shallow.is_shallow());
    }
}
