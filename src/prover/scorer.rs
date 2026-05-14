use std::error::Error;

use super::features::Features;
use super::scoring_model::ScoringModel;

pub trait Scorer {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>>;

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        Ok(features.iter().map(|f| self.score(f).unwrap()).collect())
    }
}

pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    Box::new(ScoringModel::load().expect(
        "ONNX scorer failed to load. \
         Call init_default_scorer() at startup to surface this error cleanly.",
    ))
}

/// Eagerly loads the default scorer so a misconfigured ONNX runtime surfaces
/// here, at one well-known site, instead of as a panic inside the first prover
/// construction. Intended to be called once from binary entry points.
pub fn init_default_scorer() -> Result<(), Box<dyn Error>> {
    ScoringModel::load().map(drop)
}

// Developed before I had any other framework for policies.
pub struct HandcraftedScorer;

impl Scorer for HandcraftedScorer {
    // The first heuristic is like negative depth.
    // It's bounded at -2 so after that we don't use depth for scoring any more.
    //
    // The second heuristic is an ordering by the type
    //
    //   Global facts, both explicit and deductions
    //   The negated goal
    //   Explicit hypotheses
    //   Local deductions
    //
    // The third heuristic is a combination of a bunch of stuff, roughly to discourage
    // complexity.
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        // The first heuristic is 0 for zero depth, -1 for depth 1, -2 for anything deeper.
        let heuristic1 = match features.depth {
            0 => 0,
            1 => -1,
            _ => -2,
        };

        // The second heuristic is based on truthiness.
        // Higher = more important.
        let heuristic2 = if features.is_counterfactual {
            if features.is_negated_goal {
                3
            } else {
                1
            }
        } else if features.is_hypothetical {
            if features.is_assumption {
                2
            } else {
                1
            }
        } else {
            4
        };

        // The third heuristic is a hodgepodge.
        let mut heuristic3 = 0;
        heuristic3 -= features.atom_count;
        heuristic3 -= 2 * features.proof_size;
        if features.is_hypothetical {
            heuristic3 -= 3;
        }

        // Essentially lexicographical
        let score =
            1000000.0 * (heuristic1 as f32) + 100000.0 * (heuristic2 as f32) + heuristic3 as f32;
        Ok(score)
    }
}

pub struct DepthFirstScorer;

impl Scorer for DepthFirstScorer {
    // Always scoring zero will make it do depth-first search.
    fn score(&self, _features: &Features) -> Result<f32, Box<dyn Error>> {
        Ok(0.0)
    }
}
