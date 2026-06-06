use std::error::Error;
use std::fmt;
use std::str::FromStr;

use super::features::Features;
use super::scoring_model::ScoringModel;

pub trait Scorer {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>>;

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        Ok(features.iter().map(|f| self.score(f).unwrap()).collect())
    }
}

pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    Box::new(ScoringModel::load().unwrap())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScoringPolicy {
    Onnx,
    Handcrafted,
    DepthFirst,
    OnnxNoShallow,
}

impl Default for ScoringPolicy {
    fn default() -> Self {
        Self::Onnx
    }
}

impl ScoringPolicy {
    pub fn make_scorer(self) -> Box<dyn Scorer + Send + Sync> {
        match self {
            Self::Onnx | Self::OnnxNoShallow => Box::new(ScoringModel::load().unwrap()),
            Self::Handcrafted => Box::new(HandcraftedScorer),
            Self::DepthFirst => Box::new(DepthFirstScorer),
        }
    }

    pub fn uses_shallow_ordering(self) -> bool {
        !matches!(self, Self::OnnxNoShallow)
    }

    pub fn options() -> &'static str {
        "onnx, handcrafted, depth-first, onnx-no-shallow"
    }
}

impl fmt::Display for ScoringPolicy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Onnx => "onnx",
            Self::Handcrafted => "handcrafted",
            Self::DepthFirst => "depth-first",
            Self::OnnxNoShallow => "onnx-no-shallow",
        };
        f.write_str(name)
    }
}

impl FromStr for ScoringPolicy {
    type Err = String;

    fn from_str(raw: &str) -> Result<Self, Self::Err> {
        match raw {
            "onnx" => Ok(Self::Onnx),
            "handcrafted" => Ok(Self::Handcrafted),
            "depth-first" => Ok(Self::DepthFirst),
            "onnx-no-shallow" => Ok(Self::OnnxNoShallow),
            _ => Err(format!(
                "unknown policy '{}'. Expected one of: {}",
                raw,
                Self::options()
            )),
        }
    }
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
