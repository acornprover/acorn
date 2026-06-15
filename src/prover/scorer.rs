use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use super::features::Features;
use super::scoring_model::{ScoringModel, EMBEDDED_MODEL_POLICY};

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
    Model20260611E50H512L3,
    Handcrafted,
    DepthFirst,
    Model,
    ModelNoShallow,
}

impl Default for ScoringPolicy {
    fn default() -> Self {
        Self::Model20260611E50H512L3
    }
}

impl ScoringPolicy {
    pub fn make_scorer(self) -> Box<dyn Scorer + Send + Sync> {
        ScoringConfig::new(self).make_scorer()
    }

    pub fn uses_shallow_ordering(self) -> bool {
        !matches!(self, Self::ModelNoShallow)
    }

    pub fn requires_model(self) -> bool {
        matches!(self, Self::Model | Self::ModelNoShallow)
    }

    pub fn options() -> &'static str {
        "model-20260611-e50-h512-l3, handcrafted, depth-first, model, model-no-shallow"
    }
}

impl fmt::Display for ScoringPolicy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Model20260611E50H512L3 => EMBEDDED_MODEL_POLICY,
            Self::Handcrafted => "handcrafted",
            Self::DepthFirst => "depth-first",
            Self::Model => "model",
            Self::ModelNoShallow => "model-no-shallow",
        };
        f.write_str(name)
    }
}

impl FromStr for ScoringPolicy {
    type Err = String;

    fn from_str(raw: &str) -> Result<Self, Self::Err> {
        match raw {
            "model-20260611-e50-h512-l3" => Ok(Self::Model20260611E50H512L3),
            "handcrafted" => Ok(Self::Handcrafted),
            "depth-first" => Ok(Self::DepthFirst),
            "model" => Ok(Self::Model),
            "model-no-shallow" => Ok(Self::ModelNoShallow),
            _ => Err(format!(
                "unknown policy '{}'. Expected one of: {}",
                raw,
                Self::options()
            )),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScoringConfig {
    policy: ScoringPolicy,
    model_path: Option<PathBuf>,
    trace_label: Option<String>,
}

impl Default for ScoringConfig {
    fn default() -> Self {
        Self::new(ScoringPolicy::default())
    }
}

impl ScoringConfig {
    pub fn new(policy: ScoringPolicy) -> Self {
        Self {
            policy,
            model_path: None,
            trace_label: None,
        }
    }

    pub fn with_model_path(mut self, model_path: PathBuf) -> Self {
        self.model_path = Some(model_path);
        self
    }

    pub fn with_trace_label(mut self, trace_label: String) -> Self {
        self.trace_label = Some(trace_label);
        self
    }

    pub fn policy(&self) -> ScoringPolicy {
        self.policy
    }

    pub fn trace_label(&self) -> String {
        self.trace_label
            .clone()
            .unwrap_or_else(|| self.policy.to_string())
    }

    pub fn load_scorer(&self) -> Result<Box<dyn Scorer + Send + Sync>, Box<dyn Error>> {
        match self.policy {
            ScoringPolicy::Model20260611E50H512L3 => {
                Ok(Box::new(ScoringModel::load().map_err(|e| {
                    format!("failed to load embedded model: {}", e)
                })?))
            }
            ScoringPolicy::Model | ScoringPolicy::ModelNoShallow => {
                let path = self
                    .model_path
                    .as_deref()
                    .ok_or_else(|| format!("policy '{}' requires --model PATH", self.policy))?;
                Ok(Box::new(ScoringModel::load_from_path(path).map_err(
                    |e| format!("failed to load scoring model {}: {}", path.display(), e),
                )?))
            }
            ScoringPolicy::Handcrafted => Ok(Box::new(HandcraftedScorer)),
            ScoringPolicy::DepthFirst => Ok(Box::new(DepthFirstScorer)),
        }
    }

    pub fn make_scorer(&self) -> Box<dyn Scorer + Send + Sync> {
        self.load_scorer().unwrap_or_else(|e| {
            panic!(
                "failed to initialize scoring config '{}': {}",
                self.trace_label(),
                e
            )
        })
    }

    pub fn validate(&self) -> Result<(), Box<dyn Error>> {
        self.load_scorer().map(|_| ())
    }

    pub fn model_path(&self) -> Option<&Path> {
        self.model_path.as_deref()
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
