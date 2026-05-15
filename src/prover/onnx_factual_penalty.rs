use std::error::Error;

use super::features::Features;
use super::scorer::Scorer;
use super::scoring_model::ScoringModel;

// Wraps the ONNX scorer with a fixed penalty for factual-assumption steps,
// motivated by the May 2026 eval observation that factual activations dominate
// runtime cost roughly 117 to 1 over non-factual activations.
pub struct OnnxFactualPenalty {
    onnx: ScoringModel,
    penalty: f32,
}

impl OnnxFactualPenalty {
    pub fn new() -> Result<Self, Box<dyn Error>> {
        Ok(Self {
            onnx: ScoringModel::load()?,
            penalty: 1.0,
        })
    }
}

impl Scorer for OnnxFactualPenalty {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        let mut score = self.onnx.score(features)?;
        if features.is_factual && features.is_assumption {
            score -= self.penalty;
        }
        Ok(score)
    }

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        let mut scores = self.onnx.score_batch(features)?;
        for (i, f) in features.iter().enumerate() {
            if f.is_factual && f.is_assumption {
                scores[i] -= self.penalty;
            }
        }
        Ok(scores)
    }
}
