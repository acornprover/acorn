use std::error::Error;
use std::sync::{Arc, OnceLock};

use ndarray::{Axis, IxDyn};
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;

use super::features::Features;
use super::scorer::Scorer;
use crate::ort_utils::ensure_ort_initialized;

// The ScoringModel uses ort to load an onnx model and uses it to score feature vectors.
pub struct ScoringModel {
    // The ONNX model.
    session: Arc<Session>,
}

static SCORING_SESSION: OnceLock<Arc<Session>> = OnceLock::new();

const MODEL_BYTES: &[u8] = include_bytes!("../../files/models/model-2024-09-25-15-33-10.onnx");

fn make_session(bytes: &[u8]) -> Result<Arc<Session>, Box<dyn Error>> {
    ensure_ort_initialized()?;

    let session = Session::builder()?
        .with_intra_threads(1)?
        .with_inter_threads(1)?
        .with_optimization_level(GraphOptimizationLevel::Level3)?
        .commit_from_memory(bytes)?;
    Ok(Arc::new(session))
}

impl ScoringModel {
    // Loads a model from bytes.
    // The bytes are typically preloaded into the binary with include_bytes!.
    fn load_bytes(bytes: &[u8]) -> Result<Self, Box<dyn Error>> {
        let session = SCORING_SESSION
            .get_or_init(|| make_session(bytes).expect("Failed to initialize ORT session"));
        Ok(ScoringModel {
            session: Arc::clone(session),
        })
    }

    // Loads the hardcoded model.
    pub fn load() -> Result<Self, Box<dyn Error>> {
        ScoringModel::load_bytes(MODEL_BYTES)
    }
}

impl Scorer for ScoringModel {
    // This assumes that the model is calculating a probability of the positive class,
    // where the positive class is a step that was actually taken in a proof.
    // There's a lot of unwrapping - it would be nice to handle errors more gracefully.
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        let array = features.to_array().insert_axis(Axis(0));
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let ix = IxDyn(&[0, 0]);
        if let Some(score) = extracted.get(ix) {
            Ok(*score)
        } else {
            Err("No score at [0, 0]. Maybe the model is the wrong shape?".into())
        }
    }

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        let array = Features::to_array2(features);
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let scores: Vec<f32> = extracted.iter().copied().collect();
        Ok(scores)
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::proof_step::ProofStep;

    use super::*;

    #[test]
    fn test_ort_model_score() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constants(&["c2", "c3"], "Bool");
        let clause = kctx.parse_clause("g0(c3) = c2", &[]);
        let step = ProofStep::mock_from_clause(clause);
        let features = Features::new(&step);

        let scoring_model = ScoringModel::load().unwrap();
        let ort_score = scoring_model.score(&features).unwrap();
        assert!(ort_score.is_finite());
    }

    #[test]
    fn test_ort_model_batch_score() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c1", "c2"], "Bool");

        let clause1 = kctx.parse_clause("g0(c1, c1) = c2", &[]);
        let clause2 = kctx.parse_clause("g0(c1, c1) = g0(c2, c2)", &[]);
        let step1 = ProofStep::mock_from_clause(clause1);
        let step2 = ProofStep::mock_from_clause(clause2);
        let features1 = Features::new(&step1);
        let features2 = Features::new(&step2);
        let scoring_model = ScoringModel::load().unwrap();

        let score1 = scoring_model.score(&features1).unwrap();
        let score2 = scoring_model.score(&features2).unwrap();

        // The scores should be different, even up to floating point error
        assert!((score1 - score2).abs() > 1e-6);

        // Recalculate the scores in a batch
        let scores = scoring_model.score_batch(&[features1, features2]).unwrap();
        assert_eq!(scores.len(), 2);
        assert!((scores[0] - score1).abs() < 1e-6);
        assert!((scores[1] - score2).abs() < 1e-6);
    }
}
