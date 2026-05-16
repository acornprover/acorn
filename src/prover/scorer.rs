use std::error::Error;
use std::sync::atomic::{AtomicU8, Ordering};

use super::depth_first_scorer::DepthFirstScorer;
use super::features::Features;
use super::handcrafted_scorer::HandcraftedScorer;
use super::onnx_factual_penalty::OnnxFactualPenalty;
use super::scoring_model::ScoringModel;

pub trait Scorer {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>>;

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        Ok(features.iter().map(|f| self.score(f).unwrap()).collect())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ScorerKind {
    Onnx = 0,
    Handcrafted = 1,
    DepthFirst = 2,
    OnnxFactualPenalty = 3,
}

impl ScorerKind {
    pub fn parse(s: &str) -> Result<ScorerKind, String> {
        match s {
            "onnx" => Ok(ScorerKind::Onnx),
            "handcrafted" => Ok(ScorerKind::Handcrafted),
            "depthfirst" | "depth-first" => Ok(ScorerKind::DepthFirst),
            "onnx-factual-penalty" | "factual-penalty" => Ok(ScorerKind::OnnxFactualPenalty),
            _ => Err(format!(
                "unknown scorer '{}'. Expected one of: onnx, handcrafted, depthfirst, onnx-factual-penalty",
                s
            )),
        }
    }
}

static SCORER_KIND: AtomicU8 = AtomicU8::new(ScorerKind::Onnx as u8);
static FACTUAL_PENALTY_BITS: std::sync::atomic::AtomicU32 =
    std::sync::atomic::AtomicU32::new(0x3f800000); // 1.0_f32.to_bits()

pub fn set_default_scorer_kind(kind: ScorerKind) {
    SCORER_KIND.store(kind as u8, Ordering::Relaxed);
}

pub fn set_factual_penalty(penalty: f32) {
    FACTUAL_PENALTY_BITS.store(penalty.to_bits(), Ordering::Relaxed);
}

pub fn factual_penalty() -> f32 {
    f32::from_bits(FACTUAL_PENALTY_BITS.load(Ordering::Relaxed))
}

pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    match SCORER_KIND.load(Ordering::Relaxed) {
        x if x == ScorerKind::Handcrafted as u8 => Box::new(HandcraftedScorer),
        x if x == ScorerKind::DepthFirst as u8 => Box::new(DepthFirstScorer),
        x if x == ScorerKind::OnnxFactualPenalty as u8 => {
            Box::new(OnnxFactualPenalty::new().expect(
                "ONNX scorer failed to load. \
                 Call init_default_scorer() at startup to surface this error cleanly.",
            ))
        }
        _ => Box::new(ScoringModel::load().expect(
            "ONNX scorer failed to load. \
             Call init_default_scorer() at startup to surface this error cleanly.",
        )),
    }
}

/// Eagerly loads the default scorer so a misconfigured ONNX runtime surfaces
/// here, at one well-known site, instead of as a panic inside the first prover
/// construction. Intended to be called once from binary entry points.
pub fn init_default_scorer() -> Result<(), Box<dyn Error>> {
    ScoringModel::load().map(drop)
}
