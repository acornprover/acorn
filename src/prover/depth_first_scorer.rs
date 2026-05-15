use std::error::Error;

use super::features::Features;
use super::scorer::Scorer;

// Always scores zero, so within each (contradiction, shallow_status) tier the
// BTreeSet falls back to clause-id order. Since clause ids increase with
// insertion, this yields LIFO/depth-first activation.
pub struct DepthFirstScorer;

impl Scorer for DepthFirstScorer {
    fn score(&self, _features: &Features) -> Result<f32, Box<dyn Error>> {
        Ok(0.0)
    }
}
