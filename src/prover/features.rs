use ndarray::{Array1, Array2, Axis};

use crate::kernel::proof_step::{ProofStep, Truthiness};

// Features of a proof step that can be used to score it.
// This is like a feature vector but in struct rather than vector form.
// Try to only use bools, i32s, and f32s.
pub struct Features {
    pub is_contradiction: bool,

    // Features from the clause
    pub atom_count: i32,

    // Features from truthiness
    pub is_counterfactual: bool,
    pub is_hypothetical: bool,
    pub is_factual: bool,

    // Features from the rule
    pub is_assumption: bool,
    pub is_negated_goal: bool,

    // Features from the search process
    pub proof_size: i32,
    pub depth: i32,
}

const NUM_FEATURES: usize = 9;

impl Features {
    pub fn new(step: &ProofStep) -> Self {
        Features {
            is_contradiction: step.clause.is_impossible(),
            atom_count: step.clause.atom_count() as i32,
            is_counterfactual: step.truthiness == Truthiness::Counterfactual,
            is_hypothetical: step.truthiness == Truthiness::Hypothetical,
            is_factual: step.truthiness == Truthiness::Factual,
            is_assumption: step.rule.is_underlying_assumption(),
            is_negated_goal: step.rule.is_underlying_negated_goal(),
            proof_size: step.proof_size as i32,
            depth: step.depth as i32,
        }
    }

    pub fn to_floats(&self) -> [f32; NUM_FEATURES] {
        [
            self.is_contradiction as i8 as f32,
            self.atom_count as f32,
            self.is_counterfactual as i8 as f32,
            self.is_hypothetical as i8 as f32,
            self.is_factual as i8 as f32,
            self.is_assumption as i8 as f32,
            self.is_negated_goal as i8 as f32,
            self.proof_size as f32,
            self.depth as f32,
        ]
    }

    pub fn to_array(&self) -> Array1<f32> {
        Array1::from(self.to_floats().to_vec())
    }

    // Create an array of size (number of items, number of features) from a slice of features.
    // Each row is a feature vector.
    pub fn to_array2(features_slice: &[Features]) -> Array2<f32> {
        let num_rows = features_slice.len();
        assert_ne!(num_rows, 0);

        let mut array2 = Array2::zeros((num_rows, NUM_FEATURES));

        // Fill the Array2 with the feature vectors
        for (i, features) in features_slice.iter().enumerate() {
            let feature_row = features.to_array();
            array2.index_axis_mut(Axis(0), i).assign(&feature_row);
        }

        array2
    }
}
