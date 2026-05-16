use std::collections::BTreeMap;
use std::fmt;

use crate::kernel::proof_step::{ProofStep, Truthiness};

pub mod active_set;
pub mod dataset;
pub mod depth_first_scorer;
pub mod features;
pub mod handcrafted_scorer;
pub mod onnx_factual_penalty;
pub mod passive_set;
pub mod proof;
mod prover;
pub mod rewrite_tree;
pub mod score;
pub mod scorer;
pub mod scoring_model;
pub(crate) mod synthetic;

// Re-export the main public types
pub use prover::Prover;
pub use scorer::{init_default_scorer, set_default_scorer_kind, set_factual_penalty, ScorerKind};

/// Instrumentation collected during one prover search.
#[derive(Clone, Debug, Default)]
pub struct SearchStats {
    pub initial_passive_len: usize,
    pub initial_active_len: usize,
    pub final_passive_len: usize,
    pub final_active_len: usize,
    pub max_passive_len: usize,
    pub activated_steps: usize,
    pub factual_activations: usize,
    pub nonfactual_activations: usize,
    pub generated_steps: usize,
    pub accepted_steps: usize,
    pub auto_rejected_steps: usize,
    pub simplified_away_steps: usize,
    pub passive_simplification_steps: usize,
    pub scoring_time_secs: f64,
    pub passive_indexing_time_secs: f64,
    pub activation_time_secs: f64,
    pub active_inference_time_secs: f64,
    pub active_simplification_time_secs: f64,
    pub passive_simplification_time_secs: f64,
    pub activated_by_rule: BTreeMap<String, usize>,
    pub generated_by_rule: BTreeMap<String, usize>,
}

impl SearchStats {
    pub fn new(initial_passive_len: usize, initial_active_len: usize) -> Self {
        Self {
            initial_passive_len,
            initial_active_len,
            max_passive_len: initial_passive_len,
            ..Self::default()
        }
    }

    pub fn record_activation(&mut self, step: &ProofStep) {
        self.activated_steps += 1;
        if step.truthiness == Truthiness::Factual {
            self.factual_activations += 1;
        } else {
            self.nonfactual_activations += 1;
        }
        *self
            .activated_by_rule
            .entry(step.rule.name().to_string())
            .or_default() += 1;
    }

    pub fn record_generated(&mut self, step: &ProofStep) {
        self.generated_steps += 1;
        *self
            .generated_by_rule
            .entry(step.rule.name().to_string())
            .or_default() += 1;
    }

    pub fn record_generated_batch(&mut self, steps: &[ProofStep]) {
        for step in steps {
            self.record_generated(step);
        }
    }
}

/// Mode controlling proof search behavior
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ProverMode {
    /// About as long as a human is willing to wait for a proof.
    /// The timeout_secs parameter controls how long to search before giving up.
    /// The activation_limit parameter controls the cap on non-factual activations.
    Interactive {
        timeout_secs: f32,
        activation_limit: i32,
    },

    /// A shallow-only search with configurable limits.
    /// Stops as soon as the prover reaches the shallow frontier.
    Shallow {
        timeout_secs: f32,
        activation_limit: i32,
    },

    /// A fast search that only uses shallow steps, for testing.
    Test,
}

/// The outcome of a proof search
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    ShallowExhausted,
    ShallowExplosion,
    Exhausted,
    Inconsistent,
    Interrupted,
    Timeout,
    ActivationCap,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::ShallowExhausted => write!(f, "ShallowExhausted"),
            Outcome::ShallowExplosion => write!(f, "ShallowExplosion"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Timeout => write!(f, "Timeout"),
            Outcome::ActivationCap => write!(f, "ActivationCap"),
        }
    }
}
