use std::fmt;

pub mod active_set;
pub mod dataset;
pub mod features;
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

    /// A fast search that only uses shallow steps, for testing.
    Test,
}

/// The outcome of a proof search
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    Exhausted,
    Inconsistent,
    Interrupted,
    Timeout,
    Constrained,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Timeout => write!(f, "Timeout"),
            Outcome::Constrained => write!(f, "Constrained"),
        }
    }
}
