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
