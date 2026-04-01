#![allow(unexpected_cfgs)]

#[cfg(feature = "nocnf")]
compile_error!("feature \"nocnf\" is not supported with named-witness certificates");

pub mod build_cache;
pub mod builder;
pub mod certificate;
pub mod claim_codec;
pub mod cleaner;
pub mod code_generator;
pub mod common;
pub mod doc_generator;
pub mod elaborator;
pub mod exporter;
pub mod interfaces;
pub mod kernel;
pub mod manifest;
pub mod module;
pub mod ort_utils;
pub mod processor;
pub mod project;
pub mod proof_display;
pub mod prover;
pub mod server;
pub mod syntax;
pub mod verifier;

#[cfg(test)]
mod tests;
