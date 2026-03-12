#![allow(unexpected_cfgs)]

#[cfg(all(feature = "nwit", feature = "nocnf"))]
compile_error!("features \"nwit\" and \"nocnf\" are not supported together");

pub mod build_cache;
pub mod builder;
pub mod certificate;
pub mod cleaner;
pub mod code_generator;
pub mod common;
pub mod doc_generator;
pub mod elaborator;
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
