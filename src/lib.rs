#![allow(unexpected_cfgs)]

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
pub mod lint;
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
