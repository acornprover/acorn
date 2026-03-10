use crate::kernel::clause::Clause;
use crate::kernel::variable_map::VariableMap;

/// A certificate claim line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Claim {
    /// The generic clause we are specializing.
    pub clause: Clause,

    /// Variable substitutions used for this claim.
    pub var_map: VariableMap,
}

/// A single kernel-level step in certificate generation/checking.
///
/// Parsing and generation both use this representation. Each step corresponds to one
/// line of certificate code.
#[derive(Clone, PartialEq, Eq)]
pub enum CertificateStep {
    /// A claim statement with a generic clause plus specialization map.
    Claim(Claim),
}
