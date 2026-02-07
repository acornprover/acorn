use crate::kernel::clause::Clause;

/// Result of parsing a single line of certificate code.
///
/// This is the boundary where name resolution happens: certificate strings use names
/// like "Nat.add", which get resolved to current numeric IDs during parsing.
/// This makes certificates robust to refactoring (see `Certificate` docs).
pub enum CertificateStep {
    /// A let...satisfy statement. Sets up bindings for subsequent claims.
    ///
    /// These map user-chosen names (like "s0") to existing synthetic constants.
    /// The synthetic constants themselves are created during goal normalization,
    /// not from the certificate - the certificate just establishes the name mapping.
    LetSatisfy {
        /// Clauses from the satisfy condition (empty for trivial conditions like `true`).
        clauses_to_insert: Vec<Clause>,
    },

    /// A claim statement with clauses to check.
    Claim(Vec<Clause>),
}
