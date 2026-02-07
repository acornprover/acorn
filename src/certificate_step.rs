use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::Term;
use crate::module::ModuleId;

/// A single kernel-level step in certificate generation/checking.
///
/// Parsing uses `LetSatisfy` and `Claim`. Generation also uses kernel-only helper
/// variants to represent one line before generating code strings.
#[derive(Clone)]
pub enum CertificateStep {
    /// Define one arbitrary witness constant for a concrete type.
    DefineArbitrary {
        /// Kernel type term for the witness being introduced.
        /// This is the key used in `SyntheticNameSet.arbitrary_names`.
        var_type: Term,

        /// Local context used to denormalize `var_type` into user-facing type syntax.
        /// Needed because free-variable types are interpreted relative to context.
        local_context: LocalContext,
    },

    /// Define one synthetic group produced by normalization.
    DefineSynthetic {
        /// Synthetic atom IDs introduced together by this definition.
        /// Each pair is `(module_id, local_atom_id)` and maps to a generated `sN` name.
        atoms: Vec<(ModuleId, AtomId)>,

        /// Type-variable kind terms (in var-id order) for the synthetic definition.
        /// Each entry is either `Type`-like or a typeclass kind constraint.
        type_vars: Vec<Term>,

        /// Kernel clauses that define the synthetic condition.
        /// These clauses are converted into the `satisfy { ... }` body.
        clauses: Vec<Clause>,
    },

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
