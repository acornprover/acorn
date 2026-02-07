use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::module::ModuleId;

/// A single kernel-level step in certificate generation/checking.
///
/// Parsing and generation both use this representation. Each step corresponds to one
/// line of certificate code.
#[derive(Clone, PartialEq, Eq)]
pub enum CertificateStep {
    /// Define one arbitrary witness constant for a concrete type.
    DefineArbitrary {
        /// Kernel symbol for the witness constant.
        /// This is expected to be a local scoped constant.
        symbol: Symbol,
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

    /// A claim statement with one concrete clause to check.
    Claim(Clause),
}
