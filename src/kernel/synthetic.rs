use crate::elaborator::source::Source;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::term::Term;
use crate::module::ModuleId;

/// Information about the definition of a set of synthetic atoms.
pub struct SyntheticDefinition {
    /// The synthetic atoms that are defined in this definition.
    /// Each of these should be present in clauses.
    pub atoms: Vec<(ModuleId, AtomId)>,

    /// The kinds of the type variables (e.g., Type for unconstrained type params).
    /// These are "pinned" as x0, x1, ... in all clauses.
    /// Empty in non-polymorphic mode.
    pub type_vars: Vec<Term>,

    /// The types of the synthetic atoms (one per atom).
    /// For polymorphic synthetics, these types may contain FreeVariable references
    /// to the pinned type parameters.
    pub synthetic_types: Vec<Term>,

    /// The clauses are true by construction and describe the synthetic atoms.
    /// Type variables are pinned at x0, x1, ... across all clauses.
    pub clauses: Vec<Clause>,

    /// The source location where this synthetic definition originated.
    pub source: Option<Source>,
}

impl std::fmt::Display for SyntheticDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let type_vars_str: Vec<String> = self.type_vars.iter().map(|t| t.to_string()).collect();
        let types_str: Vec<String> = self.synthetic_types.iter().map(|t| t.to_string()).collect();
        let clauses_str: Vec<String> = self.clauses.iter().map(|c| c.to_string()).collect();
        write!(
            f,
            "SyntheticDefinition(atoms: {:?}, type_vars: [{}], types: [{}], clauses: {})",
            self.atoms,
            type_vars_str.join(", "),
            types_str.join(", "),
            clauses_str.join(" and ")
        )
    }
}
