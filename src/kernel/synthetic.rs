use std::collections::HashSet;
use std::sync::Arc;

use im::HashMap as ImHashMap;

use crate::elaborator::source::Source;
use crate::kernel::atom::{Atom, AtomId};
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

/// The SyntheticKey normalizes out the specific choice of id for the synthetic atoms
/// in the SyntheticDefinition.
/// This lets us check if two different synthetic atoms would be "defined the same way".
///
/// Note: Uses Vec<Clause> for matching because clauses have been individually normalized
/// and this is the format used in both definition and lookup paths.
#[derive(Hash, Eq, PartialEq, Debug, Clone)]
struct SyntheticKey {
    /// The kinds of the type variables (e.g., Type for unconstrained type params).
    /// These are "pinned" as x0, x1, ... in all clauses.
    type_vars: Vec<Term>,

    /// The types of the synthetic atoms.
    synthetic_types: Vec<Term>,

    /// Clauses that define the synthetic atoms.
    /// Here, the synthetic atoms have been remapped to the invalid range,
    /// and type variables are pinned at x0, x1, ...
    clauses: Vec<Clause>,
}

impl std::fmt::Display for SyntheticKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let type_vars_str: Vec<String> = self.type_vars.iter().map(|t| t.to_string()).collect();
        let types_str: Vec<String> = self.synthetic_types.iter().map(|t| t.to_string()).collect();
        let clauses_str: Vec<String> = self.clauses.iter().map(|c| c.to_string()).collect();
        write!(
            f,
            "SyntheticKey(type_vars: [{}], types: [{}], clauses: {})",
            type_vars_str.join(", "),
            types_str.join(", "),
            clauses_str.join(" and ")
        )
    }
}

/// A registry for synthetic atom definitions.
///
/// The registry stores synthetic definitions indexed in two ways:
/// 1. By (ModuleId, AtomId) for direct lookup
/// 2. By a normalized key for deduplication (finding equivalent definitions)
#[derive(Clone)]
pub struct SyntheticRegistry {
    /// The definition for each synthetic atom, indexed by (ModuleId, AtomId).
    /// Uses im::HashMap for O(1) clones with structural sharing.
    definitions: ImHashMap<(ModuleId, AtomId), Arc<SyntheticDefinition>>,

    /// Same information as `definitions`, but indexed by SyntheticKey.
    /// This is used to avoid defining the same thing multiple times.
    /// Uses im::HashMap for O(1) clones with structural sharing.
    by_key: ImHashMap<SyntheticKey, Arc<SyntheticDefinition>>,
}

impl SyntheticRegistry {
    pub fn new() -> Self {
        SyntheticRegistry {
            definitions: ImHashMap::new(),
            by_key: ImHashMap::new(),
        }
    }

    /// Returns true if the given synthetic atom has been defined.
    pub fn contains(&self, id: &(ModuleId, AtomId)) -> bool {
        self.definitions.contains_key(id)
    }

    /// Gets the definition for a synthetic atom by its id.
    pub fn get(&self, id: &(ModuleId, AtomId)) -> Option<&Arc<SyntheticDefinition>> {
        self.definitions.get(id)
    }

    /// Build a canonical synthetic key from raw key components.
    ///
    /// This canonicalizes each clause with pinned type variables, then sorts and deduplicates
    /// the clause list to make key matching deterministic and order-insensitive.
    fn build_key(type_vars: &[Term], synthetic_types: &[Term], clauses: &[Clause]) -> SyntheticKey {
        let pinned = type_vars.len();
        let mut canonical_clauses: Vec<Clause> = clauses
            .iter()
            .map(|c| c.key_canonicalized_with_pinned(pinned))
            .collect();

        canonical_clauses.sort_by(|a, b| {
            a.literals
                .cmp(&b.literals)
                .then_with(|| a.context.get_var_types().cmp(b.context.get_var_types()))
        });
        canonical_clauses.dedup();

        SyntheticKey {
            type_vars: type_vars.to_vec(),
            synthetic_types: synthetic_types.to_vec(),
            clauses: canonical_clauses,
        }
    }

    /// Looks up a definition by its normalized key components.
    /// Returns the existing definition if one with equivalent structure exists.
    pub fn lookup_by_key(
        &self,
        type_vars: &[Term],
        synthetic_types: &[Term],
        clauses: &[Clause],
    ) -> Option<&Arc<SyntheticDefinition>> {
        self.by_key
            .get(&Self::build_key(type_vars, synthetic_types, clauses))
    }

    /// Returns all synthetic atom IDs that have been defined.
    #[cfg(test)]
    pub fn get_ids(&self) -> Vec<(ModuleId, AtomId)> {
        self.definitions.keys().copied().collect()
    }

    /// Given a list of (module_id, atom_id) for synthetic atoms that we need to define,
    /// find a set of SyntheticDefinition that covers them.
    /// The output may have synthetic atoms that aren't used in the input.
    /// The input doesn't have to be in order and may contain duplicates.
    pub fn find_covering_info(&self, ids: &[(ModuleId, AtomId)]) -> Vec<Arc<SyntheticDefinition>> {
        let mut covered = HashSet::new();
        let mut infos = vec![];
        for id in ids {
            if covered.contains(id) {
                continue;
            }
            let info = self.definitions[id].clone();
            for synthetic_id in &info.atoms {
                covered.insert(*synthetic_id);
            }
            infos.push(info);
        }

        // Order definitions so dependencies appear first when possible.
        // This avoids generating `let ... satisfy` bodies that reference unknown local symbols.
        let mut atom_to_info_idx = std::collections::HashMap::new();
        for (idx, info) in infos.iter().enumerate() {
            for atom in &info.atoms {
                atom_to_info_idx.insert(*atom, idx);
            }
        }

        let mut deps_by_info: Vec<HashSet<usize>> = vec![HashSet::new(); infos.len()];
        for (idx, info) in infos.iter().enumerate() {
            let mut dep_atoms: HashSet<(ModuleId, AtomId)> = HashSet::new();
            for clause in &info.clauses {
                for literal in &clause.literals {
                    for term in [&literal.left, &literal.right] {
                        for atom in term.iter_atoms() {
                            if let &Atom::Symbol(crate::kernel::symbol::Symbol::Synthetic(
                                module_id,
                                local_id,
                            )) = atom
                            {
                                dep_atoms.insert((module_id, local_id));
                            }
                        }
                    }
                }
            }
            for dep_atom in dep_atoms {
                if let Some(dep_idx) = atom_to_info_idx.get(&dep_atom).copied() {
                    if dep_idx != idx {
                        deps_by_info[idx].insert(dep_idx);
                    }
                }
            }
        }

        let mut placed = HashSet::new();
        let mut ordered = vec![];
        let mut remaining: Vec<usize> = (0..infos.len()).collect();
        loop {
            let mut progress = false;
            let mut i = 0;
            while i < remaining.len() {
                let idx = remaining[i];
                if deps_by_info[idx].iter().all(|dep| placed.contains(dep)) {
                    ordered.push(infos[idx].clone());
                    placed.insert(idx);
                    remaining.remove(i);
                    progress = true;
                } else {
                    i += 1;
                }
            }
            if remaining.is_empty() {
                break;
            }
            if !progress {
                // Fall back to the original order if dependencies are cyclic/ambiguous.
                for idx in remaining {
                    ordered.push(infos[idx].clone());
                }
                break;
            }
        }
        ordered
    }

    /// Merges another SyntheticRegistry into this one.
    pub fn merge(&mut self, other: &SyntheticRegistry) {
        for (k, v) in other.definitions.iter() {
            self.definitions.insert(*k, v.clone());
        }
        for (k, v) in other.by_key.iter() {
            self.by_key.insert(k.clone(), v.clone());
        }
    }
}

impl Default for SyntheticRegistry {
    fn default() -> Self {
        Self::new()
    }
}
