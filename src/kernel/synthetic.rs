use std::collections::HashSet;
use std::sync::Arc;

use im::HashMap as ImHashMap;

use crate::elaborator::source::Source;
use crate::kernel::atom::AtomId;
#[cfg(feature = "canonicalization")]
use crate::kernel::atom::{Atom, INVALID_SYNTHETIC_MODULE};
use crate::kernel::clause::Clause;
#[cfg(feature = "canonicalization")]
use crate::kernel::symbol::Symbol;
#[cfg(feature = "canonicalization")]
use crate::kernel::term::Decomposition;
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

    /// Canonical term-level key shape (with concrete synthetic ids) used for
    /// canonicalization-mode codegen and round-tripping.
    #[cfg(feature = "canonicalization")]
    pub key_term: Term,

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

    /// Canonical term key for this synthetic definition.
    ///
    /// In canonicalization mode, this is the only identity key and never passes
    /// through `Vec<Clause>` form.
    #[cfg(feature = "canonicalization")]
    key_term: Term,

    /// Clauses that define the synthetic atoms.
    /// Here, the synthetic atoms have been remapped to the invalid range,
    /// and type variables are pinned at x0, x1, ...
    #[cfg(not(feature = "canonicalization"))]
    clauses: Vec<Clause>,
}

impl std::fmt::Display for SyntheticKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let type_vars_str: Vec<String> = self.type_vars.iter().map(|t| t.to_string()).collect();
        let types_str: Vec<String> = self.synthetic_types.iter().map(|t| t.to_string()).collect();
        #[cfg(feature = "canonicalization")]
        {
            write!(
                f,
                "SyntheticKey(type_vars: [{}], types: [{}], key_term: {})",
                type_vars_str.join(", "),
                types_str.join(", "),
                self.key_term
            )
        }
        #[cfg(not(feature = "canonicalization"))]
        {
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

    #[cfg(feature = "canonicalization")]
    fn build_key(type_vars: &[Term], synthetic_types: &[Term], key_term: &Term) -> SyntheticKey {
        SyntheticKey {
            type_vars: type_vars.to_vec(),
            synthetic_types: synthetic_types.to_vec(),
            key_term: canonicalize_synthetic_key_term(key_term),
        }
    }

    #[cfg(not(feature = "canonicalization"))]
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
    #[cfg(feature = "canonicalization")]
    pub fn lookup_by_key(
        &self,
        type_vars: &[Term],
        synthetic_types: &[Term],
        key_term: &Term,
    ) -> Option<&Arc<SyntheticDefinition>> {
        self.by_key
            .get(&Self::build_key(type_vars, synthetic_types, key_term))
    }

    #[cfg(not(feature = "canonicalization"))]
    pub fn lookup_by_key(
        &self,
        type_vars: &[Term],
        synthetic_types: &[Term],
        clauses: &[Clause],
    ) -> Option<&Arc<SyntheticDefinition>> {
        self.by_key
            .get(&Self::build_key(type_vars, synthetic_types, clauses))
    }

    /// Defines synthetic atoms with the given information.
    ///
    /// Keying canonicalization is applied internally:
    /// - defined synthetic ids are invalidated in key clauses
    /// - clauses are canonicalized with pinned type vars
    /// - clause order is sorted/deduplicated
    ///
    /// Returns an error if any of the atoms are already defined.
    #[cfg(feature = "canonicalization")]
    pub fn define(
        &mut self,
        atoms: Vec<(ModuleId, AtomId)>,
        type_vars: Vec<Term>,
        synthetic_types: Vec<Term>,
        clauses: Vec<Clause>,
        key_term: Term,
        source: Option<Source>,
    ) -> Result<(), String> {
        for atom in &atoms {
            if self.definitions.contains_key(atom) {
                return Err(format!("synthetic atom {:?} is already defined", atom));
            }
        }

        let canonical_key_term = canonicalize_synthetic_key_term(&key_term);
        let key_term_for_lookup = canonical_key_term.invalidate_synthetics(&atoms);
        let key = Self::build_key(&type_vars, &synthetic_types, &key_term_for_lookup);

        let info = Arc::new(SyntheticDefinition {
            atoms: atoms.clone(),
            type_vars,
            synthetic_types,
            clauses,
            key_term: canonical_key_term,
            source,
        });

        for atom in &atoms {
            self.definitions.insert(*atom, info.clone());
        }
        self.by_key.insert(key, info);
        Ok(())
    }

    #[cfg(not(feature = "canonicalization"))]
    pub fn define(
        &mut self,
        atoms: Vec<(ModuleId, AtomId)>,
        type_vars: Vec<Term>,
        synthetic_types: Vec<Term>,
        clauses: Vec<Clause>,
        source: Option<Source>,
    ) -> Result<(), String> {
        // Check if any atoms are already defined
        for atom in &atoms {
            if self.definitions.contains_key(atom) {
                return Err(format!("synthetic atom {:?} is already defined", atom));
            }
        }

        // In the key, normalize out the concrete ids of the defined synthetic atoms.
        let num_type_vars = type_vars.len();
        let key_clauses: Vec<Clause> = clauses
            .iter()
            .map(|c| c.invalidate_synthetics_with_pinned(&atoms, num_type_vars))
            .collect();
        let key = Self::build_key(&type_vars, &synthetic_types, &key_clauses);

        let info = Arc::new(SyntheticDefinition {
            atoms: atoms.clone(),
            type_vars,
            synthetic_types,
            clauses,
            source,
        });

        for atom in &atoms {
            self.definitions.insert(*atom, info.clone());
        }
        self.by_key.insert(key, info);
        Ok(())
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
        let mut output = vec![];
        for id in ids {
            if covered.contains(id) {
                continue;
            }
            let info = self.definitions[id].clone();
            for synthetic_id in &info.atoms {
                covered.insert(*synthetic_id);
            }
            output.push(info);
        }
        output
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

#[cfg(feature = "canonicalization")]
fn open_exists_with_replacements(term: &Term, replacements: &[Term]) -> Result<Term, String> {
    let mut current = term.clone();
    for replacement in replacements {
        let Decomposition::Exists(_, body) = current.as_ref().decompose() else {
            return Err("expected leading exists binders for synthetic key term".to_string());
        };
        current = body
            .to_owned()
            .substitute_bound(0, replacement)
            .shift_bound(0, -1);
    }
    Ok(current)
}

#[cfg(feature = "canonicalization")]
fn open_exists_with_replacements_lossy(term: &Term, replacements: &[Term]) -> Term {
    let mut current = term.clone();
    for replacement in replacements {
        let Decomposition::Exists(_, body) = current.as_ref().decompose() else {
            break;
        };
        current = body
            .to_owned()
            .substitute_bound(0, replacement)
            .shift_bound(0, -1);
    }
    current
}

#[cfg(feature = "canonicalization")]
fn reduce_head_lambda_application(term: &Term) -> Option<Term> {
    match term.as_ref().decompose() {
        Decomposition::Application(func, arg) => match func.decompose() {
            Decomposition::Lambda(_, body) => {
                let arg_term = arg.to_owned();
                // De Bruijn beta reduction:
                // (lambda. body) arg  ==>  shift(-1, substitute(body, 0, shift(+1, arg)))
                let shifted_arg = arg_term.shift_bound(0, 1);
                Some(
                    body.to_owned()
                        .substitute_bound(0, &shifted_arg)
                        .shift_bound(0, -1),
                )
            }
            _ => reduce_head_lambda_application(&func.to_owned())
                .map(|reduced_func| reduced_func.apply(&[arg.to_owned()])),
        },
        _ => None,
    }
}

#[cfg(feature = "canonicalization")]
fn reduce_head_lambda_applications(term: &Term) -> Term {
    let mut current = term.clone();
    while let Some(reduced) = reduce_head_lambda_application(&current) {
        current = reduced;
    }
    current
}

#[cfg(feature = "canonicalization")]
fn reduce_key_term_lambda_heads(term: &Term) -> Term {
    let reduced_top = reduce_head_lambda_applications(term);
    match reduced_top.as_ref().decompose() {
        Decomposition::Atom(_) => reduced_top,
        Decomposition::Application(func, arg) => {
            let reduced_func = reduce_key_term_lambda_heads(&func.to_owned());
            let reduced_arg = reduce_key_term_lambda_heads(&arg.to_owned());
            reduce_head_lambda_applications(&reduced_func.apply(&[reduced_arg]))
        }
        Decomposition::Pi(input, output) => Term::pi(
            reduce_key_term_lambda_heads(&input.to_owned()),
            reduce_key_term_lambda_heads(&output.to_owned()),
        ),
        Decomposition::Lambda(input, body) => Term::lambda(
            reduce_key_term_lambda_heads(&input.to_owned()),
            reduce_key_term_lambda_heads(&body.to_owned()),
        ),
        Decomposition::ForAll(binder_type, body) => Term::forall(
            reduce_key_term_lambda_heads(&binder_type.to_owned()),
            reduce_key_term_lambda_heads(&body.to_owned()),
        ),
        Decomposition::Exists(binder_type, body) => Term::exists(
            reduce_key_term_lambda_heads(&binder_type.to_owned()),
            reduce_key_term_lambda_heads(&body.to_owned()),
        ),
    }
}

#[cfg(feature = "canonicalization")]
pub fn canonicalize_synthetic_key_term(term: &Term) -> Term {
    let reduced = reduce_key_term_lambda_heads(term);
    crate::kernel::canonicalize::canonicalize_term(&reduced)
}

#[cfg(feature = "canonicalization")]
fn replacement_terms_for_ids(ids: &[(ModuleId, AtomId)], num_type_vars: usize) -> Vec<Term> {
    let type_args: Vec<Term> = (0..(num_type_vars as AtomId))
        .map(Term::new_variable)
        .collect();
    ids.iter()
        .map(|&(m, i)| Term::new(Atom::Symbol(Symbol::Synthetic(m, i)), type_args.clone()))
        .collect()
}

#[cfg(feature = "canonicalization")]
fn replacement_terms_for_invalid_ids(count: usize, num_type_vars: usize) -> Vec<Term> {
    let type_args: Vec<Term> = (0..(num_type_vars as AtomId))
        .map(Term::new_variable)
        .collect();
    (0..count)
        .map(|i| {
            Term::new(
                Atom::Symbol(Symbol::Synthetic(INVALID_SYNTHETIC_MODULE, i as AtomId)),
                type_args.clone(),
            )
        })
        .collect()
}

#[cfg(feature = "canonicalization")]
pub fn build_definition_key_term_from_exists(
    term: &Term,
    atoms: &[(ModuleId, AtomId)],
    num_type_vars: usize,
) -> Result<Term, String> {
    let replacements = replacement_terms_for_ids(atoms, num_type_vars);
    let opened = open_exists_with_replacements_lossy(term, &replacements);
    Ok(canonicalize_synthetic_key_term(&opened))
}

#[cfg(feature = "canonicalization")]
pub fn build_lookup_key_term_from_exists(
    term: &Term,
    num_witnesses: usize,
    num_type_vars: usize,
) -> Result<Term, String> {
    let replacements = replacement_terms_for_invalid_ids(num_witnesses, num_type_vars);
    let opened = open_exists_with_replacements(term, &replacements)?;
    Ok(canonicalize_synthetic_key_term(&opened))
}

impl Default for SyntheticRegistry {
    fn default() -> Self {
        Self::new()
    }
}
