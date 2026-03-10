use std::cmp::Ordering;
use std::fmt;

use serde::{Deserialize, Serialize};

use super::symbol::Symbol;

pub type AtomId = u16;

/// An atomic value does not have any internal structure.
/// The Atom is a lower-level representation.
/// It is used in the prover, but not in the AcornValue / Environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Atom {
    // A free variable used in clauses and unification.
    // These have unique IDs and their types are tracked in LocalContext.
    FreeVariable(AtomId),

    // A bound variable using de Bruijn indexing.
    // BoundVariable(0) refers to the closest enclosing Pi binder.
    // These only appear inside Pi output types and don't participate in unification.
    BoundVariable(u16),

    // A symbol representing a constant, function, type, or boolean.
    Symbol(Symbol),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::FreeVariable(i) => write!(f, "x{}", i),
            Atom::BoundVariable(i) => write!(f, "b{}", i),
            Atom::Symbol(s) => write!(f, "{}", s),
        }
    }
}

impl Atom {
    pub fn new(s: &str) -> Atom {
        match Atom::parse(s) {
            Some(atom) => atom,
            None => panic!("failed to parse atom: '{}'", s),
        }
    }

    pub fn parse(s: &str) -> Option<Atom> {
        let mut chars = s.trim().chars();
        let first = chars.next()?;
        let rest = chars.as_str();
        match first {
            'g' => {
                // Format: g{module_id}_{local_id} or g{local_id} (with implicit module_id 0)
                let parts: Vec<&str> = rest.split('_').collect();
                if parts.len() == 2 {
                    // New format: g{module_id}_{local_id}
                    let module_id = crate::module::ModuleId(parts[0].parse().ok()?);
                    let local_id: AtomId = parts[1].parse().ok()?;
                    Some(Atom::Symbol(Symbol::GlobalConstant(module_id, local_id)))
                } else if parts.len() == 1 {
                    // Old format for tests: g{local_id} -> module 0
                    let local_id: AtomId = rest.parse().ok()?;
                    Some(Atom::Symbol(Symbol::GlobalConstant(
                        crate::module::ModuleId(0),
                        local_id,
                    )))
                } else {
                    None
                }
            }
            'c' => Some(Atom::Symbol(Symbol::ScopedConstant(rest.parse().ok()?))),
            'x' => Some(Atom::FreeVariable(rest.parse().ok()?)),
            'b' => Some(Atom::BoundVariable(rest.parse().ok()?)),
            _ => None,
        }
    }

    pub fn is_scoped_constant(&self) -> bool {
        matches!(self, Atom::Symbol(Symbol::ScopedConstant(_)))
    }

    /// Returns true if this is a free variable (used in unification).
    pub fn is_free_variable(&self) -> bool {
        matches!(self, Atom::FreeVariable(_))
    }

    /// Returns true if this is a bound variable (de Bruijn index).
    pub fn is_bound_variable(&self) -> bool {
        matches!(self, Atom::BoundVariable(_))
    }

    /// Returns true if this is any kind of variable (free or bound).
    pub fn is_variable(&self) -> bool {
        matches!(self, Atom::FreeVariable(_) | Atom::BoundVariable(_))
    }

    /// Returns the TypeclassId if this is a Typeclass symbol.
    pub fn as_typeclass(&self) -> Option<super::types::TypeclassId> {
        match self {
            Atom::Symbol(Symbol::Typeclass(id)) => Some(*id),
            _ => None,
        }
    }

    // Orders two atoms, but considers all free variables the same, so that the ordering
    // is stable under variable renaming.
    // True and False always sort before other atoms to ensure literals have the expected orientation.
    pub fn stable_partial_order(&self, other: &Atom) -> Ordering {
        // Helper to check if an atom is a boolean constant (True or False)
        fn is_bool_constant(atom: &Atom) -> bool {
            matches!(
                atom,
                Atom::Symbol(Symbol::True) | Atom::Symbol(Symbol::False)
            )
        }

        match (self, other) {
            // All free variables are considered equal for stable ordering
            (Atom::FreeVariable(_), Atom::FreeVariable(_)) => Ordering::Equal,
            // Bound variables are compared by index (they're structural, not semantic)
            (Atom::BoundVariable(a), Atom::BoundVariable(b)) => a.cmp(b),
            // Bool constants sort before everything except other bool constants
            (a, b) if is_bool_constant(a) && is_bool_constant(b) => a.cmp(b),
            (a, _) if is_bool_constant(a) => Ordering::Less,
            (_, b) if is_bool_constant(b) => Ordering::Greater,
            (x, y) => x.cmp(y),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::ModuleId;

    #[test]
    fn test_atom_ordering() {
        assert!(Atom::Symbol(Symbol::True) < Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)));
        assert!(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0))
                < Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1))
        );
    }

    #[test]
    fn test_atom_stable_partial_ordering() {
        assert_eq!(
            Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0))
                .stable_partial_order(&Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 1))),
            Ordering::Less
        );
        // All free variables are equal for stable ordering
        assert_eq!(
            Atom::FreeVariable(0).stable_partial_order(&Atom::FreeVariable(1)),
            Ordering::Equal
        );
        // Bound variables compare by index
        assert_eq!(
            Atom::BoundVariable(0).stable_partial_order(&Atom::BoundVariable(1)),
            Ordering::Less
        );
    }

    #[test]
    fn test_atom_size() {
        // Atom should be small since it's used extensively in the prover.
        // GlobalConstant now uses (ModuleId, AtomId) which is (u16, u16) = 4 bytes.
        // With discriminant and padding, total size is 6 bytes.
        assert_eq!(std::mem::size_of::<Atom>(), 6);
    }
}
