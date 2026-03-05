use serde::{Deserialize, Serialize};
use std::fmt;

use crate::module::ModuleId;

// Note: Bool and TypeSort are now Symbol variants (in symbol.rs),
// not GroundTypeIds. GroundTypeId is now only used for user-defined ground types.

/// A type ID that refers ONLY to a ground type (no internal structure).
/// Examples: Nat, Int, user-defined data types without parameters.
/// NOT for: function types, parameterized types like List[T], or built-in types (Bool, TypeSort).
///
/// This distinction is important because:
/// - `Term::ground_type(GroundTypeId)` creates an atomic type term
/// - `Atom::Type(GroundTypeId)` ensures atoms only contain ground types
///
/// The GroundTypeId includes a ModuleId to enable module-scoped type numbering,
/// allowing incremental builds where changing one module doesn't renumber types in others.
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize, Default,
)]
pub struct GroundTypeId(ModuleId, u16);

impl GroundTypeId {
    /// Create a new GroundTypeId with explicit module and local id.
    pub const fn new(module_id: ModuleId, local_id: u16) -> GroundTypeId {
        GroundTypeId(module_id, local_id)
    }

    /// Create a GroundTypeId for module 0 (for tests and backwards compatibility).
    #[cfg(test)]
    pub const fn test(local_id: u16) -> GroundTypeId {
        GroundTypeId(ModuleId(0), local_id)
    }

    pub fn module_id(self) -> ModuleId {
        self.0
    }

    pub fn local_id(self) -> u16 {
        self.1
    }
}

impl fmt::Display for GroundTypeId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}_{}", self.0.get(), self.1)
    }
}

/// A typeclass identifier that uniquely identifies a typeclass in the type system.
/// Includes a ModuleId for module-scoped numbering.
#[derive(
    Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize, Default,
)]
pub struct TypeclassId(ModuleId, u16);

impl TypeclassId {
    /// Create a new TypeclassId with explicit module and local id.
    pub const fn new(module_id: ModuleId, local_id: u16) -> TypeclassId {
        TypeclassId(module_id, local_id)
    }

    /// Create a TypeclassId for module 0 (for tests and backwards compatibility).
    #[cfg(test)]
    pub const fn test(local_id: u16) -> TypeclassId {
        TypeclassId(ModuleId(0), local_id)
    }

    pub fn module_id(self) -> ModuleId {
        self.0
    }

    pub fn local_id(self) -> u16 {
        self.1
    }
}

impl fmt::Display for TypeclassId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}_{}", self.0.get(), self.1)
    }
}
