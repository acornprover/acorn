use std::fmt;

use serde::{Deserialize, Serialize};

use super::atom::AtomId;
use super::types::{GroundTypeId, TypeclassId};
use crate::module::ModuleId;

/// A Symbol represents named constants, functions, and primitive values in the environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Symbol {
    // The boolean constant true.
    True,

    // The boolean constant false.
    False,

    // Logical negation: Bool -> Bool.
    Not,

    // Logical conjunction: Bool -> Bool -> Bool.
    And,

    // Logical disjunction: Bool -> Bool -> Bool.
    Or,

    // Polymorphic equality: Pi(T: Type0). T -> T -> Bool.
    Eq,

    // Polymorphic if-then-else: Pi(T: Type0). Bool -> T -> T -> T.
    Ite,

    // Choice operator: Pi(T: Type0). (T -> Bool) -> T.
    // This is introduced by prover rules (e.g. existential activation), not directly by parsing.
    #[cfg(not(feature = "nwit"))]
    Choose,

    // The Bool type.
    Bool,

    // The type of types (kind *). Called "Type" in the language but "Type0" here
    // to distinguish from the Type(GroundTypeId) variant which is for user-defined types.
    Type0,

    // A ground type, used in type terms to represent user-defined types like Nat, Int, etc.
    // Ground types have no internal structure - they are atomic type constants.
    // Note: Bool and Type0 are NOT GroundTypeIds - they have their own variants.
    Type(GroundTypeId),

    // A typeclass used as a type constraint for type variables.
    // When a type variable x has type Typeclass(Monoid), it means x is constrained to
    // types that implement Monoid.
    Typeclass(TypeclassId),

    // Constant values that are accessible anywhere in the code.
    // This includes concepts like addition, zero, and the axioms.
    // The ModuleId identifies which module defined this constant.
    GlobalConstant(ModuleId, AtomId),

    // Constant values that are only accessible inside a particular block.
    ScopedConstant(AtomId),
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::True => write!(f, "true"),
            Symbol::False => write!(f, "false"),
            Symbol::Not => write!(f, "not"),
            Symbol::And => write!(f, "and"),
            Symbol::Or => write!(f, "or"),
            Symbol::Eq => write!(f, "eq"),
            Symbol::Ite => write!(f, "ite"),
            #[cfg(not(feature = "nwit"))]
            Symbol::Choose => write!(f, "choose"),
            Symbol::Bool => write!(f, "Bool"),
            Symbol::Type0 => write!(f, "Type0"),
            Symbol::Type(t) => write!(f, "T{}_{}", t.module_id().get(), t.local_id()),
            Symbol::Typeclass(tc) => {
                write!(f, "tc{}_{}", tc.module_id().get(), tc.local_id())
            }
            Symbol::GlobalConstant(m, i) => write!(f, "g{}_{}", m.get(), i),
            Symbol::ScopedConstant(i) => write!(f, "c{}", i),
        }
    }
}
