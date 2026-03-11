use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
use crate::elaborator::acorn_value::{AcornValue, ConstantInstance};
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;

/// A fact is a statement that we are assuming to be true in a particular context.
#[derive(Clone, Debug)]
pub enum Fact {
    /// A true statement representable as a boolean value.
    Proposition(Arc<Proposition>),

    /// The first typeclass extends this set of typeclasses.
    /// The optional witness provider is a constant of shape `forall(P: Typeclass). P`.
    Extends(
        Typeclass,
        HashSet<Typeclass>,
        Option<PotentialValue>,
        Source,
    ),

    /// The fact that this class is an instance of this typeclass.
    Instance(Datatype, Typeclass, Source),

    /// A defined constant.
    /// The tuple is the name of the constant, the definition, and the source.
    /// Can be generic or not, depending on the potential value.
    Definition(PotentialValue, AcornValue, Source),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Fact::Proposition(p) => write!(f, "prop: {}", p.source.description()),
            Fact::Extends(tc, base_set, _, _) => {
                if base_set.is_empty() {
                    write!(f, "{} extends nothing", tc.name)
                } else {
                    let mut names: Vec<String> = base_set.iter().map(|t| t.name.clone()).collect();
                    names.sort();
                    write!(f, "{} extends {}", tc.name, names.join(", "))
                }
            }
            Fact::Instance(class, typeclass, _) => {
                write!(f, "{} is an instance of {}", class.name, typeclass.name)
            }
            Fact::Definition(_, _, source) => write!(f, "{}", source.description()),
        }
    }
}

impl Fact {
    pub fn proposition(value: AcornValue, source: Source) -> Fact {
        Fact::Proposition(Arc::new(Proposition::new(value, vec![], source)))
    }

    pub fn source(&self) -> &Source {
        match self {
            Fact::Proposition(p) => &p.source,
            Fact::Extends(_, _, _, source) => source,
            Fact::Instance(_, _, source) => source,
            Fact::Definition(_, _, source) => source,
        }
    }

    /// A fact that is used is normalization means that we still need it, even if it isn't used by
    /// the prover.
    pub fn used_in_normalization(&self) -> bool {
        match self {
            Fact::Instance(..) => true,
            Fact::Extends(..) => true,
            Fact::Definition(PotentialValue::Resolved(AcornValue::Constant(ci)), _, _) => {
                // Instance implementation symbols are only meant to exist while elaborating an
                // `instance` block, but later public bridge facts still refer to them. Keep their
                // definitions in normalized/imported state even though user code never names them.
                matches!(ci.name, ConstantName::InstanceAttribute(..))
                    || self.as_instance_alias().is_some()
            }
            _ => self.as_instance_alias().is_some(),
        }
    }

    /// Returns Some(..) if this fact is an aliasing for an instance of a typeclass constant.
    /// I.e., it's part of an instance statement with "let _ = _" so that it's an alias of a previously
    /// defined constant.
    pub fn as_instance_alias(&self) -> Option<(ConstantInstance, &ConstantName, AcornType)> {
        if let Fact::Definition(potential, definition, _) = self {
            if let PotentialValue::Resolved(AcornValue::Constant(ci)) = potential {
                if let Some(name) = definition.as_simple_constant() {
                    return Some((ci.clone(), name, definition.get_type()));
                }
            }
        }
        None
    }
}
