use std::fmt;

use crate::acorn_type::{Datatype, Typeclass};
use crate::atom::AtomId;
use crate::module::ModuleId;

/// An instance name is something like Ring.add<Int>.
/// This can be defined directly, although it should be expressed in
/// parametrized form when it's a value.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub struct InstanceName {
    /// Like "Ring", in Ring.add<Int>.
    pub typeclass: Typeclass,

    /// Like "add", in Ring.add<Int>.
    pub attribute: String,

    /// Like "Int", in Ring.add<Int>.
    pub datatype: Datatype,
}

impl fmt::Display for InstanceName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}.{}[{}]",
            self.typeclass.name, self.attribute, self.datatype.name
        )
    }
}

/// The ConstantName provides an identifier for a constant.
/// It is unique within a given scope. It is not necessarily globally unique, because you
/// could have two different modules mix the same attribute into a datatype or typeclass, or
/// you could have a stack variable with the same name in two different places.
#[derive(Debug, Eq, PartialEq, Clone, Hash, PartialOrd, Ord)]
pub enum ConstantName {
    /// An attribute of a datatype.
    DatatypeAttribute(Datatype, String),

    /// An attribute of a typeclass.
    TypeclassAttribute(Typeclass, String),

    /// A name for a constant that is not an attribute.
    Unqualified(ModuleId, String),

    /// A synthetic constant, created by the normalizer to simplify expressions.
    Synthetic(AtomId),
}

impl ConstantName {
    pub fn datatype_attr(datatype: Datatype, attr: &str) -> ConstantName {
        ConstantName::DatatypeAttribute(datatype, attr.to_string())
    }

    pub fn typeclass_attr(tc: Typeclass, attr: &str) -> ConstantName {
        ConstantName::TypeclassAttribute(tc, attr.to_string())
    }

    pub fn unqualified(module_id: ModuleId, name: &str) -> ConstantName {
        ConstantName::Unqualified(module_id, name.to_string())
    }

    pub fn as_attribute(&self) -> Option<(ModuleId, &str, &str)> {
        match self {
            ConstantName::DatatypeAttribute(datatype, attr) => {
                Some((datatype.module_id, &datatype.name, attr))
            }
            ConstantName::TypeclassAttribute(tc, attr) => Some((tc.module_id, &tc.name, attr)),
            ConstantName::Unqualified(..) => None,
            ConstantName::Synthetic(_) => None,
        }
    }

    pub fn to_defined(&self) -> DefinedName {
        DefinedName::Constant(self.clone())
    }

    pub fn is_typeclass_attr(&self) -> bool {
        match self {
            ConstantName::TypeclassAttribute(..) => true,
            _ => false,
        }
    }

    pub fn is_synthetic(&self) -> bool {
        match self {
            ConstantName::Synthetic(_) => true,
            _ => false,
        }
    }

    pub fn synthetic_id(&self) -> Option<AtomId> {
        match self {
            ConstantName::Synthetic(id) => Some(*id),
            _ => None,
        }
    }

    pub fn module_id(&self) -> ModuleId {
        match self {
            ConstantName::DatatypeAttribute(datatype, _) => datatype.module_id,
            ConstantName::TypeclassAttribute(tc, _) => tc.module_id,
            ConstantName::Unqualified(module_id, _) => *module_id,
            ConstantName::Synthetic(_) => panic!("synthetic constants do not have a module id"),
        }
    }

    pub fn is_attribute_of(&self, datatype: &Datatype) -> bool {
        match self {
            ConstantName::DatatypeAttribute(datatype_attr, _) => datatype_attr == datatype,
            _ => false,
        }
    }
}

impl fmt::Display for ConstantName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ConstantName::DatatypeAttribute(datatype, attr) => {
                write!(f, "{}.{}", datatype.name, attr)
            }
            ConstantName::TypeclassAttribute(tc, attr) => {
                write!(f, "{}.{}", tc.name, attr)
            }
            ConstantName::Unqualified(_, name) => write!(f, "{}", name),
            ConstantName::Synthetic(i) => write!(f, "s{}", i),
        }
    }
}

/// The DefinedName describes how a constant was defined.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub enum DefinedName {
    /// A regular constant name.
    Constant(ConstantName),

    /// An attribute defined via an instance statement.
    Instance(InstanceName),
}

impl fmt::Display for DefinedName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DefinedName::Constant(name) => write!(f, "{}", name),
            DefinedName::Instance(name) => write!(f, "{}", name),
        }
    }
}

impl DefinedName {
    pub fn unqualified(module_id: ModuleId, name: &str) -> DefinedName {
        DefinedName::Constant(ConstantName::unqualified(module_id, name))
    }

    pub fn datatype_attr(datatype: &Datatype, attr: &str) -> DefinedName {
        DefinedName::Constant(ConstantName::datatype_attr(datatype.clone(), attr))
    }

    pub fn typeclass_attr(tc: &Typeclass, attr: &str) -> DefinedName {
        DefinedName::Constant(ConstantName::typeclass_attr(tc.clone(), attr))
    }

    pub fn instance(tc: Typeclass, attr: &str, datatype: Datatype) -> DefinedName {
        let inst = InstanceName {
            typeclass: tc,
            attribute: attr.to_string(),
            datatype,
        };
        DefinedName::Instance(inst)
    }

    pub fn is_qualified(&self) -> bool {
        match self {
            DefinedName::Constant(ConstantName::Unqualified(..)) => false,
            _ => true,
        }
    }

    pub fn is_instance(&self) -> bool {
        match self {
            DefinedName::Instance(..) => true,
            _ => false,
        }
    }

    pub fn as_attribute(&self) -> Option<(&str, &str)> {
        match self {
            DefinedName::Constant(c) => {
                let (_, entity, attr) = c.as_attribute()?;
                Some((entity, attr))
            }
            DefinedName::Instance(inst) => Some((&inst.typeclass.name, &inst.attribute)),
        }
    }

    pub fn matches_instance(&self, typeclass: &Typeclass, datatype: &Datatype) -> bool {
        match self {
            DefinedName::Instance(inst) => {
                inst.typeclass == *typeclass && inst.datatype == *datatype
            }
            DefinedName::Constant(_) => false,
        }
    }

    pub fn as_constant(&self) -> Option<&ConstantName> {
        match self {
            DefinedName::Constant(name) => Some(name),
            DefinedName::Instance(_) => None,
        }
    }

    pub fn is_typeclass_attr(&self) -> bool {
        match self {
            DefinedName::Constant(const_name) => const_name.is_typeclass_attr(),
            DefinedName::Instance(_) => false,
        }
    }
}
