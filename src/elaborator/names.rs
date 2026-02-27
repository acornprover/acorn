use std::fmt;

use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
use crate::kernel::atom::AtomId;
use crate::module::ModuleId;

/// An instance name is something like Ring.add<Int>.
/// This can be defined directly, although it should be expressed in
/// parameterized form when it's a value.
#[derive(Hash, Debug, Eq, PartialEq, Clone, PartialOrd, Ord)]
pub struct InstanceName {
    /// Like "Ring", in Ring.add<Int>.
    pub typeclass: Typeclass,

    /// Like "add", in Ring.add<Int>.
    pub attribute: String,

    /// Like "Int", in Ring.add<Int>.
    pub datatype: Datatype,
}

impl InstanceName {
    /// Converts the instance name to a typeclass attribute name.
    /// This is used for enabling recursion in instance function definitions.
    pub fn to_typeclass_attribute(&self) -> ConstantName {
        ConstantName::typeclass_attr(
            self.typeclass.module_id,
            self.typeclass.clone(),
            &self.attribute,
        )
    }
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
    /// Fields are:
    /// - defining module id: where this constant was defined
    /// - receiver datatype: the type on the left side of `.` in `Type.attr`
    /// - attribute name
    ///
    /// The defining module is not always the receiver datatype's module.
    DatatypeAttribute(ModuleId, Datatype, String),

    /// An attribute of a specifically parameterized datatype (e.g., `Set[Color].has_red`).
    /// Fields are:
    /// - defining module id
    /// - receiver datatype
    /// - concrete type arguments used for specialization
    /// - attribute name
    ///
    /// As with `DatatypeAttribute`, defining module and receiver module can differ.
    SpecificDatatypeAttribute(ModuleId, Datatype, Vec<AcornType>, String),

    /// An attribute of a typeclass.
    /// Fields are:
    /// - defining module id
    /// - receiver typeclass
    /// - attribute name
    ///
    /// The defining module is not always the receiver typeclass's module.
    TypeclassAttribute(ModuleId, Typeclass, String),

    /// A name for a constant that is not an attribute.
    Unqualified(ModuleId, String),

    /// A synthetic constant, created by the kernel_context to simplify expressions.
    /// The ModuleId identifies which module's normalization created this synthetic.
    Synthetic(ModuleId, AtomId),
}

impl ConstantName {
    pub fn datatype_attr(
        defining_module: ModuleId,
        datatype: Datatype,
        attr: &str,
    ) -> ConstantName {
        ConstantName::DatatypeAttribute(defining_module, datatype, attr.to_string())
    }

    pub fn datatype_specific_attr(
        defining_module: ModuleId,
        datatype: Datatype,
        types: Vec<AcornType>,
        attr: &str,
    ) -> ConstantName {
        ConstantName::SpecificDatatypeAttribute(defining_module, datatype, types, attr.to_string())
    }

    pub fn typeclass_attr(defining_module: ModuleId, tc: Typeclass, attr: &str) -> ConstantName {
        ConstantName::TypeclassAttribute(defining_module, tc, attr.to_string())
    }

    pub fn unqualified(module_id: ModuleId, name: &str) -> ConstantName {
        ConstantName::Unqualified(module_id, name.to_string())
    }

    /// Returns attribute receiver information as `(receiver_module_id, receiver_name, attr_name)`.
    ///
    /// This is for receiver-side behavior (inheritance, member syntax, etc.), not for locating
    /// the module that defined the constant.
    pub fn as_attribute(&self) -> Option<(ModuleId, &str, &str)> {
        match self {
            ConstantName::DatatypeAttribute(_, datatype, attr) => {
                Some((datatype.module_id, &datatype.name, attr))
            }
            ConstantName::SpecificDatatypeAttribute(_, datatype, _types, attr) => {
                Some((datatype.module_id, &datatype.name, attr))
            }
            ConstantName::TypeclassAttribute(_, tc, attr) => Some((tc.module_id, &tc.name, attr)),
            ConstantName::Unqualified(..) => None,
            ConstantName::Synthetic(..) => None,
        }
    }

    pub fn to_defined(&self) -> DefinedName {
        DefinedName::Constant(self.clone())
    }

    pub fn is_typeclass_attr(&self) -> bool {
        matches!(self, ConstantName::TypeclassAttribute(..))
    }

    pub fn is_synthetic(&self) -> bool {
        matches!(self, ConstantName::Synthetic(..))
    }

    pub fn synthetic_id(&self) -> Option<(ModuleId, AtomId)> {
        match self {
            ConstantName::Synthetic(m, id) => Some((*m, *id)),
            _ => None,
        }
    }

    /// Returns the defining module id for this constant.
    ///
    /// For datatype/typeclass attributes, this can differ from `as_attribute().0`, which is the
    /// receiver's module id.
    pub fn module_id(&self) -> ModuleId {
        match self {
            ConstantName::DatatypeAttribute(module_id, _, _) => *module_id,
            ConstantName::SpecificDatatypeAttribute(module_id, _, _, _) => *module_id,
            ConstantName::TypeclassAttribute(module_id, _, _) => *module_id,
            ConstantName::Unqualified(module_id, _) => *module_id,
            ConstantName::Synthetic(module_id, _) => *module_id,
        }
    }

    pub fn is_attribute_of(&self, datatype: &Datatype) -> bool {
        match self {
            ConstantName::DatatypeAttribute(_, datatype_attr, _) => datatype_attr == datatype,
            ConstantName::SpecificDatatypeAttribute(_, datatype_attr, _, _) => {
                datatype_attr == datatype
            }
            _ => false,
        }
    }
}

impl fmt::Display for ConstantName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ConstantName::DatatypeAttribute(_, datatype, attr) => {
                write!(f, "{}.{}", datatype.name, attr)
            }
            ConstantName::SpecificDatatypeAttribute(_, datatype, types, attr) => {
                write!(f, "{}[", datatype.name)?;
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, "].{}", attr)
            }
            ConstantName::TypeclassAttribute(_, tc, attr) => {
                write!(f, "{}.{}", tc.name, attr)
            }
            ConstantName::Unqualified(_, name) => write!(f, "{}", name),
            ConstantName::Synthetic(m, i) => write!(f, "s{}_{}", m.0, i),
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
        Self::datatype_attr_defined(datatype.module_id, datatype, attr)
    }

    pub fn datatype_attr_defined(
        defining_module: ModuleId,
        datatype: &Datatype,
        attr: &str,
    ) -> DefinedName {
        DefinedName::Constant(ConstantName::datatype_attr(
            defining_module,
            datatype.clone(),
            attr,
        ))
    }

    pub fn datatype_specific_attr(
        datatype: Datatype,
        types: &[AcornType],
        attr: &str,
    ) -> DefinedName {
        Self::datatype_specific_attr_defined(datatype.module_id, datatype, types, attr)
    }

    pub fn datatype_specific_attr_defined(
        defining_module: ModuleId,
        datatype: Datatype,
        types: &[AcornType],
        attr: &str,
    ) -> DefinedName {
        DefinedName::Constant(ConstantName::datatype_specific_attr(
            defining_module,
            datatype,
            types.to_vec(),
            attr,
        ))
    }

    pub fn typeclass_attr(tc: &Typeclass, attr: &str) -> DefinedName {
        Self::typeclass_attr_defined(tc.module_id, tc, attr)
    }

    pub fn typeclass_attr_defined(
        defining_module: ModuleId,
        tc: &Typeclass,
        attr: &str,
    ) -> DefinedName {
        DefinedName::Constant(ConstantName::typeclass_attr(
            defining_module,
            tc.clone(),
            attr,
        ))
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
        matches!(self, DefinedName::Instance(..))
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

    /// Returns a ConstantName that can be used for enabling recursion.
    /// For constants, this is the constant name itself.
    /// For instance functions, we use an unqualified name with the attribute name,
    /// which allows recursion via direct function call syntax (e.g., `id(pred)`).
    pub fn recursion_name(&self) -> Option<ConstantName> {
        match self {
            DefinedName::Constant(name) => Some(name.clone()),
            DefinedName::Instance(inst) => {
                // Use an unqualified name so recursive calls like `id(pred)` will find it.
                // We can't use TypeclassAttribute because that would overwrite and then
                // remove the existing typeclass attribute definition.
                Some(ConstantName::Unqualified(
                    inst.datatype.module_id,
                    inst.attribute.clone(),
                ))
            }
        }
    }

    pub fn is_typeclass_attr(&self) -> bool {
        match self {
            DefinedName::Constant(const_name) => const_name.is_typeclass_attr(),
            DefinedName::Instance(_) => false,
        }
    }
}
