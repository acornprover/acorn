use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::kernel::atom::AtomId;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::term::Term;

/// Mapping from elaborator type-parameter names to kernel type variables.
/// The tuple is `(variable_id, kind_term)`, where kind_term is usually `Type` or a typeclass.
pub type TypeVarMap = HashMap<String, (AtomId, Term)>;

/// Builds the kernel type-variable map for a list of type parameters.
///
/// The map uses declaration order:
/// - first type parameter gets id 0
/// - second gets id 1
/// - ...
///
/// If a type parameter has a typeclass constraint, the kind term is the typeclass;
/// otherwise the kind term is `Type`.
pub fn build_type_var_map(
    kernel_context: &mut KernelContext,
    type_params: &[TypeParam],
) -> TypeVarMap {
    type_params
        .iter()
        .enumerate()
        .map(|(i, param)| {
            let kind = if let Some(typeclass) = &param.typeclass {
                let typeclass_id = kernel_context.type_store.add_typeclass(typeclass);
                Term::typeclass(typeclass_id)
            } else {
                Term::type_sort()
            };
            (param.name.clone(), (i as AtomId, kind))
        })
        .collect()
}

/// Elaborates an `AcornType` into a kernel `Term`.
///
/// This handles:
/// - registering any needed ground/typeclass IDs in `TypeStore`
/// - converting generic type parameters via `type_var_map` into `FreeVariable`s
pub fn elaborate_type_to_term(
    kernel_context: &mut KernelContext,
    acorn_type: &AcornType,
    type_var_map: Option<&TypeVarMap>,
) -> Term {
    register_typeclasses(kernel_context, acorn_type);
    kernel_context.type_store.add_type(acorn_type);
    kernel_context
        .type_store
        .to_type_term_with_vars(acorn_type, type_var_map)
}

fn register_typeclasses(kernel_context: &mut KernelContext, acorn_type: &AcornType) {
    match acorn_type {
        AcornType::Function(function_type) => {
            for arg_type in &function_type.arg_types {
                register_typeclasses(kernel_context, arg_type);
            }
            register_typeclasses(kernel_context, &function_type.return_type);
        }
        AcornType::Data(_, params) => {
            for param in params {
                register_typeclasses(kernel_context, param);
            }
        }
        AcornType::Variable(type_param) | AcornType::Arbitrary(type_param) => {
            if let Some(typeclass) = &type_param.typeclass {
                kernel_context.type_store.add_typeclass(typeclass);
            }
        }
        AcornType::TypeclassConstraint(typeclass) => {
            kernel_context.type_store.add_typeclass(typeclass);
        }
        AcornType::Bool | AcornType::Empty | AcornType::Type0 => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::elaborator::acorn_type::{Datatype, Typeclass};
    use crate::kernel::atom::Atom;
    use crate::module::ModuleId;

    use super::*;

    #[test]
    fn test_build_type_var_map_respects_constraints() {
        let mut kernel_context = KernelContext::new();
        let eq = Typeclass {
            module_id: ModuleId(0),
            name: "Eq".to_string(),
        };
        let params = vec![
            TypeParam {
                name: "T".to_string(),
                typeclass: Some(eq.clone()),
            },
            TypeParam {
                name: "U".to_string(),
                typeclass: None,
            },
        ];

        let map = build_type_var_map(&mut kernel_context, &params);

        let (t_id, t_kind) = map.get("T").expect("missing T");
        assert_eq!(*t_id, 0);
        assert!(matches!(
            t_kind.as_ref().get_head_atom(),
            Atom::Symbol(crate::kernel::symbol::Symbol::Typeclass(_))
        ));

        let (u_id, u_kind) = map.get("U").expect("missing U");
        assert_eq!(*u_id, 1);
        assert!(u_kind.as_ref().is_type0());
    }

    #[test]
    fn test_elaborate_type_to_term_generic_function() {
        let mut kernel_context = KernelContext::new();
        let params = vec![
            TypeParam {
                name: "T".to_string(),
                typeclass: None,
            },
            TypeParam {
                name: "U".to_string(),
                typeclass: None,
            },
        ];
        let map = build_type_var_map(&mut kernel_context, &params);

        let t = AcornType::Variable(params[0].clone());
        let u = AcornType::Variable(params[1].clone());
        let acorn_type = AcornType::functional(vec![t.clone(), u.clone()], t);
        let term = elaborate_type_to_term(&mut kernel_context, &acorn_type, Some(&map));

        let expected = Term::pi(
            Term::atom(Atom::FreeVariable(0)),
            Term::pi(
                Term::atom(Atom::FreeVariable(1)),
                Term::atom(Atom::FreeVariable(0)),
            ),
        );
        assert_eq!(term, expected);
    }

    #[test]
    fn test_elaborate_type_to_term_registers_parameterized_datatype() {
        let mut kernel_context = KernelContext::new();
        let list = Datatype {
            module_id: ModuleId(0),
            name: "List".to_string(),
        };
        let acorn_type = AcornType::Data(list.clone(), vec![AcornType::Bool]);
        let term = elaborate_type_to_term(&mut kernel_context, &acorn_type, None);

        let datatype_id = kernel_context
            .type_store
            .get_datatype_id(&list)
            .expect("List should be registered");
        let expected =
            Term::type_application(Term::ground_type(datatype_id), vec![Term::bool_type()]);
        assert_eq!(term, expected);
    }

    #[test]
    fn test_elaborate_type_to_term_typeclass_constraint() {
        let mut kernel_context = KernelContext::new();
        let monoid = Typeclass {
            module_id: ModuleId(0),
            name: "Monoid".to_string(),
        };
        let acorn_type = AcornType::TypeclassConstraint(monoid);
        let term = elaborate_type_to_term(&mut kernel_context, &acorn_type, None);

        assert!(matches!(
            term.as_ref().get_head_atom(),
            Atom::Symbol(crate::kernel::symbol::Symbol::Typeclass(_))
        ));
    }
}
