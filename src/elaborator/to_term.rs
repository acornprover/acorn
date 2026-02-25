use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp};
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::Atom;
use crate::kernel::atom::AtomId;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
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

/// Elaborates an `AcornValue` into a kernel `Term`.
///
/// This is a term-level elaboration pass:
/// - registers referenced types/constants in the kernel tables
/// - lowers logical connectives to built-in logical atoms
/// - lowers `if` into builtin `ite`
/// - lowers `match` into datatype eliminator application (`Type.match`)
///
/// The result is intended to be logically lossless, not syntactically identical.
pub fn elaborate_value_to_term(
    kernel_context: &mut KernelContext,
    value: &AcornValue,
    ctype: NewConstantType,
    type_var_map: Option<&TypeVarMap>,
) -> Result<Term, String> {
    kernel_context
        .symbol_table
        .add_from(value, ctype, &mut kernel_context.type_store);

    let mut stack = vec![];
    elaborate_value_to_term_with_stack(kernel_context, value, type_var_map, &mut stack)
}

fn elaborate_value_to_term_with_stack(
    kernel_context: &mut KernelContext,
    value: &AcornValue,
    type_var_map: Option<&TypeVarMap>,
    stack: &mut Vec<Term>,
) -> Result<Term, String> {
    match value {
        AcornValue::Variable(i, var_type) => stack.get(*i as usize).cloned().ok_or_else(|| {
            format!(
                "variable {} (type {}) out of range in value elaboration (stack len {})",
                i,
                var_type,
                stack.len()
            )
        }),

        AcornValue::Constant(c) => {
            if c.params.is_empty() {
                let Some(symbol) = kernel_context.symbol_table.get_symbol(&c.name) else {
                    return Err(format!("constant {} not found in symbol table", c));
                };
                Ok(Term::atom(Atom::Symbol(symbol)))
            } else {
                kernel_context.symbol_table.term_from_instance_with_vars(
                    c,
                    &kernel_context.type_store,
                    type_var_map,
                )
            }
        }

        AcornValue::Application(app) => {
            let function_term = elaborate_value_to_term_with_stack(
                kernel_context,
                &app.function,
                type_var_map,
                stack,
            )?;
            let mut arg_terms = Vec::with_capacity(app.args.len());
            for arg in &app.args {
                arg_terms.push(elaborate_value_to_term_with_stack(
                    kernel_context,
                    arg,
                    type_var_map,
                    stack,
                )?);
            }
            Ok(function_term.apply(&arg_terms))
        }

        AcornValue::TypeApplication(app) => {
            let instantiated = app.instantiated_function();
            elaborate_value_to_term_with_stack(kernel_context, &instantiated, type_var_map, stack)
        }

        AcornValue::Lambda(arg_types, body) => elaborate_binder_to_term(
            kernel_context,
            arg_types,
            body,
            type_var_map,
            stack,
            BinderKind::Lambda,
        ),

        AcornValue::ForAll(arg_types, body) => elaborate_binder_to_term(
            kernel_context,
            arg_types,
            body,
            type_var_map,
            stack,
            BinderKind::ForAll,
        ),

        AcornValue::Exists(arg_types, body) => elaborate_binder_to_term(
            kernel_context,
            arg_types,
            body,
            type_var_map,
            stack,
            BinderKind::Exists,
        ),

        AcornValue::Binary(op, left, right) => {
            let left_term =
                elaborate_value_to_term_with_stack(kernel_context, left, type_var_map, stack)?;
            let right_term =
                elaborate_value_to_term_with_stack(kernel_context, right, type_var_map, stack)?;

            match op {
                BinaryOp::And => Ok(logical_head(Symbol::And).apply(&[left_term, right_term])),
                BinaryOp::Or => Ok(logical_head(Symbol::Or).apply(&[left_term, right_term])),
                BinaryOp::Implies => {
                    // Logically lossless sugar: (a -> b) = (not a) or b.
                    let not_left = logical_head(Symbol::Not).apply(&[left_term]);
                    Ok(logical_head(Symbol::Or).apply(&[not_left, right_term]))
                }
                BinaryOp::Equals => {
                    let eq_type =
                        elaborate_type_to_term(kernel_context, &left.get_type(), type_var_map);
                    Ok(logical_head(Symbol::Eq).apply(&[eq_type, left_term, right_term]))
                }
                BinaryOp::NotEquals => {
                    // Logically lossless sugar: (a != b) = not (a = b).
                    let eq_type =
                        elaborate_type_to_term(kernel_context, &left.get_type(), type_var_map);
                    let eq_term = logical_head(Symbol::Eq).apply(&[eq_type, left_term, right_term]);
                    Ok(logical_head(Symbol::Not).apply(&[eq_term]))
                }
            }
        }

        AcornValue::Not(subvalue) => {
            let sub_term =
                elaborate_value_to_term_with_stack(kernel_context, subvalue, type_var_map, stack)?;
            Ok(logical_head(Symbol::Not).apply(&[sub_term]))
        }

        AcornValue::Try(_, _) => {
            Err("try operator not yet implemented in term elaboration".to_string())
        }

        AcornValue::Bool(b) => {
            if *b {
                Ok(Term::new_true())
            } else {
                Ok(Term::new_false())
            }
        }

        AcornValue::IfThenElse(cond, then_value, else_value) => {
            let cond_term =
                elaborate_value_to_term_with_stack(kernel_context, cond, type_var_map, stack)?;
            let then_term = elaborate_value_to_term_with_stack(
                kernel_context,
                then_value,
                type_var_map,
                stack,
            )?;
            let else_term = elaborate_value_to_term_with_stack(
                kernel_context,
                else_value,
                type_var_map,
                stack,
            )?;
            let value_type =
                elaborate_type_to_term(kernel_context, &then_value.get_type(), type_var_map);
            Ok(logical_head(Symbol::Ite).apply(&[value_type, cond_term, then_term, else_term]))
        }

        AcornValue::Match(scrutinee, cases) => {
            lower_match_to_term(kernel_context, scrutinee, cases, type_var_map, stack)
        }
    }
}

#[derive(Clone, Copy)]
enum BinderKind {
    Lambda,
    ForAll,
    Exists,
}

fn elaborate_binder_to_term(
    kernel_context: &mut KernelContext,
    binder_types: &[AcornType],
    body: &AcornValue,
    type_var_map: Option<&TypeVarMap>,
    stack: &mut Vec<Term>,
    kind: BinderKind,
) -> Result<Term, String> {
    let binder_type_terms: Vec<Term> = binder_types
        .iter()
        .map(|t| elaborate_type_to_term(kernel_context, t, type_var_map))
        .collect();

    let num_new = binder_types.len();
    let old_len = stack.len();

    // Existing bound-variable references are one level deeper for each new binder.
    for existing in stack.iter_mut() {
        *existing = existing.shift_bound(0, num_new as i16);
    }

    // AcornValue variables are levels (outermost = 0). For the newly introduced binders:
    // first binder in this block becomes the outer one of the block.
    for j in 0..num_new {
        let bound = Term::atom(Atom::BoundVariable((num_new - 1 - j) as u16));
        stack.push(bound);
    }

    let body_term = elaborate_value_to_term_with_stack(kernel_context, body, type_var_map, stack)?;

    stack.truncate(old_len);
    for existing in stack.iter_mut() {
        *existing = existing.shift_bound(0, -(num_new as i16));
    }

    let wrapped = match kind {
        BinderKind::Lambda => Term::lambda_multi(binder_type_terms, body_term),
        BinderKind::ForAll => Term::forall_multi(binder_type_terms, body_term),
        BinderKind::Exists => Term::exists_multi(binder_type_terms, body_term),
    };

    Ok(wrapped)
}

fn lower_match_to_term(
    kernel_context: &mut KernelContext,
    scrutinee: &AcornValue,
    cases: &[(Vec<AcornType>, AcornValue, AcornValue)],
    type_var_map: Option<&TypeVarMap>,
    stack: &mut Vec<Term>,
) -> Result<Term, String> {
    let scrutinee_type = scrutinee.get_type();
    let (datatype, data_type_args) = match &scrutinee_type {
        AcornType::Data(datatype, type_args) => (datatype.clone(), type_args.clone()),
        _ => {
            return Err(format!(
                "match scrutinee must be a datatype, but got {}",
                scrutinee_type
            ))
        }
    };
    if cases.is_empty() {
        return Err("match must have at least one case".to_string());
    }

    let result_type = cases[0].2.get_type();
    for (_, _, case_result) in cases.iter().skip(1) {
        if case_result.get_type() != result_type {
            return Err("all match cases must have the same result type".to_string());
        }
    }

    let match_name = ConstantName::datatype_attr(datatype.module_id, datatype, "match");
    let Some(match_symbol) = kernel_context.symbol_table.get_symbol(&match_name) else {
        return Err(format!(
            "missing datatype match eliminator symbol: {}",
            match_name
        ));
    };

    let mut type_arg_terms: Vec<Term> = data_type_args
        .iter()
        .map(|t| elaborate_type_to_term(kernel_context, t, type_var_map))
        .collect();
    type_arg_terms.push(elaborate_type_to_term(
        kernel_context,
        &result_type,
        type_var_map,
    ));

    let scrutinee_term =
        elaborate_value_to_term_with_stack(kernel_context, scrutinee, type_var_map, stack)?;

    // We currently rely on case order from elaboration to match constructor order.
    let mut case_terms = vec![];
    for (case_binders, _pattern, case_result) in cases {
        case_terms.push(elaborate_binder_to_term(
            kernel_context,
            case_binders,
            case_result,
            type_var_map,
            stack,
            BinderKind::Lambda,
        )?);
    }

    let mut args = vec![scrutinee_term];
    args.extend(case_terms);

    let head = Term::atom(Atom::Symbol(match_symbol));
    Ok(head.apply(&type_arg_terms).apply(&args))
}

fn logical_head(symbol: Symbol) -> Term {
    Term::atom(Atom::Symbol(symbol))
}

#[cfg(test)]
mod tests {
    use crate::elaborator::acorn_type::{Datatype, Typeclass};
    use crate::elaborator::acorn_value::FunctionApplication;
    use crate::elaborator::names::ConstantName;
    use crate::kernel::atom::Atom;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::symbol_table::NewConstantType;
    use crate::module::ModuleId;
    use crate::normalizer::Normalizer;

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

    fn assert_term_roundtrip_stable(value: AcornValue) {
        let mut normalizer = Normalizer::new();
        let term = elaborate_value_to_term(
            normalizer.kernel_context_mut(),
            &value,
            NewConstantType::Local,
            None,
        )
        .expect("elaboration should succeed");
        let denormalized =
            normalizer.denormalize_term_with_context(&term, LocalContext::empty_ref(), false);
        let roundtripped = elaborate_value_to_term(
            normalizer.kernel_context_mut(),
            &denormalized,
            NewConstantType::Local,
            None,
        )
        .expect("re-elaboration should succeed");
        assert_eq!(term, roundtripped);
    }

    #[test]
    fn test_elaborate_value_to_term_logical_atoms_and_ite() {
        let mut kernel_context = KernelContext::new();
        let value = AcornValue::IfThenElse(
            Box::new(AcornValue::and(
                AcornValue::Bool(true),
                AcornValue::Bool(true),
            )),
            Box::new(AcornValue::equals(
                AcornValue::Bool(true),
                AcornValue::Bool(false),
            )),
            Box::new(AcornValue::not_equals(
                AcornValue::Bool(false),
                AcornValue::Bool(false),
            )),
        );
        let term =
            elaborate_value_to_term(&mut kernel_context, &value, NewConstantType::Local, None)
                .expect("value elaboration should succeed");

        let bool_type = Term::bool_type();
        let and_term =
            Term::atom(Atom::Symbol(Symbol::And)).apply(&[Term::new_true(), Term::new_true()]);
        let eq_term = Term::atom(Atom::Symbol(Symbol::Eq)).apply(&[
            bool_type.clone(),
            Term::new_true(),
            Term::new_false(),
        ]);
        let ne_term =
            Term::atom(Atom::Symbol(Symbol::Not)).apply(&[Term::atom(Atom::Symbol(Symbol::Eq))
                .apply(&[bool_type.clone(), Term::new_false(), Term::new_false()])]);
        let expected =
            Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[bool_type, and_term, eq_term, ne_term]);
        assert_eq!(term, expected);
    }

    #[test]
    fn test_elaborate_value_to_term_implies_is_not_or() {
        let mut kernel_context = KernelContext::new();
        let value = AcornValue::implies(AcornValue::Bool(true), AcornValue::Bool(false));
        let term =
            elaborate_value_to_term(&mut kernel_context, &value, NewConstantType::Local, None)
                .expect("value elaboration should succeed");

        let expected = Term::atom(Atom::Symbol(Symbol::Or)).apply(&[
            Term::atom(Atom::Symbol(Symbol::Not)).apply(&[Term::new_true()]),
            Term::new_false(),
        ]);
        assert_eq!(term, expected);
    }

    #[test]
    fn test_elaborate_value_to_term_binders_use_bound_variables() {
        let mut kernel_context = KernelContext::new();
        let bool_ty = AcornType::Bool;
        let value = AcornValue::lambda(
            vec![bool_ty.clone()],
            AcornValue::forall(
                vec![bool_ty.clone()],
                AcornValue::exists(
                    vec![bool_ty.clone()],
                    AcornValue::and(
                        AcornValue::Variable(0, bool_ty.clone()),
                        AcornValue::Variable(2, bool_ty),
                    ),
                ),
            ),
        );

        let term =
            elaborate_value_to_term(&mut kernel_context, &value, NewConstantType::Local, None)
                .expect("value elaboration should succeed");

        let expected = Term::lambda(
            Term::bool_type(),
            Term::forall(
                Term::bool_type(),
                Term::exists(
                    Term::bool_type(),
                    Term::atom(Atom::Symbol(Symbol::And)).apply(&[
                        Term::atom(Atom::BoundVariable(2)),
                        Term::atom(Atom::BoundVariable(0)),
                    ]),
                ),
            ),
        );
        assert_eq!(term, expected);
    }

    #[test]
    fn test_elaborate_value_to_term_match_lowers_to_match_eliminator() {
        let mut kernel_context = KernelContext::new();
        let nat = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let nat_type = AcornType::Data(nat.clone(), vec![]);
        kernel_context.type_store.add_type(&nat_type);
        let nat_id = kernel_context
            .type_store
            .get_datatype_id(&nat)
            .expect("nat type id should exist");

        let zero_name = ConstantName::datatype_attr(ModuleId(0), nat.clone(), "zero");
        let succ_name = ConstantName::datatype_attr(ModuleId(0), nat.clone(), "succ");
        let match_name = ConstantName::datatype_attr(ModuleId(0), nat, "match");

        let nat_term = Term::ground_type(nat_id);
        kernel_context.symbol_table.add_constant(
            zero_name.clone(),
            NewConstantType::Global,
            nat_term.clone(),
        );
        kernel_context.symbol_table.add_constant(
            succ_name.clone(),
            NewConstantType::Global,
            Term::pi(nat_term.clone(), nat_term.clone()),
        );
        // Monomorphic stand-in shape: Pi(Type, Nat -> Nat -> (Nat -> Nat) -> Nat)
        // (sufficient for term elaboration shape checks in this test).
        kernel_context.symbol_table.add_constant(
            match_name.clone(),
            NewConstantType::Global,
            Term::pi(
                Term::type_sort(),
                Term::pi(
                    nat_term.clone(),
                    Term::pi(
                        nat_term.clone(),
                        Term::pi(
                            Term::pi(nat_term.clone(), nat_term.clone()),
                            nat_term.clone(),
                        ),
                    ),
                ),
            ),
        );

        let zero = AcornValue::constant(
            zero_name.clone(),
            vec![],
            nat_type.clone(),
            nat_type.clone(),
            vec![],
        );
        let succ = AcornValue::constant(
            succ_name.clone(),
            vec![],
            AcornType::functional(vec![nat_type.clone()], nat_type.clone()),
            AcornType::functional(vec![nat_type.clone()], nat_type.clone()),
            vec![],
        );

        let match_value = AcornValue::Match(
            Box::new(zero.clone()),
            vec![
                (vec![], zero.clone(), zero.clone()),
                (
                    vec![nat_type.clone()],
                    AcornValue::Application(FunctionApplication {
                        function: Box::new(succ),
                        args: vec![AcornValue::Variable(0, nat_type.clone())],
                    }),
                    AcornValue::Variable(0, nat_type.clone()),
                ),
            ],
        );

        let term = elaborate_value_to_term(
            &mut kernel_context,
            &match_value,
            NewConstantType::Local,
            None,
        )
        .expect("match elaboration should succeed");

        let match_symbol = kernel_context
            .symbol_table
            .get_symbol(&match_name)
            .expect("match symbol should exist");
        let zero_symbol = kernel_context
            .symbol_table
            .get_symbol(&zero_name)
            .expect("zero symbol should exist");

        let expected = Term::atom(Atom::Symbol(match_symbol)).apply(&[
            nat_term.clone(),
            Term::atom(Atom::Symbol(zero_symbol)),
            Term::atom(Atom::Symbol(zero_symbol)),
            Term::lambda(nat_term, Term::atom(Atom::BoundVariable(0))),
        ]);
        assert_eq!(term, expected);
    }

    #[test]
    fn test_parity_roundtrip_for_logic_binders_and_match() {
        // and/or/eq/not/implies/ite
        assert_term_roundtrip_stable(AcornValue::IfThenElse(
            Box::new(AcornValue::implies(
                AcornValue::Bool(true),
                AcornValue::Not(Box::new(AcornValue::Bool(false))),
            )),
            Box::new(AcornValue::equals(
                AcornValue::Bool(true),
                AcornValue::Bool(true),
            )),
            Box::new(AcornValue::or(
                AcornValue::Bool(false),
                AcornValue::Bool(true),
            )),
        ));

        // lambda / forall / exists with variable levels
        let bool_ty = AcornType::Bool;
        assert_term_roundtrip_stable(AcornValue::forall(
            vec![bool_ty.clone()],
            AcornValue::exists(
                vec![bool_ty.clone()],
                AcornValue::lambda(vec![bool_ty.clone()], AcornValue::Variable(1, bool_ty)),
            ),
        ));
    }
}
