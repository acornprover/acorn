use super::*;
use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::module::ModuleId;

#[test]
fn test_replace_head_variable_with_compound_term() {
    let term = Term::parse("x0(x1)");
    let replacement = Term::parse("g0(c0)");

    let result = term.replace_variable(0, &replacement);

    let head = result.get_head_atom();
    assert!(matches!(
        head,
        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0))
    ));

    let args: Vec<_> = result.iter_args().collect();
    assert_eq!(args.len(), 2, "Expected 2 args, got {}", args.len());

    let arg0_head = args[0].get_head_atom();
    assert!(matches!(arg0_head, Atom::Symbol(Symbol::ScopedConstant(0))));

    let arg1_head = args[1].get_head_atom();
    assert!(matches!(arg1_head, Atom::FreeVariable(1)));
}

#[test]
fn test_replace_head_variable_simple() {
    let term = Term::parse("x0(x1)");
    let replacement = Term::parse("c0");

    let result = term.replace_variable(0, &replacement);

    let head = result.get_head_atom();
    assert!(matches!(head, Atom::Symbol(Symbol::ScopedConstant(0))));

    let args: Vec<_> = result.iter_args().collect();
    assert_eq!(args.len(), 1);
    assert!(matches!(args[0].get_head_atom(), Atom::FreeVariable(1)));
}

#[test]
fn test_replace_non_head_variable_with_compound() {
    let term = Term::parse("c0(x0)");
    let replacement = Term::parse("g0(c1)");

    let result = term.replace_variable(0, &replacement);

    let head = result.get_head_atom();
    assert!(matches!(head, Atom::Symbol(Symbol::ScopedConstant(0))));

    let args: Vec<_> = result.iter_args().collect();
    assert_eq!(args.len(), 1);

    let arg = &args[0];
    let arg_head = arg.get_head_atom();
    assert!(matches!(
        arg_head,
        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0))
    ));
}

#[test]
fn test_nested_term_comparison() {
    let term1 = Term::parse("c0(c1(c2))");
    let term2 = Term::parse("c0(c1(c3))");

    let _ = term1.extended_kbo_cmp(&term2);
}

#[test]
fn test_checked_type_rejects_wrong_argument_type() {
    let mut kctx = KernelContext::new();
    kctx.parse_datatype("Foo");
    kctx.parse_datatype("Bar");
    kctx.parse_constant("g0", "Foo -> Bool");
    kctx.parse_constant("c0", "Bar");

    let term = kctx.parse_term("g0(c0)");
    let error = term
        .checked_type_with_context(LocalContext::empty_ref(), &kctx)
        .expect_err("wrong argument type should be rejected");
    assert!(
        error.contains("Argument c0 has type") && error.contains("but expected"),
        "unexpected error: {}",
        error
    );
}

#[test]
fn test_iter_args_on_nested_term() {
    let term = Term::parse("c0(c1(c2), c3)");

    let args: Vec<_> = term.iter_args().collect();
    assert_eq!(args.len(), 2);

    for arg in &args {
        let _ = arg.get_head_atom();
    }
}

#[test]
fn test_new_term_format() {
    let term = Term::parse("c0(c1)");
    assert!(
        matches!(term.components()[0], TermComponent::Application { .. }),
        "Non-atomic term should start with Application. Got: {:?}",
        term.components()
    );

    let atomic = Term::parse("c0");
    assert!(
        matches!(atomic.components()[0], TermComponent::Atom(_)),
        "Atomic term should start with Atom"
    );

    let nested = Term::parse("c0(c1(c2), c3)");
    assert!(
        matches!(nested.components()[0], TermComponent::Application { .. }),
        "Nested term should start with Application"
    );
    assert_eq!(nested.num_args(), 2);

    let term2 = Term::parse("c0(c1, c2)");
    if let Decomposition::Application(func, arg) = term2.as_ref().decompose() {
        assert_eq!(format!("{}", func), "c0(c1)");
        assert_eq!(format!("{}", arg), "c2");
    } else {
        panic!("Expected Application decomposition");
    }
}

#[test]
fn test_bound_variable_parsing() {
    let b0 = Term::parse("b0");
    assert!(matches!(b0.get_head_atom(), Atom::BoundVariable(0)));

    let b5 = Term::parse("b5");
    assert!(matches!(b5.get_head_atom(), Atom::BoundVariable(5)));

    let term = Term::parse("c0(b0, b1)");
    assert!(term.has_bound_variable());
    assert!(!term.has_free_variable());
}

#[test]
fn test_lambda_decomposition_and_display() {
    let lambda = Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0)));
    assert!(lambda.as_ref().is_lambda());

    let (input, body) = lambda
        .as_ref()
        .split_lambda()
        .expect("expected lambda split");
    assert_eq!(format!("{}", input), "Bool");
    assert_eq!(format!("{}", body), "b0");
    assert_eq!(format!("{}", lambda), "lambda(Bool => b0)");
}

#[test]
fn test_quantifier_decomposition_and_display() {
    let forall = Term::forall(Term::bool_type(), Term::atom(Atom::BoundVariable(0)));
    assert!(forall.as_ref().is_forall());
    let (forall_input, forall_body) = forall
        .as_ref()
        .split_forall()
        .expect("expected forall split");
    assert_eq!(format!("{}", forall_input), "Bool");
    assert_eq!(format!("{}", forall_body), "b0");
    assert_eq!(format!("{}", forall), "forall(Bool => b0)");

    let exists = Term::exists(Term::bool_type(), Term::atom(Atom::BoundVariable(0)));
    assert!(exists.as_ref().is_exists());
    let (exists_input, exists_body) = exists
        .as_ref()
        .split_exists()
        .expect("expected exists split");
    assert_eq!(format!("{}", exists_input), "Bool");
    assert_eq!(format!("{}", exists_body), "b0");
    assert_eq!(format!("{}", exists), "exists(Bool => b0)");
}

#[test]
fn test_substitute_bound_simple() {
    let term = Term::parse("b0");
    let replacement = Term::parse("c0");
    let result = term.substitute_bound(0, &replacement);
    assert_eq!(format!("{}", result), "c0");
}

#[test]
fn test_substitute_bound_in_application() {
    let term = Term::parse("c0(b0, b1)");
    let replacement = Term::parse("c1");
    let result = term.substitute_bound(0, &replacement);
    assert_eq!(format!("{}", result), "c0(c1, b1)");

    let result2 = term.substitute_bound(1, &replacement);
    assert_eq!(format!("{}", result2), "c0(b0, c1)");
}

#[test]
fn test_substitute_bound_in_lambda_respects_binder() {
    let lambda = Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0)));
    let replacement = Term::parse("c0");
    let result = lambda.substitute_bound(0, &replacement);
    assert_eq!(format!("{}", result), "lambda(Bool => b0)");

    let lambda_outer = Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(1)));
    let result_outer = lambda_outer.substitute_bound(0, &replacement);
    assert_eq!(format!("{}", result_outer), "lambda(Bool => c0)");
}

#[test]
fn test_substitute_bound_in_quantifier_respects_binder() {
    let forall = Term::forall(Term::bool_type(), Term::atom(Atom::BoundVariable(0)));
    let replacement = Term::parse("c0");
    let result = forall.substitute_bound(0, &replacement);
    assert_eq!(format!("{}", result), "forall(Bool => b0)");

    let forall_outer = Term::forall(Term::bool_type(), Term::atom(Atom::BoundVariable(1)));
    let result_outer = forall_outer.substitute_bound(0, &replacement);
    assert_eq!(format!("{}", result_outer), "forall(Bool => c0)");
}

#[test]
fn test_shift_bound_simple() {
    let term = Term::parse("b0");
    let result = term.shift_bound(0, 1);
    assert_eq!(format!("{}", result), "b1");

    let term2 = Term::parse("b2");
    let result2 = term2.shift_bound(0, -1);
    assert_eq!(format!("{}", result2), "b1");
}

#[test]
fn test_shift_bound_with_cutoff() {
    let term = Term::parse("b0");
    let result = term.shift_bound(1, 1);
    assert_eq!(format!("{}", result), "b0");

    let term2 = Term::parse("b1");
    let result2 = term2.shift_bound(1, 1);
    assert_eq!(format!("{}", result2), "b2");
}

#[test]
fn test_shift_bound_in_compound() {
    let term = Term::parse("c0(b0, b1)");
    let result = term.shift_bound(0, 1);
    assert_eq!(format!("{}", result), "c0(b1, b2)");
}

#[test]
fn test_has_free_and_bound_variable() {
    let free_only = Term::parse("c0(x0, x1)");
    assert!(free_only.has_free_variable());
    assert!(!free_only.has_bound_variable());

    let bound_only = Term::parse("c0(b0, b1)");
    assert!(!bound_only.has_free_variable());
    assert!(bound_only.has_bound_variable());

    let both = Term::parse("c0(x0, b0)");
    assert!(both.has_free_variable());
    assert!(both.has_bound_variable());

    let neither = Term::parse("c0(c1)");
    assert!(!neither.has_free_variable());
    assert!(!neither.has_bound_variable());
}

#[test]
fn test_polymorphic_type_application() {
    let correct_type = Term::pi(Term::type_sort(), Term::atom(Atom::BoundVariable(0)));
    let concrete_type = Term::parse("c0");

    let result = correct_type.type_apply_with_arg(&concrete_type);
    assert!(result.is_some());
    assert_eq!(
        format!("{}", result.unwrap()),
        "c0",
        "Applying Pi(TypeSort, b0) to c0 should give c0"
    );
}

#[test]
fn test_free_variable_not_substituted_in_type_apply() {
    let pi_with_free = Term::pi(Term::type_sort(), Term::atom(Atom::FreeVariable(0)));
    let concrete_type = Term::parse("c0");

    let result = pi_with_free.type_apply_with_arg(&concrete_type);
    assert!(result.is_some());
    assert_eq!(
        format!("{}", result.unwrap()),
        "x0",
        "FreeVariables are not substituted by type_apply_with_arg"
    );
}

#[test]
fn test_checked_type_with_context_rejects_invalid_typeclass_type_arg() {
    let mut kctx = KernelContext::new();

    let arf = Typeclass {
        module_id: ModuleId(0),
        name: "Arf".to_string(),
    };
    let arf_tc_id = kctx.type_store.add_typeclass(&arf);

    kctx.parse_datatype("Foo");
    let foo_id = kctx.type_store.get_ground_id_by_name("Foo").unwrap();

    let arf_type = Term::typeclass(arf_tc_id);
    let dependent_result = Term::atom(Atom::BoundVariable(0));
    let arf_method_type = Term::pi(arf_type, dependent_result);
    kctx.symbol_table.add_global_constant(arf_method_type);

    let invalid = Term::atom(Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)))
        .apply(&[Term::ground_type(foo_id)]);

    let err = invalid
        .checked_type_with_context(&LocalContext::empty(), &kctx)
        .expect_err("Foo should not typecheck as an Arf instance");
    assert!(
        err.contains("not an instance of Arf"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_checked_type_with_context_accepts_valid_typeclass_type_arg() {
    let mut kctx = KernelContext::new();

    let arf = Typeclass {
        module_id: ModuleId(0),
        name: "Arf".to_string(),
    };
    let arf_tc_id = kctx.type_store.add_typeclass(&arf);

    kctx.parse_datatype("Foo");
    let foo_id = kctx.type_store.get_ground_id_by_name("Foo").unwrap();
    let foo_datatype = Datatype {
        module_id: ModuleId(0),
        name: "Foo".to_string(),
    };
    kctx.type_store
        .add_type_instance(&AcornType::Data(foo_datatype, vec![]), arf_tc_id);

    let arf_type = Term::typeclass(arf_tc_id);
    let dependent_result = Term::atom(Atom::BoundVariable(0));
    let arf_method_type = Term::pi(arf_type, dependent_result);
    kctx.symbol_table.add_global_constant(arf_method_type);

    let valid = Term::atom(Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 0)))
        .apply(&[Term::ground_type(foo_id)]);

    let ty = valid
        .checked_type_with_context(&LocalContext::empty(), &kctx)
        .expect("Foo should typecheck as an Arf instance");
    assert_eq!(ty, Term::ground_type(foo_id));
}
