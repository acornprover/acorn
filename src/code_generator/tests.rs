use super::CodeGenerator;
use crate::elaborator::evaluator::Evaluator;
use crate::module::LoadState;
use crate::project::Project;
use crate::syntax::expression::Expression;

#[test]
fn test_non_legacy_boolean_reduction_emission_is_feature_gated() {
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;
    use crate::kernel::variable_map::VariableMap;
    use crate::processor::Processor;
    use crate::prover::proof::{ConcreteRationale, ConcreteStep};

    let (_processor, bindings, normalized_goal) = Processor::test_goal("theorem goal { true }");
    let mut kernel_context = normalized_goal.kernel_context;
    let source = Clause::new(
        vec![Literal::positive(Term::and(
            Term::new_variable(0),
            Term::new_true(),
        ))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    );
    let reduced = kernel_context.parse_clause("x0", &["Bool"]);
    let step = ConcreteStep {
        rationale: ConcreteRationale::BooleanReduction {
            source,
            emit_legacy: false,
        },
        generic: reduced,
        var_maps: vec![(
            VariableMap::new(),
            LocalContext::from_types(vec![Term::bool_type()]),
        )],
        preserve_open: true,
    };

    let mut generator = CodeGenerator::new_for_certificate(&bindings);
    let steps = generator
        .concrete_step_to_certificate_steps(&step, &mut kernel_context)
        .expect("certificate step generation should succeed");

    if cfg!(feature = "ebr") {
        assert_eq!(steps.len(), 1, "ebr should emit boolean reductions");
        assert!(
            matches!(
                steps.first(),
                Some(crate::kernel::certificate_step::CertificateStep::BooleanReduction(_))
            ),
            "ebr should emit explicit boolean-reduction certificate steps"
        );
    } else {
        assert!(
            steps.is_empty(),
            "default mode should preserve legacy skipping"
        );
    }
}

#[test]
fn test_foreign_scoped_constant_in_claim_codegen_is_rejected() {
    use crate::elaborator::acorn_type::AcornType;
    use crate::elaborator::names::ConstantName;
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;
    use crate::kernel::variable_map::VariableMap;
    use crate::module::ModuleId;
    use crate::processor::Processor;

    let (_processor, bindings, normalized_goal) = Processor::test_goal("theorem goal { true }");
    let mut kernel_context = normalized_goal.kernel_context;

    let foreign_name = ConstantName::Unqualified(ModuleId(999), "s0".to_string());
    let foreign_atom = kernel_context.add_scoped_constant(foreign_name, &AcornType::Bool, None);
    let Atom::Symbol(Symbol::ScopedConstant(foreign_local_id)) = foreign_atom else {
        panic!("expected scoped constant");
    };

    let clause = Clause::new(
        vec![Literal::positive(Term::atom(Atom::Symbol(
            Symbol::ScopedConstant(foreign_local_id),
        )))],
        &LocalContext::empty(),
    );

    let mut generator = CodeGenerator::new(&bindings);
    let mut steps = vec![];
    let err = generator
        .specialization_to_certificate_steps(
            &clause,
            &VariableMap::new(),
            &LocalContext::empty(),
            false,
            &mut kernel_context,
            &mut steps,
        )
        .expect_err("foreign scoped constants should fail certificate generation");
    assert!(
        err.to_string().contains("foreign scoped constant"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_incompatible_claim_mapping_is_rejected() {
    use crate::kernel::term::Term;
    use crate::kernel::variable_map::VariableMap;
    use crate::processor::Processor;

    let (_processor, bindings, normalized_goal) = Processor::test_goal("theorem goal { true }");
    let mut kernel_context = normalized_goal.kernel_context;
    let generic = kernel_context.parse_clause("x0 = x0", &["Bool"]);

    let mut bad_map = VariableMap::new();
    bad_map.set(0, Term::type_sort());

    let mut generator = CodeGenerator::new(&bindings);
    let mut steps = vec![];
    let err = generator
        .specialization_to_certificate_steps(
            &generic,
            &bad_map,
            &crate::kernel::local_context::LocalContext::empty(),
            false,
            &mut kernel_context,
            &mut steps,
        )
        .expect_err("incompatible mappings should fail certificate specialization");
    assert!(
        steps.is_empty(),
        "failing specialization should not emit steps"
    );
    assert!(
        err.to_string()
            .contains("certificate claim map type mismatch"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_out_of_scope_claim_mapping_is_rejected() {
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;
    use crate::kernel::variable_map::VariableMap;
    use crate::processor::Processor;

    let (_processor, bindings, normalized_goal) = Processor::test_goal("theorem goal { true }");
    let mut kernel_context = normalized_goal.kernel_context;
    let generic = kernel_context.parse_clause("x0 = x0", &["Bool"]);

    let mut bad_map = VariableMap::new();
    bad_map.set(0, Term::new_variable(2));
    let replacement_context = LocalContext::from_types(vec![Term::bool_type()]);

    let mut generator = CodeGenerator::new(&bindings);
    let mut steps = vec![];
    let err = generator
        .specialization_to_certificate_steps(
            &generic,
            &bad_map,
            &replacement_context,
            false,
            &mut kernel_context,
            &mut steps,
        )
        .expect_err("out-of-scope mappings should fail certificate specialization");
    assert!(
        steps.is_empty(),
        "failing specialization should not emit steps"
    );
    assert!(
        err.to_string().contains("out-of-scope term"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_claim_replay_handles_replacement_type_var_inference() {
    use crate::kernel::variable_map::VariableMap;
    use crate::processor::Processor;

    let (_processor, bindings, normalized_goal) = Processor::test_goal("theorem goal { true }");
    let mut kernel_context = normalized_goal.kernel_context;

    kernel_context.parse_polymorphic_constant("g0", "T: Type", "T -> Bool");
    kernel_context.parse_polymorphic_constant("g1", "A: Type, B: Type", "A -> B");

    let generic = kernel_context.parse_clause("g0(x0, x1)", &["Type", "x0"]);
    let replacement_context = kernel_context.parse_local(&["Type", "x0"]);

    let mut var_map = VariableMap::new();
    var_map.set(0, kernel_context.parse_term("Bool"));
    var_map.set(1, kernel_context.parse_term("g1(x0, Bool, x1)"));

    let mut generator = CodeGenerator::new(&bindings);
    let mut steps = vec![];
    generator
        .specialization_to_certificate_steps(
            &generic,
            &var_map,
            &replacement_context,
            false,
            &mut kernel_context,
            &mut steps,
        )
        .expect("specialization should succeed without replay mismatch");

    let claim = steps
        .iter()
        .find_map(|step| match step {
            crate::kernel::certificate_step::CertificateStep::Claim(claim) => Some(claim),
            crate::kernel::certificate_step::CertificateStep::Satisfy(_)
            | crate::kernel::certificate_step::CertificateStep::BooleanReduction(_) => None,
        })
        .expect("expected claim step");
    let mapped_value = claim
        .var_map()
        .get_mapping(1)
        .expect("expected value mapping in claim");
    assert!(
        mapped_value.max_variable().is_none(),
        "mapped term should have no free replacement vars left, got {}",
        mapped_value
    );
}

#[test]
fn test_claim_replay_preserves_replacement_context_for_surviving_type_local() {
    use crate::kernel::certificate_step::CertificateStep;
    use crate::kernel::variable_map::VariableMap;
    use crate::processor::Processor;

    let (_processor, bindings, normalized_goal) = Processor::test_goal("theorem goal { true }");
    let mut kernel_context = normalized_goal.kernel_context;

    kernel_context.parse_typeclass("FiniteGroup");
    kernel_context.parse_polymorphic_constant("g0", "T: Type", "Bool -> Bool");
    kernel_context.parse_polymorphic_constant("g1", "T: Type", "T -> Bool");

    // Reproduces the replay-mismatch shape from `reprove finite_group --line 67`:
    // a generic `(Type, x0)` clause is specialized using a replacement-context type local
    // constrained by a typeclass, but replay reinterprets the surviving local under the
    // generic context instead of the replacement context.
    let generic = kernel_context.parse_clause("g1(x0, x1)", &["Type", "x0"]);
    let replacement_context = kernel_context.parse_local(&["FiniteGroup"]);

    let mut var_map = VariableMap::new();
    var_map.set(0, kernel_context.parse_term("Bool"));
    var_map.set(1, kernel_context.parse_term("g0(x0, false)"));
    let expected_clause = var_map.specialize_clause_with_replacement_context_and_compact_vars(
        &generic,
        &replacement_context,
        &kernel_context,
    );

    let mut generator = CodeGenerator::new(&bindings);
    let mut steps = vec![];
    generator
        .specialization_to_certificate_steps(
            &generic,
            &var_map,
            &replacement_context,
            false,
            &mut kernel_context,
            &mut steps,
        )
        .expect("claim replay should preserve the replacement context for surviving type locals");

    assert_eq!(steps.len(), 1, "expected one generated claim step");
    let CertificateStep::Claim(claim) = &steps[0] else {
        panic!("expected a claim step");
    };
    assert_eq!(
        claim.clause().get_local_context().get_var_type(1),
        replacement_context.get_var_type(0),
        "generated claim should keep the replacement-context kind on a non-capturing local"
    );
    let mapped_x1 = claim
        .var_map()
        .get_mapping(2)
        .expect("expected a mapping for the generic value local");
    assert_eq!(mapped_x1, &kernel_context.parse_term("g0(x1, false)"));
    let displayed = claim
        .specialized_clause_for_display(&kernel_context)
        .expect("generated claim should specialize for display");
    assert_eq!(
        displayed, expected_clause,
        "generated claim should replay to the concrete clause built from the replacement context"
    );
}

#[test]
fn test_code_generation() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            type MyType: axiom
            let t: MyType = axiom
        "#,
    );
    p.check_code("main", "t");
    p.check_code("main", "forall(x0: MyType) { x0 = t }");
}

#[test]
fn test_bound_dependent_datatype_attribute_does_not_treat_receiver_as_family_arg() {
    use crate::elaborator::acorn_type::{AcornType, Datatype, DependentTypeArg, TypeParam};
    use crate::elaborator::acorn_value::{AcornValue, ConstantInstance};
    use crate::elaborator::names::ConstantName;

    let mut p = Project::new_mock_ide();
    p.mock(
        "/mock/main.ac",
        r#"
            type Set[T]: axiom

            structure Subspace[T, a: Set[T]] {
                value: T
            }
        "#,
    );
    let module_id = p.load_module_by_name("main").expect("load failed");
    let env = match p.get_module_by_id(module_id) {
        LoadState::Ok(module) => module.env().expect("expected retained environment"),
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    let set_datatype = Datatype {
        module_id,
        name: "Set".to_string(),
    };
    let subspace_datatype = Datatype {
        module_id,
        name: "Subspace".to_string(),
    };
    let t_param = TypeParam {
        name: "T".to_string(),
        typeclass: None,
    };
    let t_type = AcornType::Variable(t_param);
    let generic_set_t = AcornType::Data(set_datatype.clone(), vec![t_type.clone()]);
    let generic_a = AcornValue::Variable(0, generic_set_t.clone());
    let generic_subspace_t_a = AcornType::Family(
        subspace_datatype.clone(),
        vec![
            DependentTypeArg::Type(t_type.clone()),
            DependentTypeArg::Value(generic_a),
        ],
    );
    let generic_field_type = AcornType::functional(vec![generic_subspace_t_a], t_type.clone());

    let set_bool = AcornType::Data(set_datatype, vec![AcornType::Bool]);
    let a = AcornValue::Variable(0, set_bool.clone());
    let subspace_bool_a = AcornType::Family(
        subspace_datatype.clone(),
        vec![
            DependentTypeArg::Type(AcornType::Bool),
            DependentTypeArg::Value(a.clone()),
        ],
    );
    let p_value = AcornValue::Variable(1, subspace_bool_a.clone());
    let field = AcornValue::Constant(ConstantInstance {
        name: ConstantName::datatype_attr(module_id, subspace_datatype, "value"),
        params: vec![AcornType::Bool],
        instance_type: AcornType::functional(vec![subspace_bool_a], AcornType::Bool),
        generic_type: generic_field_type,
        type_param_names: vec!["T".to_string()],
        value_param_types: vec![generic_set_t],
        bound_value_args: vec![a],
    });
    let projection = AcornValue::apply(field, vec![p_value]);

    let mut generator = CodeGenerator::new_for_certificate(&env.bindings);
    let generated = generator
        .value_to_code_with_initial_vars(&projection, &["a".to_string(), "p".to_string()])
        .expect("projection should generate code");
    assert_eq!(generated, "Subspace[Bool, a].value(p)");
}

#[test]
fn test_code_for_imported_things() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/stuff.ac",
        r#"
            let thing1: Bool = axiom
            let thing2: Bool = axiom
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from stuff import thing1, thing2
            let st1: Bool = thing1
        "#,
    );
    p.check_code_into("main", "thing1", "thing1");
    p.check_code("main", "thing1");
    p.check_code("main", "thing2");
}

#[test]
fn test_imported_member_functions() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/boolpair.ac",
        r#"
            structure BoolPair {
                first: Bool
                second: Bool
            }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from boolpair import BoolPair
            let first: BoolPair -> Bool = BoolPair.first
        "#,
    );
    p.expect_ok("main");
    p.check_code("main", "first");
    p.check_code_into("main", "BoolPair.first", "first");
    p.check_code_into("main", "lib(boolpair).BoolPair.first", "first");

    p.check_code("main", "BoolPair.second");
    p.check_code_into("main", "lib(boolpair).BoolPair.second", "BoolPair.second");
}

#[test]
fn test_structure_aliasing() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/stuff.ac",
        r#"
            structure Foo {
                member: Bool
            }
            type Bar: Foo
        "#,
    );
    p.expect_ok("stuff");
    p.check_code_into("stuff", "Bar.member", "Foo.member");
}

#[test]
fn test_names_imported_via_from() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/stuff.ac",
        r#"
            type Foo: axiom
            attributes Foo {
                let foo: Bool = true
                let foo2: Bool = false
            }
            type Bar: Foo
            let bar: Bar = axiom
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from stuff import Foo, Bar, bar
            let x: Bool = Bar.foo
            let y: Bar = bar
        "#,
    );
    p.expect_ok("stuff");
    p.expect_ok("main");
    p.check_code("main", "x");
    p.check_code_into("main", "y", "bar");
    p.check_code_into("main", "Foo.foo2", "Foo.foo2");
}

#[test]
fn test_imported_numbers_codegen_basic() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/nat.ac",
        r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from nat import Nat
            "#,
    );
    p.check_code_into("main", "Nat.0", "Nat.0");
    p.check_code_into("main", "Nat.suc(Nat.0)", "Nat.0.suc");
    p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "Nat.0 + Nat.0");
}

#[test]
fn test_imported_numbers_codegen_with_numerals() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/nat.ac",
        r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from nat import Nat
            numerals Nat
            "#,
    );
    p.check_code_into("main", "Nat.0", "0");
    p.check_code_into("main", "Nat.suc(Nat.0)", "0.suc");
    p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "0 + 0");
}

#[test]
fn test_import_without_from_codegen() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/boolbox.ac",
        r#"
            structure BoolBox {
                item: Bool
            }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from boolbox import BoolBox
        "#,
    );
    p.check_code("main", "forall(x0: BoolBox) { true }");
}

#[test]
fn test_importing_a_generic_type() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/pair.ac",
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from pair import Pair
            "#,
    );
    p.check_code("main", "forall(x0: Pair[Bool, Bool]) { true }");
    p.check_code(
        "main",
        "forall(x0: Bool, x1: Bool) { Pair.new(x0, x1).second = x1 }",
    );
}

#[test]
fn test_generic_type_in_imported_module() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/pair.ac",
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from pair import Pair
            "#,
    );
    p.check_code("main", "forall(x0: Pair[Bool, Bool]) { true }");
}

#[test]
fn test_aliasing_local_generic_constant() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/pair.ac",
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            let pbbn: (Bool, Bool) -> Pair[Bool, Bool] = Pair[Bool, Bool].new
            "#,
    );
    p.expect_ok("pair");
    p.check_code("pair", "pbbn(false, true)");
}

#[test]
fn test_importing_generic_function() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/pair.ac",
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            define double[T](x: T) -> Pair[T, T] {
                Pair.new(x, x)
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from pair import double
            "#,
    );
    p.check_code("main", "double(true)");
}

#[test]
fn test_codegen_preserves_generic_args_for_partial_application() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            inductive Point {
                point
            }

            define constant[T, U](u: U, t: T) -> U {
                u
            }

            define apply_fn[T, U](f: T -> U, x: T) -> U {
                f(x)
            }

            theorem goal(a: Point, x: Point) {
                apply_fn(constant[Point, Point](a), x) = a
            }
            "#,
    );
    p.check_goal_code("main", "goal", "apply_fn(constant(a), x) = a");

    let module_id = p.expect_ok("main");
    let lowered = p
        .get_lowered_module(module_id)
        .expect("missing lowered module");
    let (_, entry) = lowered.goal_by_name("goal").expect("missing lowered goal");
    let mut generator = CodeGenerator::new_for_certificate(&entry.bindings);
    assert_eq!(
        generator
            .value_to_code(&entry.lowered_goal.goal.proposition.value)
            .expect("certificate codegen should render the goal"),
        "apply_fn(constant[Point, Point](a), x) = a"
    );
}

#[test]
fn test_codegen_preserves_generic_lambda_application() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            theorem goal {
                true
            }
            "#,
    );
    p.check_code_into(
        "main",
        "function[T](x0: T) { x0 = x0 }[Bool](true)",
        "function[T](x0: T) { x0 = x0 }[Bool](true)",
    );
}

#[test]
fn test_generic_function_in_imported_module() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/pair.ac",
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            define double[T](x: T) -> Pair[T, T] {
                Pair.new(x, x)
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from pair import double
            "#,
    );
    p.check_code("main", "double(true)");
}

#[test]
fn test_importing_typeclasses_with_import() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/magma.ac",
        r#"
            typeclass M: Magma {
                op: (M, M) -> M
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from magma import Magma

            inductive Z1 {
                zero
            }

            instance Z1: Magma {
                define op(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
    );
    p.check_code("main", "Z1.zero.op(Z1.zero) = Z1.zero");
}

#[test]
fn test_importing_typeclasses_with_from() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/magma.ac",
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from magma import Magma

            inductive Z1 {
                zero
            }

            instance Z1: Magma {
                define mul(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
    );
    p.check_code("main", "Z1.zero * Z1.zero = Z1.zero");
}

#[test]
fn test_codegen_typeclass_infix() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            theorem goal[M: Magma](x: M) {
                x * x = x
            }
            "#,
    );
    p.check_goal_code("main", "goal", "x * x = x");
}

#[test]
fn test_codegen_extended_infix() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            typeclass T: Thing extends Magma {
                thing_property: Bool
            }

            theorem goal[T: Thing](x: T) {
                x * x = x
            }
            "#,
    );
    p.check_goal_code("main", "goal", "x * x = x");
}

#[test]
fn test_codegen_for_imported_typeclasses() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
            typeclass F: Foo {
                zero: F
                add: (F, F) -> F
                neg: F -> F
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from foo import Foo

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            theorem goal[B: Bar](x: B) {
                x + -x = B.zero + B.zero
            }
            "#,
    );
    p.check_goal_code("main", "goal", "x + -x = B.zero + B.zero");
}

#[test]
fn test_codegen_rejects_future_instance_out_of_selected_scope() {
    let code = "\
typeclass A: Mul {
    mul: (A, A) -> A
}
inductive Foo {
    foo
}
let foo_zero: Foo = axiom
theorem goal {
    true
}
instance Foo: Mul {
    define mul(self, other: Foo) -> Foo {
        foo_zero
    }
}
";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let module_id = project
        .load_module_by_name("main")
        .expect("module should load");
    let (full_bindings, goal_bindings) = {
        let module = match project.get_module_by_id(module_id) {
            LoadState::Ok(module) => module,
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("unexpected module load state"),
        };
        let internal_line = 8;
        let lowered = module.lowered().expect("module should retain lowered work");
        let (_, entry) = lowered
            .goals()
            .find(|(_, entry)| {
                let goal = &entry.lowered_goal.goal;
                goal.first_line <= internal_line && internal_line <= goal.last_line
            })
            .expect("the selected theorem body line should resolve to a goal");
        (module.bindings().clone(), entry.bindings.clone())
    };

    let expr =
        Expression::parse_value_string("foo_zero * foo_zero").expect("expression should parse");
    let mut evaluator = Evaluator::new(&project, &full_bindings, None);
    let value = evaluator
        .evaluate_value(&expr, None)
        .expect("full-module bindings should resolve the later instance");

    let mut full_generator = CodeGenerator::new(&full_bindings);
    assert_eq!(
        full_generator
            .value_to_code(&value)
            .expect("value should render when the instance is in scope"),
        "foo_zero * foo_zero"
    );

    let mut goal_generator = CodeGenerator::new(&goal_bindings);
    let err = goal_generator
        .value_to_code(&value)
        .expect_err("selected goal bindings should reject future-instance calls");
    assert!(
        err.to_string().contains("current scope"),
        "unexpected error: {}",
        err
    );

    let mut cert_generator = CodeGenerator::new_for_certificate(&goal_bindings);
    let rendered = cert_generator
        .value_to_code(&value)
        .expect("certificate mode should allow explicit future-instance calls");
    assert_eq!(rendered, "Mul.mul[Foo](foo_zero, foo_zero)");

    let explicit_expr =
        Expression::parse_value_string(&rendered).expect("rendered expression should parse");
    let mut goal_evaluator = Evaluator::new(&project, &goal_bindings, None);
    let roundtrip = goal_evaluator
        .evaluate_value(&explicit_expr, None)
        .expect("explicit typeclass call should evaluate in goal bindings");
    assert_eq!(roundtrip, value);
}

#[test]
fn test_codegen_parenthesizes_if_in_binary_expression() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            type Nat: axiom
            let b: Nat = axiom

            theorem goal(a: Bool) {
                if a { b } else { b } != b
            }
            "#,
    );
    p.check_goal_code("main", "goal", "(if a { b } else { b }) != b");
}

#[test]
fn test_codegen_parenthesizes_not_in_left_binary_operand() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            let r: (Bool, Bool) -> Bool = axiom

            theorem goal(a: Bool, b: Bool, q: Bool) {
                (not r(a, b)) != q
            }
            "#,
    );
    p.check_goal_code("main", "goal", "(not r(a, b)) != q");
}

#[test]
fn test_codegen_uses_not_equals_for_nested_negative_equality() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            type Nat: axiom

            theorem goal(a: Nat, b: Nat, p: Bool) {
                not (p and not (a = b))
            }
            "#,
    );
    p.check_goal_code("main", "goal", "not (p and a != b)");
}

#[test]
fn test_codegen_for_quantified_types() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass F: Foo {
                item: F
            }

            inductive List[T] {
                nil
                cons(T, List[T])
            }

            structure Bar {
                item: Bool
            }

            theorem goal1 {
                exists(a: Bar) {
                    true
                }
            }

            theorem goal2 {
                exists(a: List[Bool]) {
                    true
                }
            }

            theorem goal3[F: Foo] {
                exists(a: List[F]) {
                    true
                }
            }

            theorem goal4 {
                exists(a: Bool) {
                    a
                }
            }
            "#,
    );
    p.check_goal_code("main", "goal1", "exists(k0: Bar) { true }");
    p.check_goal_code("main", "goal2", "exists(k0: List[Bool]) { true }");
    p.check_goal_code("main", "goal3", "exists(k0: List[F]) { true }");
    p.check_goal_code("main", "goal4", "exists(k0: Bool) { k0 }");
}

#[test]
fn test_codegen_indirect_attribute() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo_base.ac",
        r#"
            inductive Foo {
                foo
            }

            attributes Foo {
                define add(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
        "#,
    );
    p.mock(
        "/mock/foo_middle.ac",
        r#"
            from foo_base import Foo
            attributes Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
    );
    p.mock(
        "/mock/foo.ac",
        r#"
            from foo_middle import Foo
            attributes Foo {
                define sub(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from foo import Foo
            "#,
    );
    p.check_code("main", "Foo.add");
    p.check_code("main", "Foo.foo.add");
    p.check_code("main", "Foo.foo + Foo.foo");
    p.check_code("main", "Foo.mul");
    p.check_code("main", "Foo.foo.mul");
    p.check_code("main", "Foo.foo * Foo.foo");
    p.check_code("main", "Foo.sub");
    p.check_code("main", "Foo.foo.sub");
    p.check_code("main", "Foo.foo - Foo.foo");
}

#[test]
fn test_codegen_instance_attribute_access() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass F: Foo {
                vacuous {
                    true
                }
            }

            attributes F: Foo {
                let flag: Bool = true
                define foo(self) -> Bool {
                    true
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            theorem const_attr(b: Bar) {
                Bar.flag
            }

            theorem fn_attr(b: Bar) {
                b.foo
            }
            "#,
    );
    p.check_goal_code("main", "const_attr", "Bar.flag");
    p.check_goal_code("main", "fn_attr", "b.foo");
}

#[test]
fn test_codegen_overridden_attribute() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass F: Foo {
                vacuous {
                    true
                }
            }

            attributes F: Foo {
                let flag: Bool = true
                define foo(self) -> Bool {
                    true
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            // These override, changing the desired codegen.
            attributes Bar {
                let flag: Bool = false
                define foo(self) -> Bool {
                    false
                }
            }

            theorem const_attr(b: Bar) {
                Foo.flag[Bar]
            }

            theorem fn_attr(b: Bar) {
                Foo.foo[Bar](b)
            }
            "#,
    );
    p.check_goal_code("main", "const_attr", "Foo.flag[Bar]");
    p.check_goal_code("main", "fn_attr", "Foo.foo[Bar](b)");
}

#[test]
fn test_codegen_typeclass_digit_with_numerals() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass Z: Zero {
                0: Z
            }

            inductive Foo {
                foo
            }

            instance Foo: Zero {
                let 0: Foo = Foo.foo
            }

            numerals Foo

            theorem goal {
                Zero.0[Foo] = Foo.foo
            }
            "#,
    );
    p.check_goal_code("main", "goal", "0 = Foo.foo");
}

#[test]
fn test_codegen_typeclass_digit_with_own_attribute() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            typeclass Z: Zero {
                0: Z
            }

            inductive Bar {
                bar
            }

            // Bar has its OWN 0 attribute
            attributes Bar {
                let 0: Bar = Bar.bar
            }

            // Bar is also an instance of Zero, referencing its own 0
            instance Bar: Zero {
                let 0: Bar = Bar.0
            }

            theorem goal {
                Zero.0[Bar] = Bar.bar
            }
            "#,
    );
    p.check_goal_code("main", "goal", "Bar.0 = Bar.bar");
}

#[test]
fn test_codegen_operator_refs() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            type Nat: axiom
            "#,
    );
    p.check_code("main", "(not)");
    p.check_code("main", "(and)");
    p.check_code("main", "(or)");
    p.check_code_into("main", "function(x0: Nat, x1: Nat) { x0 = x1 }", "(=)");
}
