use crate::elaborator::environment::Environment;
use crate::kernel::kernel_context::KernelContext;
use crate::module::LoadState;
use crate::project::Project;

fn has_inline_exists(clause: &crate::kernel::clause::Clause) -> bool {
    clause.literals.iter().any(|lit| {
        lit.is_signed_term()
            && matches!(
                lit.left.as_ref().decompose(),
                crate::kernel::term::Decomposition::Exists(_, _)
            )
    })
}

fn get_inline_exists_body(
    clause: &crate::kernel::clause::Clause,
) -> Option<crate::kernel::term::Term> {
    clause.literals.iter().find_map(|lit| {
        if lit.is_signed_term() {
            if let crate::kernel::term::Decomposition::Exists(_, body) =
                lit.left.as_ref().decompose()
            {
                return Some(body.to_owned());
            }
        }
        None
    })
}

#[test]
fn test_nat_normalization() {
    let mut env = Environment::test();
    let mut norm = KernelContext::new();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.expect_type("zero", "Nat");
    env.add("let suc: Nat -> Nat = axiom");
    env.expect_type("suc", "Nat -> Nat");
    env.add("let one: Nat = suc(zero)");
    env.expect_type("one", "Nat");

    env.add("axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }");
    norm.check(&env, "suc_injective", &["suc(x0) != suc(x1) or x0 = x1"]);
    env.expect_type("suc_injective", "(Nat, Nat) -> Bool");

    env.add("axiom suc_neq_zero(x: Nat) { suc(x) != zero }");
    norm.check(&env, "suc_neq_zero", &["zero != suc(x0)"]);
    env.expect_type("suc_neq_zero", "Nat -> Bool");

    env.add(
        "axiom induction(f: Nat -> Bool) {\
        f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) } }",
    );

    env.expect_type("induction", "(Nat -> Bool) -> Bool");

    env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }");
    env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

    env.add("axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }");
    env.expect_type("recursion_base", "(Nat -> Nat, Nat) -> Bool");
    norm.check(&env, "recursion_base", &["recursion(x0, x1, zero) = x1"]);

    env.add(
        "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {\
        recursion(f, a, suc(n)) = f(recursion(f, a, n)) }",
    );
    env.expect_type("recursion_step", "(Nat -> Nat, Nat, Nat) -> Bool");
    norm.check(
        &env,
        "recursion_step",
        &["recursion(x0, x1, suc(x2)) = x0(recursion(x0, x1, x2))"],
    );
}

#[test]
fn test_bool_formulas() {
    let mut env = Environment::test();
    let mut norm = KernelContext::new();
    env.add("theorem one(a: Bool) { a implies a or (a or a) }");
    norm.check(&env, "one", &[]);

    env.add("theorem two(a: Bool) { a implies a and (a and a) }");
    norm.check(&env, "two", &["not x0 or and(x0, and(x0, x0))"]);
}

#[test]
fn test_tautology_elimination() {
    let mut env = Environment::test();
    let mut norm = KernelContext::new();
    env.add("type Nat: axiom");
    env.add("theorem one(n: Nat) { n = n }");
    norm.check(&env, "one", &[]);

    env.add("theorem two(n: Nat) { n = n or n != n }");
    norm.check(&env, "two", &[]);
}

#[test]
fn test_forall_reflexive_goal_keeps_normalized_goal() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        r#"
        type MyType: axiom

        theorem goal(x: MyType) {
            x = x
        }
        "#,
    );

    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    let cursor = env.get_node_by_goal_name("goal");
    let normalized_goal = cursor
        .normalized_goal()
        .expect("reflexive forall goal should normalize");
    assert!(
        normalized_goal
            .steps
            .iter()
            .any(|step| step.clause.is_impossible()),
        "expected negated reflexive forall goal to normalize to contradiction, got {:?}",
        normalized_goal
            .steps
            .iter()
            .map(|step| step.clause.to_string())
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_second_order_binding() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let borf: (Nat, Nat, Nat) -> Bool = axiom
        define also_borf(a: Nat, b: Nat, c: Nat) -> Bool { borf(a, b, c) }
        let bb: Nat = axiom
        let cc: Nat = axiom
        define specific_borf(x: Nat) -> Bool { also_borf(x, bb, cc) }
        define always_true(f: Nat -> Bool) -> Bool { forall(n: Nat) { f(n) } }
        theorem goal { not always_true(specific_borf) }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["not always_true(specific_borf)"]);
}

#[test]
fn test_iet_normalizes_quantifier_bodies_before_clausification() {
    let mut env = Environment::test();
    env.add(
        r#"
        theorem goal {
            not forall(x: Bool) {
                not (x and not not x)
            }
        }
    "#,
    );

    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);
    assert_eq!(clauses.len(), 1, "expected a single clause");
    let clause = &clauses[0];
    assert!(
        has_inline_exists(clause),
        "expected an inline exists: {:?}",
        clause
    );
    let body = get_inline_exists_body(clause).expect("expected exists body");
    let bound = crate::kernel::term::Term::atom(crate::kernel::atom::Atom::BoundVariable(0));
    let expected = crate::kernel::term::Term::and(bound.clone(), bound);
    assert_eq!(body, expected);
}

#[test]
fn test_iet_top_level_negated_and_clausifies_to_disjunction() {
    let mut env = Environment::test();
    let mut norm = KernelContext::new();
    env.add("theorem goal(a: Bool, b: Bool, c: Bool) { a and b implies c }");
    norm.check(&env, "goal", &["not x0 or not x1 or x2"]);
}

#[test]
fn test_boolean_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let n0: Nat = axiom
        let n1: Nat = axiom
        let n2: Nat = axiom
        let n3: Nat = axiom
        theorem goal { (n0 = n1) = (n2 = n3) }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &["n1 != n0 or n3 = n2", "n3 != n2 or n1 = n0"],
    );
}

#[test]
fn test_boolean_inequality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let n0: Nat = axiom
        let n1: Nat = axiom
        let n2: Nat = axiom
        let n3: Nat = axiom
        theorem goal { (n0 = n1) != (n2 = n3) }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &["n3 != n2 or n1 != n0", "n3 = n2 or n1 = n0"],
    );
}

#[test]
fn test_functions_returning_lambdas() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let addx: (Nat, Nat) -> Nat = axiom
        define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
        theorem goal(a: Nat, b: Nat) { adder(a)(b) = adder(b)(a) }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["adder(x0, x1) = adder(x1, x0)"]);
}

#[test]
fn test_functional_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        define zerof(a: Nat) -> (Nat -> Nat) { function(b: Nat) { zero } }
        theorem goal(a: Nat, b: Nat) { zerof(a) = zerof(b) }
        "#,
    );
    let mut norm = KernelContext::new();
    // Functional equality gets expanded with free variables
    norm.check(&env, "goal", &["zerof(x0, x1) = zerof(x2, x1)"]);
}

#[test]
fn test_normalizing_exists_inline_with_iet() {
    use crate::kernel::term::Decomposition;

    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        let addx: (Nat, Nat) -> Nat = axiom
        theorem goal { exists(x: Nat) { addx(x, zero) = one } }
        "#,
    );
    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);
    assert_eq!(clauses.len(), 1, "expected one clause");
    let clause = &clauses[0];
    assert_eq!(clause.literals.len(), 1, "expected one literal");
    let lit = &clause.literals[0];
    assert!(
        lit.is_signed_term() && lit.positive,
        "expected a positive signed-term literal, got {}",
        lit
    );
    assert!(
        matches!(lit.left.as_ref().decompose(), Decomposition::Exists(_, _)),
        "expected inline exists term, got {}",
        lit.left
    );
    assert!(
        !clause.has_synthetic(),
        "inline exists clausification should not synthesize skolems"
    );
}

#[test]
fn test_denormalizing_disjunction() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        let ltx: (Nat, Nat) -> Bool = axiom
        let addx: (Nat, Nat) -> Nat = axiom
        theorem foo(x0: Nat, x1: Nat) { addx(addx(x0, zero), x1) != zero or ltx(x1, zero) }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "foo",
        &["addx(addx(x0, zero), x1) != zero or ltx(x1, zero)"],
    );
}

#[test]
fn test_if_then_else_under_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        let d: Bool = axiom

        theorem goal {
            a = if b {
                c
            } else {
                d
            }
        }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &[
            "not b or not a or c",
            "not a or d or b",
            "not c or not b or a",
            "not d or b or a",
        ],
    );
}

#[test]
fn test_if_then_else_with_true_branch_under_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let d: Bool = axiom

        theorem goal {
            a = if b {
                true
            } else {
                d
            }
        }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &["not a or d or b", "not b or a", "not d or b or a"],
    );
}

#[test]
fn test_if_then_else_in_boolean_disjunction() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        let d: Bool = axiom

        theorem goal {
            if a {
                b
            } else {
                c
            } or d
        }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["ite(Bool, a, b, c) or d"]);
}

#[test]
fn test_if_then_else_normalization_with_variables() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Elem: axiom
        let foo: (Elem -> Bool, Elem, Elem) -> Bool = axiom

        theorem goal(f: Elem -> Bool, item: Elem, x: Elem) {
            foo(f, item, x) = if x = item {
                true
            } else {
                f(x)
            }
        }
        "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &[
            "not foo(x0, x1, x2) or x1 = x2 or x0(x2)",
            "x0 != x1 or foo(x2, x0, x1)",
            "not x0(x1) or foo(x0, x2, x1) or x1 = x2",
        ],
    );
}

#[test]
fn test_lambda_normalization() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f1: (Nat, Nat) -> Nat = axiom
        let f2: (Nat, Nat) -> Nat = axiom

        theorem goal {
            forall(a: Nat) {
                f1(a) = function(b: Nat) {
                    f2(a)(b)
                }
            }
        }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["f2(x0, x1) = f1(x0, x1)"]);
}

#[test]
fn test_normalizing_functional_or() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        let dis: Nat -> Bool = axiom

        theorem goal(a: Nat) {
            dis(a) = (f(a) or g(a) or h(a))
        }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &[
            "not dis(x0) or h(x0) or g(x0) or f(x0)",
            "not f(x0) or dis(x0)",
            "not g(x0) or dis(x0)",
            "not h(x0) or dis(x0)",
        ],
    );
}

#[test]
fn test_normalizing_lambda_inside_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let z: Nat = axiom
        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Nat = axiom
        let h: (Nat, Nat) -> Nat = axiom

        theorem goal(a: Nat) {
            f(a) = function(b: Nat) {
                g(h(a, b)) = z
            }
        }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &[
            "not f(x0, x1) or g(h(x0, x1)) = z",
            "g(h(x0, x1)) != z or f(x0, x1)",
        ],
    );
}

#[test]
fn test_normalizing_function_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Nat = axiom
        let g: (Nat, Nat) -> Nat = axiom
        let a: Nat = axiom

        theorem goal {
            f = g(a)
        }
    "#,
    );
    let mut norm = KernelContext::new();
    // Functional equality gets expanded with free variables
    norm.check(&env, "goal", &["g(a, x0) = f(x0)"]);
}

#[test]
fn test_normalizing_function_inequality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Nat = axiom
        let g: (Nat, Nat) -> Nat = axiom
        let a: Nat = axiom

        theorem goal {
            f != g(a)
        }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["g(a) != f"]);
    let clauses = norm.get_all_clauses(&env);
    assert_eq!(clauses.len(), 1, "expected one clause");
    assert!(!clauses[0].has_synthetic());
}

#[test]
fn test_normalizing_func_eq_inside_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom
        let g: (Nat, Nat) -> Nat = axiom
        let h: (Nat, Nat) -> Nat = axiom

        theorem goal {
            f = function(x: Nat) {
                g(x) = h(x)
            }
        }
    "#,
    );
    let mut norm = KernelContext::new();
    // Functional equality inside lambda gets expanded with free variables
    norm.check(
        &env,
        "goal",
        &[
            "not f(x0) or h(x0, x1) = g(x0, x1)",
            "h(x0) != g(x0) or f(x0)",
        ],
    );
    let clauses = norm.get_all_clauses(&env);
    let has_synthetic = clauses.iter().any(|clause| clause.has_synthetic());
    assert!(!has_synthetic);
}

#[test]
fn test_normalizing_forall_inside_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            g = function(x: Nat) {
                    forall(y: Nat) {
                        f(x, y)
                    }
                }
        }
    "#,
    );
    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);
    assert_eq!(clauses.len(), 2, "expected two clauses");
    assert!(
        clauses.iter().any(|clause| {
            !has_inline_exists(clause)
                && clause.literals.len() == 2
                && clause.literals.iter().any(|lit| lit.positive)
                && clause.literals.iter().any(|lit| !lit.positive)
        }),
        "expected the forward implication clause to stay first-order"
    );
    assert!(
        clauses
            .iter()
            .any(|clause| has_inline_exists(clause) && clause.literals.len() == 2),
        "expected the reverse implication to keep an inline exists"
    );
}

#[test]
fn test_normalizing_forall_inside_neq_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            g != function(x: Nat) {
                    forall(y: Nat) {
                        f(x, y)
                    }
                }
        }
    "#,
    );
    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);
    assert_eq!(clauses.len(), 1, "expected one direct inequality clause");
    assert_eq!(clauses[0].literals.len(), 1, "expected one literal");
    assert!(
        !clauses[0].literals[0].positive,
        "expected direct function inequality, got {}",
        clauses[0]
    );
    let left = &clauses[0].literals[0].left;
    let right = &clauses[0].literals[0].right;
    assert!(
        left.as_ref().is_lambda() || right.as_ref().is_lambda(),
        "expected one side to stay as a lambda-valued function, got {}",
        clauses[0]
    );
    let lambda_side = if left.as_ref().is_lambda() {
        left
    } else {
        right
    };
    let (_input, body) = lambda_side
        .as_ref()
        .split_lambda()
        .expect("expected lambda-valued side");
    assert!(
        matches!(
            body.to_owned().as_ref().decompose(),
            crate::kernel::term::Decomposition::ForAll(_, _)
        ),
        "expected direct function inequality to preserve the lambda body, got {}",
        lambda_side
    );
    assert!(
        !clauses[0].has_synthetic(),
        "direct function inequality should not synthesize a witness"
    );
}

#[test]
fn test_normalizing_boolean_function_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            f = g
        }
    "#,
    );
    let mut norm = KernelContext::new();
    // Boolean functional equality gets expanded with free variables
    norm.check(&env, "goal", &["g(x0) = f(x0)"]);
}

#[test]
fn test_normalizing_boolean_function_inequality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            f != g
        }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["g != f"]);
    let clauses = norm.get_all_clauses(&env);
    assert_eq!(clauses.len(), 1, "expected one clause");
    assert!(!clauses[0].has_synthetic());
}

#[test]
fn test_normalizing_lambda_applied_to_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Foo: axiom
        let a: Foo = axiom
        let b: Foo = axiom
        let g: (Foo, Foo) -> Bool = axiom

        theorem goal {
            function(f: Foo -> Bool) {
                f(a)
            }(
                function(x: Foo) {
                    g(x, b)
                }
            )
        }
    "#,
    );
    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["g(a, b)"]);
}

#[test]
fn test_normalizing_and_inside_arg() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure BoxedBool {
            value: Bool
        }

        let f: (BoxedBool, BoxedBool) -> BoxedBool = axiom

        theorem goal {
            f = function(a: BoxedBool, b: BoxedBool) {
                BoxedBool.new(a.value and b.value)
            }
        }
    "#,
    );

    let mut norm = KernelContext::new();
    let expected = vec!["BoxedBool.new(and(BoxedBool.value(x0), BoxedBool.value(x1))) = f(x0, x1)"];
    norm.check(&env, "goal", &expected);
}

#[test]
fn test_preserves_or_over_and_shape() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom

        theorem goal {
            (a and b) or c
        }
    "#,
    );

    let mut norm = KernelContext::new();
    norm.check(&env, "goal", &["and(a, b) or c"]);
}

#[test]
fn test_normalizing_nested_lambdas() {
    let mut env = Environment::test();
    env.add(
        r#"
    type Nat: axiom
    type ListNat: axiom
    let range: Nat -> ListNat = axiom
    let sum: ListNat -> Nat = axiom
    let map: (ListNat, Nat -> Nat) -> ListNat = axiom

    define double_sum(n: Nat, m: Nat, f: (Nat, Nat) -> Nat) -> Nat {
        sum(map(range(n), function(i: Nat) {
            sum(map(range(m), function(j: Nat) { f(i, j) }))
        }))
    }

    theorem goal(a: Nat, b: Nat, f: (Nat, Nat) -> Nat) {
        double_sum(a, b, f) = sum(map(range(a), function(i: Nat) {
            sum(map(range(b), function(j: Nat) { f(i, j) }))
        }))
    }
    "#,
    );

    let mut norm = KernelContext::new();
    norm.check(
        &env,
        "goal",
        &["sum(map(range(x0), T0_0)) = double_sum(x0, x1, x2)"],
    );
}

#[test]
fn test_if_then_else_with_forall_condition() {
    // Test that if-then-else with a forall in the condition works correctly.
    // This exercises a code path where forall variables need their types tracked
    // in the context. The forall body is a conjunction so that it produces non-literal CNF.
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        let p: Nat -> Bool = axiom
        let q: Nat -> Bool = axiom

        theorem goal {
            if forall(n: Nat) { p(n) and q(n) } {
                zero
            } else {
                one
            } = zero
        }
        "#,
    );
    let mut norm = KernelContext::new();
    // The key thing is that normalization doesn't panic - the forall variable's type must be
    // properly tracked in the context when creating clauses.
    let expected = vec!["ite(T0_0, T0_0, zero, one) = zero"];
    norm.check(&env, "goal", &expected);
}

/// Test that normalizing a polymorphic theorem with type parameters in the goal doesn't crash.
/// This test catches a bug where the LocalContext was empty when clause normalization tried
/// to remap variables for type parameters.
#[test]
fn test_polymorphic_type_params_in_goal() {
    let mut env = Environment::test();
    env.add(
        r#"
        // Define a simple identity function with two equivalent definitions
        define id1[T](x: T) -> T { x }
        define id2[T](x: T) -> T { x }

        // This theorem has type parameter [T] that appears directly in the goal
        theorem id_equivalence[T] {
            id1[T] = id2[T]
        }
        "#,
    );
    let mut norm = KernelContext::new();
    // We don't check the exact clauses - we just verify normalization doesn't crash
    let clauses = norm.get_all_clauses(&env);
    assert!(!clauses.is_empty(), "Should have normalized clauses");
}

/// Test that checks the type of compose when instantiated with a higher-order return type.
///
/// compose[T, U, V](f: U -> V, g: T -> U) -> T -> V
///
/// When V = Nat -> Nat, the return type is Nat -> (Nat -> Nat).
/// After un-currying, compose should accept 4 value args total:
/// (f, g, x, y) where x: Nat and y: Nat.
#[test]
fn test_compose_type_with_higher_order_return() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let mul: Nat -> (Nat -> Nat) = axiom");
    env.add("let from_nat: Nat -> Nat = axiom");
    env.add(
        r#"
        define compose[T, U, V](f: U -> V, g: T -> U) -> T -> V {
            function(x: T) { f(g(x)) }
        }
        "#,
    );

    // compose[Nat, Nat, Nat -> Nat] should have type that allows 4 value args:
    // Original: (Nat -> (Nat -> Nat), Nat -> Nat) -> Nat -> (Nat -> Nat)
    // After full un-currying: (Nat -> (Nat -> Nat), Nat -> Nat, Nat, Nat) -> Nat
    env.add("let one: Nat = axiom");

    // This should work - applying compose to all 4 args
    // If this fails with "expected <= 3 arguments, but got 4", then the type isn't fully un-curried
    env.add("let result: Nat = compose[Nat, Nat, Nat -> Nat](mul, from_nat, one, one)");
}

/// THE BUG: When code generator decides type params can be "inferred", it omits them.
/// But for compose[T, U, V], when V is a function type, the arity changes.
/// Without explicit type params, the parser uses the generic arity (3), not the
/// instantiated arity (4), causing "expected <= 3 arguments, but got 4".
///
/// This test demonstrates that can_infer_type_params_from_args incorrectly returns
/// true even when the type params affect the arity.
#[test]
fn test_code_generator_omits_type_params_when_arity_changes() {
    use crate::code_generator::CodeGenerator;

    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let one: Nat = axiom");
    env.add("let mul: Nat -> (Nat -> Nat) = axiom");
    env.add("let from_nat: Nat -> Nat = axiom");
    env.add(
        r#"
        define compose[T, U, V](f: U -> V, g: T -> U) -> T -> V {
            function(x: T) { f(g(x)) }
        }

        theorem goal {
            compose[Nat, Nat, Nat -> Nat](mul, from_nat)(one) = mul(from_nat(one))
        }
        "#,
    );

    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);

    // Find the clause with compose and 4 args (the one derived from the goal)
    // This is: forall(x0: Nat) { compose[Nat, Nat, Nat -> Nat](mul, from_nat, one, x0) = ... }
    let mut found_compose_clause = false;
    for clause in &clauses {
        let denormalized = norm.denormalize(clause, None, None, false);
        let denorm_code = format!("{}", denormalized);

        if denorm_code.contains("compose[Nat, Nat, Nat -> Nat](mul, from_nat, one, x0)") {
            found_compose_clause = true;

            // Generate code using the code generator
            let mut generator = CodeGenerator::new(&env.bindings);
            let generated_code = generator.value_to_code(&denormalized).unwrap();

            // THE BUG: The code generator omits type params because can_infer_type_params_from_args
            // returns true. But for compose[T, U, V], when V is a function type, the arity changes.
            // Without explicit type params [Nat, Nat, Nat -> Nat], the parser uses generic arity (3)
            // instead of instantiated arity (4), causing "expected <= 3 arguments, but got 4".
            assert!(
                generated_code.contains("compose["),
                "BUG: Code generator omitted type params for compose.\n\
                 Denormalized: {}\n\
                 Generated: {}\n\
                 Without explicit type params, the parser will use generic arity (3)\n\
                 instead of instantiated arity (4), causing 'expected <= 3 arguments, but got 4'",
                denorm_code,
                generated_code
            );
        }
    }

    assert!(
        found_compose_clause,
        "Test setup error: no clause with compose and 4 args was found"
    );
}

/// Test that typeclass constraints work correctly when the prover needs to instantiate
/// with an arbitrary type. Similar to test_polymorphic_axiom_chain_needs_arbitrary_type
/// but with typeclass constraints.
///
/// If the Bool placeholder is being used for typeclass-constrained types, this should fail
/// because Bool doesn't satisfy the typeclass.
#[test]
fn test_polymorphic_axiom_chain_with_typeclass() {
    use crate::tests::common::verify_succeeds;

    verify_succeeds(
        r#"
        type Nat: axiom
        let zero: Nat = axiom

        typeclass N: Neg {
            neg: N -> N
        }

        let nat_neg: Nat -> Nat = axiom

        instance Nat: Neg {
            let neg: Nat -> Nat = nat_neg
        }

        let foo: Bool = axiom
        let baz: Bool = axiom

        define bar[T: Neg](x: T) -> Bool {
            axiom
        }

        axiom foo_imp_bar[T: Neg](x: T) {
            foo implies bar[T](x)
        }

        axiom bar_imp_baz[T: Neg](x: T) {
            bar[T](x) implies baz
        }

        theorem goal {
            foo implies baz
        }
        "#,
    );
}

/// Reproduces a bug where polymorphic synthetic definitions don't match during
/// certificate verification due to type variable ordering differences.
///
/// The issue is that when a polymorphic synthetic (skolem function) is created
/// with 2+ type parameters, the type variable ordering may differ between:
/// 1. When the definition is stored in synthetic_map
/// 2. When it's looked up during certificate checking
///
/// This causes "does not match any synthetic definition" errors.
#[test]
fn test_polymorphic_synthetic_type_var_ordering() {
    use crate::tests::common::verify_succeeds;

    // This test mimics the and_family pattern from set.ac which triggers the bug.
    // Key: and_family[K, I](f, x) has params in order [K, I] but uses I first in the
    // function type (I -> Set[K]).
    verify_succeeds(
        r#"
        structure Container[T] {
            member: T -> Bool
        }

        // Mirrors and_family[K, I](f: I -> Set[K], x: K) -> Bool
        // Note: K comes first in type params but I comes first in function type
        define all_contain[K, I](f: I -> Container[K], x: K) -> Bool {
            forall(i: I) {
                f(i).member(x)
            }
        }

        type Nat: axiom
        type Item: axiom

        // This axiom creates the skolem function pattern
        // When negated: not all_contain[K,I](f,x) creates exists(i:I) { not f(i).member(x) }
        axiom all_contain_witness[K, I](f: I -> Container[K], x: K) {
            not all_contain[K, I](f, x) implies exists(i: I) { not f(i).member(x) }
        }

        let f: Nat -> Container[Item] = axiom
        let x: Item = axiom

        // For this theorem, prover must use the all_contain_witness axiom
        // This requires matching the polymorphic synthetic definition
        theorem goal {
            not all_contain[Item, Nat](f, x) implies exists(n: Nat) { not f(n).member(x) }
        }
        "#,
    );
}

/// Test that type variables in denormalized clauses are displayed with proper formatting:
/// - Type variables should use "T" prefix (T0, T1) instead of "x" prefix
/// - Type variables should appear in forall with their kind (Type0 or typeclass name)
/// - The confusing pattern "x0: x0" should NOT appear
///
/// This test verifies the fix for the issue where type variables were displayed as:
///   forall(x0: x0) { not bar[x0](x0) or foo[x0] }
/// Instead of the clearer:
///   forall(T0: Type0, x1: T0) { not bar[T0](x1) or foo[T0] }
#[test]
fn test_type_variable_display_format() {
    let mut env = Environment::test();
    env.add(
        r#"
        let foo[T]: Bool = axiom
        let bar[T]: T -> Bool = axiom

        // This creates a clause with both type variables and value variables
        axiom ax1[T](x: T) { bar[T](x) implies foo[T] }
        "#,
    );

    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);

    // Find the clause for ax1 which has a type variable T and a value variable x
    let mut found_target_clause = false;
    for clause in &clauses {
        let denormalized = norm.denormalize(clause, None, None, false);
        let display = format!("{}", denormalized);

        // Check if this is a clause involving bar and foo
        if display.contains("bar") && display.contains("foo") {
            found_target_clause = true;

            // The confusing pattern "x0: x0" should NOT appear
            // (where a variable is named x0 and its type is also shown as x0)
            assert!(
                !display.contains("x0: x0"),
                "Type variable should not be displayed as 'x0: x0'. Got: {}",
                display
            );

            // Type variables should use "T" prefix when their kind is Type0
            // Value variables should use "x" prefix
            // The exact format depends on whether type vars are in forall,
            // but at minimum the "x0: x0" pattern should be gone
            println!("Denormalized clause: {}", display);
        }
    }

    assert!(
        found_target_clause,
        "Test setup error: no clause with bar and foo was found"
    );
}

/// Test that type variables with typeclass constraints display the typeclass name
/// instead of confusing internal representations.
#[test]
fn test_typeclass_constrained_type_variable_display() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass M: Monoid {
            identity: M
        }

        let identity_element[M: Monoid]: M = axiom

        // This creates a clause with a typeclass-constrained type variable
        axiom identity_exists[M: Monoid] { exists(x: M) { x = M.identity } }
        "#,
    );

    let mut norm = KernelContext::new();
    let clauses = norm.get_all_clauses(&env);

    // Find clauses involving the Monoid typeclass
    let mut found_typeclass_clause = false;
    for clause in &clauses {
        let denormalized = norm.denormalize(clause, None, None, false);
        let display = format!("{}", denormalized);

        if display.contains("Monoid") || display.contains(".identity") {
            found_typeclass_clause = true;

            // The confusing pattern where a variable's type is shown as itself should not appear
            assert!(
                !display.contains("x0: x0"),
                "Type variable should not be displayed as 'x0: x0'. Got: {}",
                display
            );

            println!("Typeclass clause: {}", display);
        }
    }

    assert!(
        found_typeclass_clause,
        "Test setup error: no clause with Monoid typeclass was found"
    );
}
