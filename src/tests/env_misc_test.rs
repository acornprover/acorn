use crate::environment::{Environment, LineType};
use crate::project::Project;

#[test]
fn test_fn_equality() {
    let mut env = Environment::test();
    env.add("define idb1(x: Bool) -> Bool { x }");
    env.expect_type("idb1", "Bool -> Bool");
    env.add("define idb2(y: Bool) -> Bool { y }");
    env.expect_type("idb2", "Bool -> Bool");
    env.assert_def_eq("idb1", "idb2");

    env.add("type Nat: axiom");
    env.add("define idn1(x: Nat) -> Nat { x }");
    env.expect_type("idn1", "Nat -> Nat");
    env.assert_def_ne("idb1", "idn1");
}

#[test]
fn test_forall_equality() {
    let mut env = Environment::test();
    env.add("let bsym1: Bool = forall(x: Bool) { x = x }");
    env.expect_type("bsym1", "Bool");
    env.add("let bsym2: Bool = forall(y: Bool) { y = y }");
    env.expect_type("bsym2", "Bool");
    env.assert_def_eq("bsym1", "bsym2");

    env.add("type Nat: axiom");
    env.add("let nsym1: Bool = forall(x: Nat) { x = x }");
    env.expect_type("nsym1", "Bool");
    env.assert_def_ne("bsym1", "nsym1");
}

#[test]
fn test_exists_equality() {
    let mut env = Environment::test();
    env.add("let bex1: Bool = exists(x: Bool) { x = x }");
    env.add("let bex2: Bool = exists(y: Bool) { y = y }");
    env.assert_def_eq("bex1", "bex2");

    env.add("type Nat: axiom");
    env.add("let nex1: Bool = exists(x: Nat) { x = x }");
    env.assert_def_ne("bex1", "nex1");
}

#[test]
fn test_forall_value() {
    let mut env = Environment::test();
    env.add("let p: Bool = forall(x: Bool) { x or not x }");
    env.expect_def("p", "forall(x0: Bool) { (x0 or not x0) }");
}

#[test]
fn test_inline_function_value() {
    let mut env = Environment::test();
    env.add("define ander(a: Bool) -> (Bool -> Bool) { function(b: Bool) { a and b } }");
    env.expect_def(
        "ander",
        "function(x0: Bool) { function(x1: Bool) { (x0 and x1) } }",
    );
}

#[test]
fn test_nat_ac_piecewise() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.add("let suc: Nat -> Nat = axiom");
    env.add("let one: Nat = suc(zero)");
    env.expect_def("one", "suc(zero)");

    env.add("axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }");
    env.expect_type("suc_injective", "(Nat, Nat) -> Bool");
    env.expect_def(
        "suc_injective",
        "function(x0: Nat, x1: Nat) { ((suc(x0) = suc(x1)) implies (x0 = x1)) }",
    );

    env.add("axiom suc_neq_zero(x: Nat) { suc(x) != zero }");
    env.expect_def("suc_neq_zero", "function(x0: Nat) { (suc(x0) != zero) }");

    assert!(env.bindings.has_typename("Nat"));
    assert!(!env.bindings.has_constant_name("Nat"));

    assert!(!env.bindings.has_typename("zero"));
    assert!(env.bindings.has_constant_name("zero"));

    assert!(!env.bindings.has_typename("one"));
    assert!(env.bindings.has_constant_name("one"));

    assert!(!env.bindings.has_typename("suc"));
    assert!(env.bindings.has_constant_name("suc"));

    assert!(!env.bindings.has_typename("foo"));
    assert!(!env.bindings.has_constant_name("foo"));

    env.add(
        "axiom induction(f: Nat -> Bool, n: Nat) {
            f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies f(n) }",
    );
    env.expect_def("induction", "function(x0: Nat -> Bool, x1: Nat) { ((x0(zero) and forall(x2: Nat) { (x0(x2) implies x0(suc(x2))) }) implies x0(x1)) }");

    env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }");
    env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

    env.add("axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }");
    env.add(
        "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {
            recursion(f, a, suc(n)) = f(recursion(f, a, n)) }",
    );

    env.add("define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }");
    env.expect_type("add", "(Nat, Nat) -> Nat");

    env.add("theorem add_zero_right(a: Nat) { add(a, zero) = a }");
    env.add("theorem add_zero_left(a: Nat) { add(zero, a) = a }");
    env.add("theorem add_suc_right(a: Nat, b: Nat) { add(a, suc(b)) = suc(add(a, b)) }");
    env.add("theorem add_suc_left(a: Nat, b: Nat) { add(suc(a), b) = suc(add(a, b)) }");
    env.add("theorem add_comm(a: Nat, b: Nat) { add(a, b) = add(b, a) }");
    env.add("theorem add_assoc(a: Nat, b: Nat, c: Nat) { add(add(a, b), c) = add(a, add(b, c)) }");
    env.add("theorem not_suc_eq_zero(x: Nat) { not (suc(x) = zero) }");
}

#[test]
fn test_names_in_subenvs() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            theorem foo(a: Nat, b: Nat) { a = b } by {
                let c: Nat = a
                define d(e: Nat) -> Bool { foo(e, b) }
            }
            "#,
    );
    env.check_lines();
}

#[test]
fn test_if_block_ending_with_exists() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            let a: Bool = axiom
            theorem goal { a } by {
                if a {
                    exists(b: Bool) { b = b }
                }
            }
            "#,
    );
    let module = p.expect_ok("main");
    let env = p.get_env_by_id(module).unwrap();
    for node in env.iter_goals() {
        node.goal().unwrap();
    }
}

#[test]
fn test_forall_block_ending_with_exists() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
            let a: Bool = axiom
            theorem goal { a } by {
                forall(b: Bool) {
                    exists(c: Bool) { c = c }
                }
            }
            "#,
    );
    let module = p.expect_ok("main");
    let env = p.get_env_by_id(module).unwrap();
    for node in env.iter_goals() {
        node.goal().unwrap();
    }
}

#[test]
fn test_type_params_cleaned_up() {
    let mut env = Environment::test();
    env.add("define foo[T](a: T) -> Bool { axiom }");
    assert!(env.bindings.get_type_for_typename("T").is_none());
}

#[test]
fn test_propositional_codegen() {
    let mut env = Environment::test();
    env.add("let b: Bool = axiom");
    env.bindings.expect_good_code("not b or b");
    env.bindings.expect_good_code("b and not b");
    env.bindings.expect_good_code("not not b");
    env.bindings.expect_good_code("not (b and b)");
}

#[test]
fn test_operator_codegen() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define add(self, other: Nat) -> Nat { axiom }
                define sub(self, other: Nat) -> Nat { axiom }
                define mul(self, other: Nat) -> Nat { axiom }
                define div(self, other: Nat) -> Nat { axiom }
                define mod(self, other: Nat) -> Nat { axiom }
                define lt(self, other: Nat) -> Bool { axiom }
                define gt(self, other: Nat) -> Bool { axiom }
                define lte(self, other: Nat) -> Bool { axiom }
                define gte(self, other: Nat) -> Bool { axiom }
                define neg(self) -> Nat { axiom }
                define suc(self) -> Nat { axiom }
                define foo(self, other: Nat) -> Nat { axiom }
                let 0: Nat = axiom
                let 1: Nat = axiom
            }
            numerals Nat
        "#,
    );
    env.bindings.expect_good_code("0 + 1");
    env.bindings.expect_good_code("0 - 1");
    env.bindings.expect_good_code("0 * 1");
    env.bindings.expect_good_code("0 / 1");
    env.bindings.expect_good_code("0 % 1");
    env.bindings.expect_good_code("0 < 1");
    env.bindings.expect_good_code("not 0 < 1");
    env.bindings.expect_good_code("0 > 1");
    env.bindings.expect_good_code("0 <= 1");
    env.bindings.expect_good_code("0 >= 1");
    env.bindings.expect_good_code("0 + 0 * 0");
    env.bindings.expect_good_code("(0 + 0) * 0");
    env.bindings.expect_good_code("0 + 0 + 0");
    env.bindings.expect_good_code("1 - (1 - 1)");
    env.bindings.expect_good_code("(0 + 1).suc = 1 + 1");
    env.bindings.expect_good_code("1 + 1 * 1");
    env.bindings.expect_good_code("0.suc = 1");
    env.bindings.expect_good_code("0.foo(1)");
    env.bindings.expect_good_code("0.add");
    env.bindings.expect_good_code("-0 - 1");
    env.bindings.expect_good_code("-(0 - 1)");
    env.bindings.expect_good_code("-0 * 1");
    env.bindings.expect_good_code("-(0 * 1)");
    env.bindings.expect_good_code("-0.suc");
    env.bindings.expect_good_code("(-0).suc");
}

#[test]
fn test_numeric_literal_codegen() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                let 0: Nat = axiom
                define suc(self) -> Nat { axiom }
                let 1: Nat = Nat.0.suc
                let 2: Nat = Nat.1.suc
                let 3: Nat = Nat.2.suc
                let 4: Nat = Nat.3.suc
                let 5: Nat = Nat.4.suc
                let 6: Nat = Nat.5.suc
                let 7: Nat = Nat.6.suc
                let 8: Nat = Nat.7.suc
                let 9: Nat = Nat.8.suc
                let 10: Nat = Nat.9.suc
                define read(self, other: Nat) -> Nat { axiom }
                define add(self, other: Nat) -> Nat { axiom }
            }
            numerals Nat
        "#,
    );
    env.bindings.expect_good_code("7");
    env.bindings.expect_good_code("10");
    env.bindings.expect_good_code("12");
    env.bindings.expect_good_code("123 + 456");
    env.bindings.expect_good_code("0.suc");
}

#[test]
fn test_non_default_numeric_literals() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                let 0: Nat = axiom
                define suc(self) -> Nat { axiom }
                let 1: Nat = Nat.0.suc
                let 2: Nat = Nat.1.suc
                let 3: Nat = Nat.2.suc
                let 4: Nat = Nat.3.suc
                let 5: Nat = Nat.4.suc
                let 6: Nat = Nat.5.suc
                let 7: Nat = Nat.6.suc
                let 8: Nat = Nat.7.suc
                let 9: Nat = Nat.8.suc
                let 10: Nat = Nat.9.suc
                define read(self, other: Nat) -> Nat { axiom }
                define add(self, other: Nat) -> Nat { axiom }
            }
        "#,
    );
    env.bindings.expect_good_code("Nat.7");
    env.bindings.expect_good_code("Nat.10");
    env.bindings.expect_good_code("Nat.12");
    env.bindings.expect_good_code("Nat.123 + Nat.456");
}

#[test]
fn test_structure_with_good_constraint() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Thing {
                foo: Bool
                baz: Bool
                bar: Bool
            } constraint {
                foo or baz or bar
            }
        "#,
    );
    for (i, line_type) in env.line_types.iter().enumerate() {
        println!("{}: {:?}", i, line_type);
    }
    assert!(matches!(env.get_line_type(6), Some(LineType::Node(_))));
    assert!(matches!(env.get_line_type(7), Some(LineType::Node(_))));
}

#[test]
fn test_structure_with_constraint_and_by_block() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Thing {
                foo: Bool
                baz: Bool
                bar: Bool
            } constraint {
                foo or baz or bar
            } by {
                true or true or true
            }
        "#,
    );
    assert_eq!(env.iter_goals().count(), 2);
}

#[test]
fn test_todo_statement() {
    let mut env = Environment::test();
    env.add(
        r#"
            let a: Bool = axiom
            let b: Bool = axiom
            
            todo {
                theorem foo(x: Bool, y: Bool) {
                    x = y or x or y
                }
                
                axiom bar {
                    a and b
                }
                
                if a {
                    b
                }
            }
            
            theorem actual_theorem {
                a or not a
            }
        "#,
    );

    // Debug: print out all goals to understand what's happening
    let goals: Vec<_> = env.iter_goals().collect();
    println!("Number of goals: {}", goals.len());
    for (i, goal) in goals.iter().enumerate() {
        println!("Goal {}: {:?}", i, goal);
    }

    // The todo block should be syntactically valid but not create any goals
    // Only the actual_theorem should create a goal
    assert_eq!(env.iter_goals().count(), 1);

    // Verify that the todo block's contents are parsed but not proven
    // by checking that we can still reference a and b (they exist in the outer scope)
    env.bindings.expect_good_code("a");
    env.bindings.expect_good_code("b");
}
