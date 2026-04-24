// Tests for syntax parsing and basic language constructs.
// These tests check parsing rules, control flow, operators, and syntactic features.

use crate::elaborator::environment::Environment;

#[test]
fn test_arg_binding() {
    let mut env = Environment::test();
    env.bad("define qux(x: Bool, x: Bool) -> Bool { x }");
    env.add("define qux(x: Bool, y: Bool) -> Bool { x }");
    env.bad("theorem foo(x: Bool, x: Bool) { x }");
    env.add("theorem foo(x: Bool, y: Bool) { x }");
    env.bad("let bar: Bool = forall(x: Bool, x: Bool) { x = x }");
    env.add("let bar: Bool = forall(x: Bool, y: Bool) { x = x }");
    env.bad("let baz: Bool = exists(x: Bool, x: Bool) { x = x }");
    env.add("let baz: Bool = exists(x: Bool, y: Bool) { x = x }");
}

#[test]
fn test_no_double_grouped_arg_list() {
    let mut env = Environment::test();
    env.add("define foo(x: Bool, y: Bool) -> Bool { x }");
    env.add("let b: Bool = axiom");
    env.bad("foo((b, b))");
}

#[test]
fn test_argless_theorem() {
    let mut env = Environment::test();
    env.add("let b: Bool = axiom");
    env.add("theorem foo { b or not b }");
}

#[test]
fn test_empty_if_block() {
    let mut env = Environment::test();
    env.add("let b: Bool = axiom");
    env.add("if b {}");
}

#[test]
fn test_empty_forall_statement() {
    // Allowed as statement but not as an expression.
    let mut env = Environment::test();
    env.add("forall(b: Bool) {}");
}

#[test]
fn test_if_condition_must_be_bool() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.add("let b: Bool = axiom");
    env.add("if b { zero = zero }");
    env.bad("if zero { zero = zero }");
}

#[test]
fn test_reusing_type_name_as_var_name() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let Nat: Bool = axiom");
}

#[test]
fn test_reusing_var_name_as_type_name() {
    let mut env = Environment::test();
    env.add("let x: Bool = axiom");
    env.bad("type x: axiom");
}

#[test]
fn test_reusing_type_name_as_fn_name() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("define Nat(x: Bool) -> Bool { x }");
}

#[test]
fn test_reusing_type_name_as_theorem_name() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("theorem Nat(x: Bool): x = x");
}

#[test]
fn test_reusing_type_name_as_exists_arg() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let b: Bool = exists(x: Bool, Nat: Bool) { x = x }");
}

#[test]
fn test_reusing_type_name_as_forall_arg() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let b: Bool = forall(x: Bool, Nat: Bool) { x = x }");
}

#[test]
fn test_reusing_type_name_as_lambda_arg() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let f: (bool, bool) -> Bool = function(x: Bool, Nat: Bool) { x = x }");
}

#[test]
fn test_parsing_true_false_keywords() {
    let mut env = Environment::test();
    env.add("let b: Bool = true or false");
}

#[test]
fn test_choose_not_allowed_in_surface_expression() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let foo: Nat -> Bool = axiom");
    env.bad("let b: Bool = choose");
    env.bad("let b: Bool = choose(true)");
    env.bad("let b: Bool = choose(x: Nat) { foo(x) }");
}

#[test]
fn test_nothing_after_explicit_false() {
    let mut env = Environment::test();
    env.add("let b: Bool = axiom");
    env.bad(
        r#"
            if b = not b {
                false
                b
            }
        "#,
    );
}

#[test]
fn test_condition_must_be_valid() {
    let mut env = Environment::test();
    env.bad(
        r#"
            if a {
            }
        "#,
    );
}

#[test]
fn test_structs_must_be_capitalized() {
    let mut env = Environment::test();
    env.bad(
        r#"
            struct foo {
                bar: Bool
            }
        "#,
    );
}

#[test]
fn test_axiomatic_types_must_be_capitalized() {
    let mut env = Environment::test();
    env.bad("type foo: axiom");
}

#[test]
fn test_dependent_structures_can_be_used() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add(
        r#"
            structure Fin[n: Nat] {
                value: Nat
            } constraint {
                value = value
            }
        "#,
    );
    env.add("theorem fin_member(n: Nat, x: Fin[n]) { x.value = x.value }");

    env.add(
        r#"
            structure Zmod[k: Nat] {
                value: Nat
            }
        "#,
    );
    env.add("theorem zmod_round_trip(k: Nat, x: Nat) { Zmod[k].new(x).value = x }");
}

#[test]
fn test_dependent_theorem_params_report_not_supported_yet() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("type Indexed[n: Nat]: axiom");
    let theorem_error = env.bad("theorem goal[T, n: Nat] { true }");
    assert!(theorem_error.contains("dependent value parameters"));
}

#[test]
fn test_dependent_type_arguments_can_be_used() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let k: Nat = axiom");
    env.add("type Fin[n: Nat]: axiom");
    env.add(
        r#"
            structure Box[T] {
                value: T
            }
        "#,
    );
    let error = env.bad("let x: Box[k] = axiom");
    assert!(error.contains("dependent type arguments"));

    env.add("let y: Fin[k] = axiom");
    env.add("theorem goal(n: Nat, x: Fin[n]) { x = x }");
}

#[test]
fn test_generic_axiomatic_type_family_can_be_used() {
    let mut env = Environment::test();
    env.add("type Box[T]: axiom");
    env.add("let x: Box[Bool] = axiom");
}

#[test]
fn test_parameterized_type_aliases_can_be_used() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
        "#,
    );
    env.add("type Diagonal[T]: Pair[T, T]");
    env.add("let x: Diagonal[Bool] = Pair.new(true, false)");
}

#[test]
fn test_parameterized_function_type_aliases_can_be_used() {
    let mut env = Environment::test();
    env.add("type Pred[T]: T -> Bool");
    env.add("let p: Pred[Bool] = function(x: Bool) { x }");
}

#[test]
fn test_generic_lambda_body_can_infer_equality_operator_ref_type() {
    let mut env = Environment::test();
    env.add("define singleton_fun[T](a: T, x: T) -> Bool { a = x }");
    env.add(
        r#"
            let b: Bool = function[T] {
                singleton_fun[T] = (=)
            }[Bool]
        "#,
    );
}

#[test]
fn test_else_on_new_line() {
    // This is ugly but it should work.
    let mut env = Environment::test();
    env.add(
        r#"
        let b: Bool = axiom
        if b {
            b
        }
        else {
            not b
        }
        "#,
    );
}

#[test]
fn test_arg_names_lowercased() {
    let mut env = Environment::test();
    env.bad("let f: Bool -> Bool = function(A: Bool) { true }");
    env.add("let f: Bool -> Bool = function(a: Bool) { true }");
    env.bad("forall(A: Bool) { true }");
    env.add("forall(a: Bool) { true }");
    env.bad("define foo(X: Bool) -> Bool { true }");
    env.add("define foo(x: Bool) -> Bool { true }");
    env.bad("theorem bar(X: Bool) { true }");
    env.add("theorem bar(x: Bool) { true }");
}

#[test]
fn test_no_magic_names_for_struct_fields() {
    let mut env = Environment::test();
    env.bad(
        r#"
            struct MyStruct {
                add: Bool
            }
        "#,
    );
}

#[test]
fn test_numerals_statement() {
    let mut env = Environment::test();
    env.add("type Foo: axiom");
    env.add("numerals Foo");
    env.bad("numerals Bar");
    env.bad("numerals Bool");
    env.bad("numerals Foo -> Foo");
}

#[test]
fn test_no_defining_top_level_numbers() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let 0: Nat = axiom");
}

#[test]
fn test_no_top_level_numbers_without_a_numerals() {
    let mut env = Environment::test();
    env.bad("let foo: Bool = (0 = 0)");
}

#[test]
fn test_anonymous_theorem_env() {
    let mut env = Environment::test();
    env.add(
        r#"
            theorem {
                true
            }
        "#,
    );
}

#[test]
fn test_anonymous_theorem_env_with_args() {
    let mut env = Environment::test();
    env.add(
        r#"
            theorem(a: Bool, b: Bool) {
                a = b or a or b
            }
        "#,
    );
    assert_eq!(
        env.nodes.last().unwrap().proposition().unwrap().arg_count,
        2
    );
}

#[test]
fn test_anonymous_axiom_env() {
    let mut env = Environment::test();
    env.add(
        r#"
            axiom {
                not false
            }
        "#,
    );
}

#[test]
fn test_anonymous_axiom_env_with_arg() {
    let mut env = Environment::test();
    env.add(
        r#"
            axiom(a: Bool) {
                a or not a
            }
        "#,
    );
}

#[test]
fn test_implies_keyword_in_env() {
    let mut env = Environment::test();
    env.add(
        r#"
            theorem {
                true implies true
            }
        "#,
    );
    env.bad(
        r#"
            type Foo {
                axiom
            }
            theorem(f: Foo) {
                f implies f
            }
            "#,
    );
}

#[test]
fn test_forall_subenv() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            forall(x: Nat) {
                x = x
            }
            "#,
    );
}

#[test]
fn test_if_subenv() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            if zero = zero {
                zero = zero
            }
            "#,
    )
}

#[test]
fn test_let_satisfy_exports_names() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            define foo(x: Nat) -> Bool { axiom }
            theorem goal { true } by {
                let z: Nat satisfy { foo(z) }
                foo(z)
            }
        "#,
    );
}

#[test]
fn test_environment_with_function_satisfy() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            let flip(a: Bool) -> b: Bool satisfy {
                a != b
            }
        "#,
    );
    assert_eq!(
        env.nodes.last().unwrap().proposition().unwrap().arg_count,
        1
    );
}

#[test]
fn test_match_subenv() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }

            forall(f: Foo) {
                match f {
                    Foo.bar(b) {
                        b or not b
                    }
                    Foo.baz {
                        true
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_value_pattern_with_no_args() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }

            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar(b) {
                        b
                    }
                    Foo.baz {
                        false
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_value_missing_cases() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }"#,
    );
    env.bad(
        r#"
            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar(b) {
                        b
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_statement_missing_cases() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }"#,
    );
    env.bad(
        r#"
            forall (f: Foo) {
                match f {
                    Foo.bar(b) {
                        b
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_value_against_new() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Foo {
                bar: Bool
            }

            define foo(f: Foo) -> Bool {
                match f {
                    Foo.new(b) {
                        b
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_match_value_no_repeating_variables() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool, Bool)
            }
            "#,
    );
    env.bad(
        r#"
            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar(b, b) {
                        b
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_match_statement_no_repeating_variables() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool, Bool)
            }
            "#,
    );
    env.bad(
        r#"
            forall (f: Foo) {
                match f {
                    Foo.bar(b, b) {
                        b
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_match_value_no_repeating_cases() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }"#,
    );
    env.bad(
        r#"
            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar(b) {
                        b
                    }
                    Foo.baz {
                        false
                    }
                    Foo.bar(b) {
                        b
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_statement_no_repeating_cases() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }"#,
    );
    env.bad(
        r#"
            forall (f: Foo) {
                match f {
                    Foo.bar(b) {
                        b
                    }
                    Foo.baz {
                        false
                    }
                    Foo.bar(b) {
                        b
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_value_results_check_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar
            }"#,
    );
    env.bad(
        r#"
            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar {
                        Foo.bar
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_match_value_with_let() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }"#,
    );
    env.add(
        r#"
            let f: Foo = Foo.bar(true)
            let b: Bool = match f {
                Foo.bar(b) {
                    b
                }
                Foo.baz {
                    false
                }
            }
        "#,
    );
}

#[test]
fn test_newline_in_define_args() {
    let mut env = Environment::test();
    env.add(
        r#"
        define foo(b: Bool,
                   c: Bool) -> Bool {
            b or c
        }
        "#,
    );
}

#[test]
fn test_omitting_else_for_boolean() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = forall(b: Bool, c: Bool) {
            if b {
                c
            }
        }
        "#,
    );
}

#[test]
fn test_standalone_lib_is_error() {
    let mut env = Environment::test();
    // lib must be used with parentheses
    env.bad("let x = lib");
    env.bad("let t: lib = axiom");
    env.bad("theorem foo { lib }");

    // lib(foo) would also fail because module foo doesn't exist
    env.bad("let y = lib(foo)");
    env.bad("let z = lib(foo).bar");
}

#[test]
fn test_reusing_forall_names() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
        "#,
    );
    env.bad(
        r#"
            forall(a: Nat) {
                forall(a: Nat) {
                    a = a
                }
            }
        "#,
    );
}

#[test]
fn test_reusing_exists_names() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
        "#,
    );
    env.bad(
        r#"
            let x: Bool = exists(a: Nat) {
                exists(a: Nat) {
                    a = a
                }
            }
        "#,
    );
}

#[test]
fn test_reusing_function_arg_names() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
        "#,
    );
    env.bad(
        r#"
            let f: Nat -> (Nat -> Bool) = function(a: Nat) {
                function(a: Nat) {
                    a = a
                }
            }
        "#,
    );
}

#[test]
fn test_reusing_goal_arg_name() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
        "#,
    );
    env.bad(
        r#"
            theorem goal(a: Nat) {
                function(a: Nat) {
                    a = a
                }(a)
            }
        "#,
    );
}

#[test]
fn test_iff_basics() {
    let mut env = Environment::test();
    env.add(
        r#"
    theorem goal(a: Bool, b: Bool) {
        a or b iff b or a
    }
    "#,
    )
}

#[test]
fn test_iff_not_allowed_for_non_bool() {
    let mut env = Environment::test();
    env.add(
        r#"
    type Nat: axiom
    let m: Nat = axiom
    let n: Nat = axiom
    "#,
    );
    env.bad("let b: Bool = (m iff n)");
}

#[test]
fn test_line_continuation_with_equals() {
    let mut env = Environment::test();
    env.add(
        r#"
        let x: Bool =
            true
        "#,
    );
    env.add(
        r#"
        type Nat: axiom
        theorem foo(a: Nat, b: Nat) {
            a = b or a != b
        } by {
            if not a != b {
                a =
                    b
            }
            if not a = b {
                a !=
                    b
            }
        }
        "#,
    );
}

#[test]
fn test_line_continuation_with_infix_operators() {
    let mut env = Environment::test();
    // Test or
    env.add(
        r#"
        let test_or: Bool = true or
            false
        "#,
    );
    // Test and
    env.add(
        r#"
        let test_and: Bool = true and
            true
        "#,
    );
    // Test chained boolean operators
    env.add(
        r#"
        let test_chain: Bool = true or
            false and
            true
        "#,
    );
    // Test arithmetic operators with magic methods
    env.add(
        r#"
        type Nat: axiom
        attributes Nat {
            define add(self, other: Nat) -> Nat { axiom }
            define sub(self, other: Nat) -> Nat { axiom }
            define mul(self, other: Nat) -> Nat { axiom }
            define div(self, other: Nat) -> Nat { axiom }
        }
        let a: Nat = axiom
        let b: Nat = axiom
        let c: Nat = axiom
        "#,
    );
    // Test +
    env.add(
        r#"
        let test_plus: Nat = a +
            b
        "#,
    );
    // Test -
    env.add(
        r#"
        let test_minus: Nat = a -
            b
        "#,
    );
    // Test *
    env.add(
        r#"
        let test_mul: Nat = a *
            b
        "#,
    );
    // Test /
    env.add(
        r#"
        let test_div: Nat = a /
            b
        "#,
    );
    // Test chained arithmetic operators
    env.add(
        r#"
        let test_chain_arith: Nat = a +
            b *
            c
        "#,
    );
}

#[test]
fn test_curry_style_type_syntax() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        define foo(n: Nat, f: Nat -> Nat -> Nat) -> Nat {
            f(n)(n)
        }
        "#,
    )
}

#[test]
fn test_env_destructuring_let() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let f: Nat -> Nat = axiom
        let f(a) = zero
        "#,
    );
}

#[test]
fn test_env_destructuring_no_duplicate_names() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let f: (Nat, Nat) -> Nat = axiom
        "#,
    );
    env.bad("let f(a, a) = zero");
}

#[test]
fn test_env_destructuring_with_attribute() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure Pair {
            first: Bool
            second: Bool
        }
        let p: Pair = Pair.new(true, false)
        let Pair.new(x, y) = p
        "#,
    );
}

#[test]
fn test_env_destructuring_with_polymorphic_constructor() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Int: axiom

        structure Rat {
            value: Int
        }

        inductive Option[T] {
            some(T)
            none
        }

        define make_rat_option(i: Int) -> Option[Rat] {
            Option.some(Rat.new(i))
        }

        let i: Int = axiom
        let Option.some(rat_zero) = make_rat_option(i)

        theorem rat_zero_is_well_typed {
            rat_zero = rat_zero
        }
        "#,
    );
}

#[test]
fn test_operator_ref_values() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom

        let negate: Bool -> Bool = (not)
        let both: (Bool, Bool) -> Bool = (and)
        let either: (Bool, Bool) -> Bool = (or)
        let eq_nat: (Nat, Nat) -> Bool = (=)
        let is_zero: Nat -> Bool = (=)(zero)

        define apply_binary[T](op: (T, T) -> Bool, a: T, b: T) -> Bool {
            op(a, b)
        }

        let b1: Bool = negate(false)
        let b2: Bool = both(true, false)
        let b3: Bool = either(true, false)
        let b4: Bool = eq_nat(zero, one)
        let b5: Bool = (=)(zero, one)
        let b6: Bool = apply_binary[Nat]((=), zero, one)
        let b7: Bool = is_zero(one)
        "#,
    );

    env.bad(
        r#"
        type Nat: axiom
        let eq = (=)
        "#,
    );
}
