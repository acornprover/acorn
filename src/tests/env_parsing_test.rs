// Tests for environment parsing.
// These tests only check whether code parses correctly or produces parse errors.
// They use only env.add() and env.bad() methods, without checking types or values.

use crate::environment::Environment;

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
fn test_structure_cant_contain_itself() {
    // If you want a type to contain itself, it has to be inductive, not a structure.
    let mut env = Environment::test();
    env.bad(
        r#"
        structure InfiniteBools {
            head: Bool
            tail: InfiniteBools
        }
        "#,
    );
}

#[test]
fn test_inductive_statements_must_have_base_case() {
    let mut env = Environment::test();
    env.bad(
        r#"
        inductive Nat {
            suc(Nat)
        }"#,
    );
}

#[test]
fn test_no_russell_paradox() {
    let mut env = Environment::test();
    env.bad(
        r#"
        structure NaiveSet {
            set: NaiveSet -> Bool 
        }
        "#,
    );
}

#[test]
fn test_template_typechecking() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.add("define eq[T](a: T, b: T) -> Bool { a = b }");
    env.add("theorem t1 { eq(zero, zero) }");
    env.add("theorem t2 { eq(zero = zero, zero = zero) }");
    env.add("theorem t3 { eq(zero = zero, eq(zero, zero)) }");
    env.bad("theorem t4 { eq(zero, zero = zero) }");
    env.bad("theorem t5 { zero = eq(zero, zero) }");
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
fn test_functional_definition_typechecking() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("define foo(f: Nat -> Nat) -> Bool { function(x: Nat) { true } }");
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
fn test_undefined_class_name() {
    let mut env = Environment::test();
    env.bad("attributes Foo {}");
}

#[test]
fn test_no_methods_on_type_aliases() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("type NatFn: Nat -> Nat");
    env.bad("attributes NatFn {}");
}

#[test]
fn test_first_arg_must_be_self() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad(
        r#"
            attributes Nat {
                define add(a: Nat, b: Nat) -> Nat { axiom }
            }
            "#,
    );
}

#[test]
fn test_no_self_variables() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let foo: Bool = exists(self) { true }");
    env.bad("let foo: Bool = forall(self) { true }");
    env.bad("let self: Nat = axiom");
}

#[test]
fn test_no_self_args_outside_class() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("define foo(self) -> Bool { true }");
}

#[test]
fn test_no_self_as_forall_arg() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("forall(self) { true }");
}

#[test]
fn test_no_self_as_exists_arg() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("exists(self) { true }");
}

#[test]
fn test_no_self_as_lambda_arg() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("let f: Nat -> Bool = lambda(self) { true }");
}

#[test]
fn test_self_must_have_correct_type() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad(
        r#"
            attributes Nat {
                define add(self: Bool, other: Nat) -> Nat { axiom }
            }
        "#,
    );
}

#[test]
fn test_no_defining_new() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad(
        r#"
            attributes Nat {
                define new(self: Bool, other: Nat) -> Bool { true }
            }
        "#,
    );
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
fn test_digits_must_be_correct_type() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad(
        r#"
            attributes Nat {
                let 1: Bool = axiom
            }
        "#,
    );
}

#[test]
fn test_read_must_have_correct_args() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad(
        r#"
            attributes Nat {
                let 1: Nat = axiom
                define suc(self) -> Nat: axiom
                define read(self, digit: Bool) -> Nat: Nat.1
            }
        "#,
    );
}

#[test]
fn test_read_must_return_correct_type() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad(
        r#"
            attributes Nat {
                let 1: Nat = axiom
                define suc(self) -> Nat: axiom
                define read(self, digit: Nat) -> Bool: true
            }
        "#,
    );
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
fn test_structure_with_bad_constraint() {
    let mut env = Environment::test();
    env.bad(
        r#"
            structure Thing {
                foo: Bool
                baz: Bool
                bar: Bool
            } constraint {
                foo or qux
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
fn test_cant_reuse_type_param_name() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
        "#,
    );

    // Reusing in a different scope is fine.
    env.add(
        r#"
            structure Pair2[T, U] {
                first: T
                second: U
            }
        "#,
    );

    // Reusing a global name is not.
    env.bad(
        r#"
            structure T[Pair, U] {
                first: Pair
                second: U
            }
        "#,
    );
}

#[test]
fn test_no_params_on_member_functions() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure BoolPair {
                first: Bool
                second: Bool
            }
            "#,
    );
    env.bad(
        r#"
            attributes BoolPair {
                define apply_first[T](self, f: Bool -> T) -> T {
                    f(self.first)
                }
            }
            "#,
    );
}

#[test]
fn test_class_with_mismatched_num_params() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    env.bad(
        r#"
            attributes Pair[T] {
                let t: Bool = true
            }
            "#,
    );
}

#[test]
fn test_structures_cant_reuse_param_names() {
    let mut env = Environment::test();
    env.bad(
        r#"
            structure Pair[T, T] {
                first: T
                second: T
            }
            "#,
    );
}

#[test]
fn test_struct_params_leave_scope() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    env.bad(
        r#"
            let f: T -> T = function(t: T) { t }
            "#,
    );
}

#[test]
fn test_class_params_leave_scope() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    env.add(
        r#"
            attributes Pair[T, U] {
                let t: T = axiom
                let u: U = axiom
            }
            "#,
    );
    env.bad(
        r#"
            let f: T -> T = function(t: T) { t }
            "#,
    );
}

#[test]
fn test_no_templated_define_inside_proof() {
    // This doesn't work correctly right now, so let's forbid it.
    let mut env = Environment::test();
    env.add(
        r#"
            theorem bar {
                true
            } by {
                define foo(x: Bool) -> Bool {
                    true
                }
            }
            "#,
    );

    env.bad(
        r#"
            theorem baz[T] {
                forall(x: T) {
                    true
                }
            } by {
                define qux[U](x: U) -> Bool {
                    true
                }
            }
            "#,
    );
}

#[test]
fn test_handling_functional_type_mismatch() {
    // This is a repro of a bug that crashed the released language server.
    let mut env = Environment::test();
    env.add(
        r#"
            type Foo: axiom
            type Bar: axiom

            let is_cut: (Foo -> Bool) -> Bool = axiom
            let liftable: (Foo -> Bar) -> Bool = axiom
            let lift_gt_rat: (Foo -> Bar, Bar, Foo) -> Bool = axiom
        "#,
    );
    // This is not valid, but it shouldn't cause a panic
    env.bad(
        r#"
            theorem lift_gt_rat_is_cut(f: Foo -> Bar) {
                liftable(f) implies is_cut(lift_gt_rat(f))
            }
        "#,
    );
}

#[test]
fn test_proposition_must_typecheck_as_bool() {
    // The Real.bar(foo) line should cause it to fail.
    let mut env = Environment::test();
    env.add(
        r#"
            type Real: axiom
            attributes Real {
                define foo(self) -> Real {
                    axiom
                }
                let bar: Real -> Real = axiom
            }
        "#,
    );
    env.bad(
        r#"
            theorem goal(a: Real, eps: Real) {
                eps = a implies eps.foo.foo = a.foo
            } by {
                eps.foo = a.foo
                Real.bar(eps)
            }
        "#,
    );
}

#[test]
fn test_let_type_inference() {
    let mut env = Environment::test();
    env.add("let a = true\n");
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
fn test_nat_ac_together() {
    let mut env = Environment::test();
    env.add(
        r#"
// The axioms of Peano arithmetic.
        
type Nat: axiom

let zero: Nat = axiom

let suc: Nat -> Nat = axiom
let one: Nat = suc(zero)

axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }

axiom suc_neq_zero(x: Nat) { suc(x) != zero }

axiom induction(f: Nat -> Bool) { f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) } }

// The old version. In the modern codebase these are parametric.
define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }
axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }
axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) { recursion(f, a, suc(n)) = f(recursion(f, a, n)) }

define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }

// Now let's have some theorems.

theorem add_zero_right(a: Nat) { add(a, zero) = a }

theorem add_zero_left(a: Nat) { add(zero, a) = a }

theorem add_suc_right(a: Nat, b: Nat) { add(a, suc(b)) = suc(add(a, b)) }

theorem add_suc_left(a: Nat, b: Nat) { add(suc(a), b) = suc(add(a, b)) }

theorem add_comm(a: Nat, b: Nat) { add(a, b) = add(b, a) }

theorem add_assoc(a: Nat, b: Nat, c: Nat) { add(add(a, b), c) = add(a, add(b, c)) }
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
}

#[test]
fn test_structure_new_definition() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure BoolPair {
            first: Bool
            second: Bool
        }
        theorem goal(p: BoolPair) {
            p = BoolPair.new(BoolPair.first(p), BoolPair.second(p))
        }
        "#,
    );
}

#[test]
fn test_inductive_new_definition() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        theorem goal(n: Nat) {
            n = Nat.zero or exists(k: Nat) { n = Nat.suc(k) }
        }
        "#,
    );
}

#[test]
fn test_inductive_constructor_can_be_member() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        theorem goal(n: Nat) {
            n = Nat.zero or exists(k: Nat) { n = k.suc }
        }
        "#,
    );
}

#[test]
fn test_match_based_definition() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz(Bool)
            }

            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar(b) {
                        b
                    }
                    Foo.baz(b) {
                        not b
                    }
                }
            }
        "#,
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
fn test_match_value_pattern_must_be_constructor() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }
            
            attributes Foo {
                define qux(self, b: Bool) -> Foo {
                    Foo.baz
                }
            }
            "#,
    );
    env.bad(
        r#"
            define foo(f: Foo) -> Bool {
                match f {
                    Foo.bar(b) {
                        b
                    }
                    Foo.qux {
                        false
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_match_value_statement_must_be_constructor() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Foo {
                bar(Bool)
                baz
            }
            
            attributes Foo {
                define qux(self, b: Bool) -> Foo {
                    Foo.baz
                }
            }
            "#,
    );
    env.bad(
        r#"
            forall (f: Foo) {
                match f {
                    Foo.bar(b) {
                        b
                    }
                    Foo.qux {
                        false
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
fn test_left_recursive_definition() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            define add(a: Nat, b: Nat) -> Nat {
                match a {
                    Nat.zero {
                        b
                    }
                    Nat.suc(pred) {
                        add(pred, b).suc
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_right_recursive_definition() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            define add(a: Nat, b: Nat) -> Nat {
                match b {
                    Nat.zero {
                        a
                    }
                    Nat.suc(pred) {
                        add(a, pred).suc
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_no_recursive_simple_infinite_loops() {
    let mut env = Environment::test();
    env.bad(
        r#"
            define loop(a: Bool) -> Bool {
                not loop(a)
            }
            "#,
    )
}

#[test]
fn test_no_recursive_complicated_infinite_loops() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            "#,
    );

    // This would infinite loop because it hits a different branch each time.
    env.bad(
        r#"
            define loop(a: Nat, b: Nat, c: Bool) -> Bool {
                if c {
                    match a {
                        Nat.zero {
                            false
                        }
                        Nat.suc(pred) {
                            not loop(pred, b.suc, false)
                        }
                    }
                } else {
                    match b {
                        Nat.zero {
                            false
                        }
                        Nat.suc(pred) {
                            loop(a.suc, pred, true)
                        }
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_templated_recursive_function() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            define repeat[T](n: Nat, f: T -> T, a: T) -> T {
                match n {
                    Nat.zero {
                        a
                    }
                    Nat.suc(pred) {
                        repeat(pred, f, f(a))
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_termination_checker_catches_functional_cheating() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            define apply(f: Nat -> Bool, n: Nat) -> Bool {
                f(n)
            }
            "#,
    );
    env.bad(
        r#"
            define cheat(n: Nat) -> Bool {
                not apply(cheat, n)
            }
            "#,
    );
}

#[test]
fn test_left_recursive_member_function() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    match self {
                        Nat.zero {
                            other
                        }
                        Nat.suc(pred) {
                            pred.add(other).suc
                        }
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_right_recursive_member_function() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Nat {
                zero
                suc(Nat)
            }

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    match other {
                        Nat.zero {
                            self
                        }
                        Nat.suc(pred) {
                            self.add(pred).suc
                        }
                    }
                }
            }
        "#,
    );
}

#[test]
fn test_class_variables() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                let zero: Nat = axiom
                let 1: Nat = axiom
            }

            axiom zero_neq_one(x: Nat) { Nat.zero = Nat.1 }
        "#,
    );

    // Attributes shouldn't get bound at module scope
    env.bad("let alsozero: Nat = zero");
}

#[test]
fn test_instance_methods() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define add(self, other: Nat) -> Nat { axiom }
            }
        "#,
    );
}

#[test]
fn test_using_member_function() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define add(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) {
                a.add(b) = b.add(a)
            }
        "#,
    );
}

#[test]
fn test_infix_add() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define add(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a + b = b + a }
        "#,
    );
}

#[test]
fn test_infix_sub() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define sub(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a - b = b - a }
        "#,
    );
}

#[test]
fn test_infix_mul() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define mul(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a * b = b * a }
        "#,
    );
}

#[test]
fn test_infix_div() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define div(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a / b = b / a }
        "#,
    );
}

#[test]
fn test_infix_mod() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define mod(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a % b = b % a }
        "#,
    );
}

#[test]
fn test_infix_lt() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define lt(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a < b = b < a }
        "#,
    );
}

#[test]
fn test_infix_gt() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define gt(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a > b = b > a }
        "#,
    );
}

#[test]
fn test_infix_lte() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define lte(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a <= b = b <= a }
        "#,
    );
}

#[test]
fn test_infix_gte() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define gte(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a >= b = b >= a }
        "#,
    );
}

#[test]
fn test_prefix_neg() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                define neg(self) -> Nat { axiom }
            }
            theorem goal(a: Nat) { -a = a }
        "#,
    );
}

#[test]
fn test_no_dot_new() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            structure NatPair {
                first: Nat
                second: Nat
            }
        "#,
    );
    env.bad("theorem goal(p: NatPair): p.new = p.new");
}

#[test]
fn test_no_using_methods_with_mismatched_self() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            attributes Nat {
                let foo: Bool -> Bool = function(b: Bool) { b }
            }
        "#,
    );
    env.bad("theorem goal: zero.foo(true)");
}

#[test]
fn test_multi_digit_unary() {
    let mut env = Environment::test();
    env.add("type Unary: axiom");
    env.add(
        r#"
            attributes Unary {
                let 1: Unary = axiom 
                define suc(self) -> Unary { axiom }
                define read(self, digit: Unary) -> Unary { self.suc }
            }
        "#,
    );
    env.add("numerals Unary");
    env.add("let two: Unary = 11");
}

#[test]
fn test_generic_structure() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
        "#,
    );
}

#[test]
fn test_generic_class_statement() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            attributes Pair[T, U] {
                define swap(self) -> Pair[U, T] {
                    Pair.new(self.second, self.first)
                }
            }
        "#,
    );
}

#[test]
fn test_aliases_for_generics() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    env.add(
        r#"
            type BoolPair: Pair[Bool, Bool]
            let truetrue: BoolPair = Pair.new(true, true)
            "#,
    );
}

#[test]
fn test_theorem_with_instantiated_arg_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    env.add(
        r#"
            theorem goal(p: Pair[Bool, Bool]) {
                p.first = p.second or p.first = not p.second
            }
            "#,
    );
}

#[test]
fn test_methods_on_generic_classes() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Foo: axiom
            type Bar: axiom
            structure Pair[T, U] {
                first: T
                second: U
            }
            let f: Foo = axiom
            let b: Bar = axiom
            let p1: Pair[Foo, Bar] = Pair.new(f, b)
            let p2: Pair[Foo, Bar] = Pair[Foo, Bar].new(f, b)
            "#,
    );

    // Originally this intentionally didn't work.
    // But need this syntax to work for typeclasses anyway.
    env.add(
        r#"
            let p3: Pair[Foo, Bar] = Pair.new[Foo, Bar](f, b)
            "#,
    );
}

#[test]
fn test_generic_return_types() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Foo: axiom
            type Bar: axiom
            structure Pair[T, U] {
                first: T
                second: U
            }
            
            attributes Pair[T, U] {
                define swap(self) -> Pair[U, T] {
                    Pair.new(self.second, self.first)
                }
            }

            let s: Pair[Foo, Bar] -> Pair[Bar, Foo] = Pair[Foo, Bar].swap
            let f: Foo = axiom
            let b: Bar = axiom
            let p1: Pair[Foo, Bar] = Pair.new(f, b)
            let p2: Pair[Bar, Foo] = p1.swap
            let p3: Pair[Foo, Bar] = p2.swap
            let p4: Pair[Foo, Bar] = p1.swap.swap
            "#,
    );
}

#[test]
fn test_aliasing_a_generic_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
    );
    env.add(
        r#"
            type Pair2: Pair
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
fn test_nested_functional_values() {
    let mut env = Environment::test();
    env.add(
        r#"
            define both(f: Bool -> Bool) -> Bool {
                f(true) and f(false)
            }

            let both2: (Bool -> Bool) -> Bool = both

            define or2(a: Bool, b: Bool) -> Bool {
                a or b
            }

            let or3: (Bool, Bool) -> Bool = or2
            // let or4: Bool -> Bool -> Bool = or3
        "#,
    );
}

#[test]
fn test_param_looking_thing() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom

            attributes Nat {
                let 0: Nat = axiom
                let 1: Nat = axiom
                let from_bool: Bool -> Nat = axiom
                define lt(self, other: Nat) -> Bool {
                    axiom
                }
            }

            theorem foo {
                Nat.from_bool(false) < Nat.from_bool(true)
            }
        "#,
    );
}

#[test]
fn test_params_with_arg_application() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom

            define maps_to[T, U](f: T -> U, u: U) -> Bool {
                exists(t: T) {
                    f(t) = u
                }
            }

            define not2(b: Bool) -> Bool {
                not b
            }

            theorem foo {
                maps_to[Bool, Bool](not2, false)
            }
        "#,
    );
}

#[test]
fn test_inline_function_in_forall_block() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.add("let suc: Nat -> Nat = axiom");
    env.add(
            r#"
            axiom induction(f: Nat -> Bool) {
                f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) }
            }
            "#,
        );
    env.add(
        r#"
            forall(f: (Nat, Bool) -> Bool) {
                induction(function(x: Nat) { f(x, true) })
            }
        "#,
    );
}

#[test]
fn test_partial_application() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.add("define add3(a: Nat, b: Nat, c: Nat) -> Nat { axiom }");
    env.add("let add0: (Nat, Nat) -> Nat = add3(zero)");
    env.add("let add00: Nat -> Nat = add3(zero, zero)");
    env.add("let add00_alt: Nat -> Nat = add0(zero)");
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
