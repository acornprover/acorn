// Tests for the "attributes" keyword and class/member functionality.
// These tests check parsing and typechecking of attributes blocks, member functions,
// and related features like self parameters and magic methods.

use crate::elaborator::environment::Environment;

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
fn test_param_on_member_function() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure BoolPair {
            first: Bool
            second: Bool
        }
        "#,
    );
    env.add(
        r#"
        attributes BoolPair {
            define apply_first<T>(self, f: Bool -> T) -> T {
                f(self.first)
            }
        }

        theorem type_attr_syntax(b: BoolPair, f: Bool -> Bool) {
            BoolPair.apply_first(b, f) = f(b.first)
        }

        theorem obj_attr_syntax(b: BoolPair, f: Bool -> Bool) {
            b.apply_first(f) = f(b.first)
        }

        let bp: BoolPair = axiom
        "#,
    );

    // Unresolved type
    env.bad("let g = bp.apply_first");
}

#[test]
fn test_env_attribute_with_extra_type_param() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure Pair<T, U> {
            first: T
            second: U
        }

        attributes Pair<T, U> {
            define map_first<V>(self, f: T -> V) -> V {
                f(self.first)
            }
        }

        theorem type_attr_syntax<A, B, C>(p: Pair<A, B>, f: A -> C) {
            Pair.map_first(p, f) = f(p.first)
        }

        theorem obj_attr_syntax<A, B, C>(p: Pair<A, B>, f: A -> C) {
            p.map_first(f) = f(p.first)
        }

        type Nat: axiom
        let zero: Nat = axiom
        let p = Pair.new(zero, zero)
        "#,
    );

    // Unresolved type
    env.bad("let f = p.map_first");
}

#[test]
fn test_env_attributes_must_provide_all_params() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Pair<T, U> {
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
fn test_attribute_let_satisfy_exports_names() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            define foo(x: Nat) -> Bool { axiom }
            attributes Nat {
                let z: Nat satisfy { foo(z) }
            }
            theorem goal {
                foo(Nat.z)
            } by {
                foo(Nat.z)
            }
        "#,
    );
}

#[test]
fn test_attribute_function_satisfy_statement() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom
            attributes Nat {
                let flip(a: Bool) -> b: Bool satisfy {
                    a != b
                }
            }
            theorem goal(a: Bool) {
                Nat.flip(a) != a
            } by {
                Nat.flip(a) != a
            }
        "#,
    );
}

#[test]
fn test_generic_attribute_with_let_satisfy() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Box[T] {
                item: T
            }
            let can_pick[T]: T -> Bool = axiom
            attributes Box[T] {
                let witness: T satisfy {
                    can_pick[T](witness)
                }
            }
        "#,
    );
}

#[test]
fn test_specific_attribute_with_let_satisfy() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive Color {
                red
                blue
            }
            structure Box[T] {
                item: T
            }
            let is_primary: Color -> Bool = axiom
            attributes Box[Color] {
                let witness: Color satisfy {
                    is_primary(witness)
                }
            }
        "#,
    );
}

#[test]
fn test_generic_attribute_let_satisfy_disallows_extra_type_params() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Box[T] {
                item: T
            }
        "#,
    );
    env.bad(
        r#"
            attributes Box[T] {
                let witness[U]: U satisfy {
                    true
                }
            }
        "#,
    );
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
    // But we need this syntax to work for typeclasses anyway.
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
fn test_env_recursive_attribute() {
    // This tests that recursive generic attribute functions have the correct number of type parameters.
    // When an attribute function on List<T> has its own type parameter <U>, the recursive reference
    // should have both T and U parameters, not just U.
    let mut env = Environment::test();
    env.add(
        r#"
        inductive List<T> {
            nil
            cons(T, List<T>)
        }

        attributes List<T> {
            define map<U>(self, f: T -> U) -> List<U> {
                match self {
                    List.nil {
                        List.nil<U>
                    }
                    List.cons(head, tail) {
                        List.cons(f(head), tail.map(f))
                    }
                }
            }
        }
        "#,
    );
}

#[test]
fn test_env_infix_with_extra_param() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive List<T> {
            nil
            cons(T, List<T>)
        }

        attributes List<T> {
            define mul<U>(self, f: T -> U) -> List<U> {
                match self {
                    List.nil {
                        List.nil<U>
                    }
                    List.cons(head, tail) {
                        List.cons(f(head), tail.mul(f))
                    }
                }
            }
        }

        define function1<T, U>(items: List<T>, f: T -> U) -> List<U> {
            items * f
        }

        theorem theorem1<T, U>(items: List<T>, f: T -> List<U>, items_1: List<List<U>>) {
            items.mul(f) = items_1
        }

        define function2<T, U>(items: List<T>, f: T -> List<U>, items_1: List<List<U>>) -> Bool {
            items.mul(f) = items_1
        }

        theorem theorem2<T, U>(items: List<T>, f: T -> U, g: U -> U, items_1: List<U>) {
            (items * f) * g = items_1
        }
        "#,
    );
}

#[test]
fn test_env_set_product_with_extra_type_param() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure Set[K] {
            contains: K -> Bool
        }
        structure Pair[K1, K2] {
            first: K1
            second: K2
        }
        define elem_in_product[K1,K2](a1: Set[K1], a2: Set[K2], p: Pair[K1,K2]) -> Bool {
            a1.contains(p.first) and a2.contains(p.second)
        }
        attributes Set[K1] {
            define mul[K2](self, a: Set[K2]) -> Set[Pair[K1,K2]] {
                Set[Pair[K1,K2]].new(elem_in_product(self, a))
            }
        }
        theorem foo_3[K1, K2](a1: Set[K1], a2: Set[K2]) {
            a1.mul(a2) = a1 * a2
        }
        theorem foo_4[K1, K2](a1: Set[K1], a2: Set[K2]) {
            a1 * a2 = a1.mul(a2)
        }
        theorem foo_5[K, L](a: Set[K], b1: Set[L], b2: Set[L]) {
            a.mul(b1).mul(b2) = a.mul(b1).mul(b2)
        }
        theorem foo_6[K](a: Set[K], b: Set[K]) {
            a.mul(b) = a.mul(b)
        }
        "#,
    );
}

#[test]
fn test_env_attribute_with_specific_parameter() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        attributes Set[Color] {
            define has_red(self) -> Bool {
                self.contains(Color.red)
            }
        }
        "#,
    );
}

#[test]
fn test_multiple_specific_parametrizations() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        structure Set[K] {
            contains: K -> Bool
        }

        attributes Set[Color] {
            define has_red(self) -> Bool {
                self.contains(Color.red)
            }
        }

        attributes Set[Size] {
            define has_small(self) -> Bool {
                self.contains(Size.small)
            }
        }
        "#,
    );
}

#[test]
fn test_error_on_mixed_params() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Pair[T, U] {
            first: T
            second: U
        }
        "#,
    );
    env.bad(
        r#"
        attributes Pair[Color, U] {
            define foo(self) -> Bool { true }
        }
        "#,
    );
}

#[test]
fn test_error_on_conflicting_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        attributes Set[K] {
            define foo(self) -> Bool { true }
        }
        "#,
    );
    env.bad(
        r#"
        attributes Set[Color] {
            define foo(self) -> Bool { false }
        }
        "#,
    );
}

#[test]
fn test_nested_specific_parametrization() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive List[T] {
            nil
            cons(T, List[T])
        }
        structure Set[K] {
            contains: K -> Bool
        }

        attributes Set[List[Color]] {
            define check_colors(self) -> Bool {
                true  // simplified for testing
            }
        }
        "#,
    );
}

#[test]
fn test_double_nested_parametrization() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        inductive List[T] {
            nil
            cons(T, List[T])
        }
        structure Set[K] {
            contains: K -> Bool
        }
        structure Map[K, V] {
            get: K -> V
        }

        attributes Map[List[Color], Set[Size]] {
            define complex_method(self) -> Bool {
                true
            }
        }
        "#,
    );
}

#[test]
fn test_specific_attribute_type_checking() {
    // Test that attributes defined on List[Color] don't work on List[Size]
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        inductive List[T] {
            nil
            cons(T, List[T])
        }

        attributes List[Color] {
            define has_red(self) -> Bool {
                axiom
            }
        }

        let color_list: List[Color] = axiom
        let size_list: List[Size] = axiom

        theorem test_color {
            color_list.has_red
        }
        "#,
    );

    // This should fail - List[Size] doesn't have has_red
    env.bad(
        r#"
        theorem test_size {
            size_list.has_red
        }
        "#,
    );
}

#[test]
fn test_specific_vs_generic_attributes() {
    // Test that generic attributes work on all types but specific ones only on the right type
    let mut env = Environment::test();

    // First test: just the generic attributes
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        inductive List[T] {
            nil
            cons(T, List[T])
        }

        attributes List[T] {
            define generic_method(self) -> Bool {
                axiom
            }
        }

        let color_list: List[Color] = axiom
        let size_list: List[Size] = axiom

        // Generic method should work on both
        theorem test_generic_color {
            color_list.generic_method
        }

        theorem test_generic_size {
            size_list.generic_method
        }
        "#,
    );

    // Now add specific attributes
    env.add(
        r#"
        attributes List[Color] {
            define color_specific(self) -> Bool {
                axiom
            }
        }

        // Specific method should only work on List[Color]
        theorem test_specific_color {
            color_list.color_specific
        }
        "#,
    );

    // This should fail - List[Size] doesn't have color_specific
    env.bad(
        r#"
        theorem test_specific_size {
            size_list.color_specific
        }
        "#,
    );
}

#[test]
fn test_nested_type_mismatch() {
    // Test that Set[List[Color]] attributes don't work on Set[List[Size]]
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        inductive List[T] {
            nil
            cons(T, List[T])
        }
        structure Set[K] {
            contains: K -> Bool
        }

        attributes Set[List[Color]] {
            define check_colors(self) -> Bool {
                axiom
            }
        }

        let color_set: Set[List[Color]] = axiom
        let size_set: Set[List[Size]] = axiom

        // Should work on Set[List[Color]]
        theorem test_color_set {
            color_set.check_colors
        }
        "#,
    );

    // Should fail on Set[List[Size]]
    env.bad(
        r#"
        theorem test_size_set {
            size_set.check_colors
        }
        "#,
    );
}
