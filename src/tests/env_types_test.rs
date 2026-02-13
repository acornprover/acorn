// Tests for type system features.
// These tests check structures, inductives, generics, type parameters, and type constraints.

use crate::elaborator::environment::{Environment, LineType};

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
fn test_inductive_negative_occurrence_basic() {
    let mut env = Environment::test();
    env.bad(
        r#"
        inductive Bad {
            base
            rec(Bad -> Bool)
        }
        "#,
    );
}

#[test]
fn test_inductive_negative_occurrence_in_generic() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure Set[T] {
            contains: T -> Bool
        }
        "#,
    );
    env.bad(
        r#"
        inductive Bad {
            base
            rec(Set[Bad])
        }
        "#,
    );
}

#[test]
fn test_inductive_negative_occurrence_through_wrapper() {
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
        inductive Bad {
            base
            rec(Box[Bad -> Bool])
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
fn test_functional_definition_typechecking() {
    let mut env = Environment::test();
    env.add("type Nat: axiom");
    env.bad("define foo(f: Nat -> Nat) -> Bool { function(x: Nat) { true } }");
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
            structure PairHolder[Pair, U] {
                first: Pair
                second: U
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
fn test_let_type_inference() {
    let mut env = Environment::test();
    env.add("let a = true\n");
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
fn test_type_params_cleaned_up() {
    let mut env = Environment::test();
    env.add("define foo[T](a: T) -> Bool { axiom }");
    assert!(env.bindings.get_type_for_typename("T").is_none());
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
fn test_structure_new_option_syntax() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Option[T] {
            none
            some(T)
        }

        structure Thing {
            foo: Bool
        } constraint {
            foo
        }

        let condition: Bool = Thing.constraint(true)
        let value: Option[Thing] = Thing.new_option(true)
        "#,
    );
}

#[test]
fn test_typechecking_try_option() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Option[T] {
            none
            some(T)
        }

        let foo: Option[Bool] = Option.some(true)
        let bar: Bool = foo?
        "#,
    );
}

#[test]
fn test_typechecking_try_bool_fails() {
    let mut env = Environment::test();
    env.bad("let foo: Bool = true?");
}

#[test]
fn test_functional_type_inference() {
    // Type inference should unify A -> (B -> C) with E -> F by setting E = A and F = B -> C.
    // This works because un-curried function types are re-curried during unification.
    let mut env = Environment::test();
    env.add(
        r#"
        define compose[T, U, V](f: U -> V, g: T -> U) -> T -> V {
            function(t: T) {
                f(g(t))
            }
        }

        theorem goal[T, V](f: (T -> V) -> V, g: T -> (T -> V)) {
            compose(f, g) = compose(f, g)
        }
        "#,
    );
}

#[test]
fn test_nested_contravariant_structure() {
    let mut env = Environment::test();

    // Define Set with T in contravariant position
    env.add(
        r#"
        structure Set[T] {
            contains: T -> Bool
        }
        "#,
    );

    // Define Wrapper that wraps Set (should make U contravariant in Wrapper)
    env.add(
        r#"
        structure Wrapper[U] {
            field: Set[U]
        }
        "#,
    );

    // This should be rejected (Bad appears in negative position via Set)
    env.bad(
        r#"
        inductive Bad {
            base
            rec(Wrapper[Bad])
        }
        "#,
    );
}
