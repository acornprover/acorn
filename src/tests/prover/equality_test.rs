use crate::project::Project;
use crate::prover::Outcome;
use crate::tests::support::*;

// Equality-heavy prover regressions.

#[test]
fn test_proving_with_injectivity() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
            baz
        }

        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: Bool = axiom

        axiom rule1(x: Foo, y: Foo) {
            f(g(Foo.foo)) != f(g(Foo.bar))
        }

        axiom rule2(x: Foo, y: Foo) {
            f(g(Foo.foo)) != f(g(Foo.baz))
        }

        axiom rule3(x: Foo, y: Foo) {
            g(Foo.foo) = g(Foo.bar) or g(Foo.foo) = g(Foo.baz) or h
        }

        theorem goal {
            h
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(
        c.proof.unwrap(),
        vec![
            "g(Foo.baz) = g(Foo.foo) or g(Foo.foo) = g(Foo.bar)",
            "g(Foo.foo) != g(Foo.bar)",
            "g(Foo.baz) != g(Foo.foo)",
            "g(Foo.baz) = g(Foo.foo)"
        ]
    );
}

#[test]
fn test_proving_with_extensionality() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        type Foo: axiom

        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom
        let h: (Foo -> Foo, Foo -> Foo) -> Foo = axiom

        axiom rule1(x: Foo) {
            f(x) = g(x)
        }

        theorem goal {
            h(f, g) = h(g, f)
        }
        "#,
    );

    prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_with_unbalanced_extensionality() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        type Foo: axiom

        let f: (Foo, Foo) -> Foo = axiom
        let g: Foo = axiom
        let h: Foo -> Foo = axiom
        let p: (Foo -> Foo, Foo -> Foo) -> Foo = axiom

        axiom rule1(x: Foo) {
            f(g, x) = h(x)
        }

        theorem goal {
            p(f(g), h) = p(h, f(g))
        }
        "#,
    );

    prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_rewrite_into_obvious_falsehood() {
    // I think the tricky part here is that we have x != y and then rewrite x to y.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }

        let f: Foo -> Foo = axiom
        let g: Foo -> Foo = axiom

        axiom rule1(x: Foo, y: Foo) {
            f(f(g(Foo.foo))) != f(f(g(Foo.bar)))
        }

        theorem goal {
            g(Foo.foo) != g(Foo.bar)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_proving_multiple_simplifying() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            f(x)
        }

        axiom rule2 {
            f(Foo.foo) and f(Foo.bar) implies g(Foo.foo)
        }
            
        theorem goal {
            g(Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { f(x0) }(Foo.foo)",
            "function(x0: Foo) { f(x0) }(Foo.bar)",
            "not f(Foo.foo) or not f(Foo.bar)",
        ],
    );
}

#[test]
fn test_proving_of_existence() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Bool = axiom

        axiom rule {
            exists(x: Foo) {
                f(x)
            }
        }
            
        theorem goal {
            exists(x: Foo) {
                f(x)
            }
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert!(!proof.is_empty());
}

#[test]
fn test_proving_of_conjunction_existence() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom

        axiom rule {
            exists(x: Foo) {
                f(x) and g(x)
            }
        }
            
        theorem goal {
            exists(x: Foo) {
                f(x) and g(x)
            }
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert!(!proof.is_empty());
}

#[test]
fn test_proving_with_existential_witness() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Bool = axiom
        let g: (Foo, Foo) -> Bool = axiom

        axiom rule1(x: Foo) {
            f(x) implies exists(y: Foo) {
                g(x, y)
            }
        }
            
        theorem goal(x: Foo) {
            f(x) implies exists(y: Foo) {
                g(x, y)
            }
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_eq!(
        proof,
        vec!["function(x0: Foo) { not f(x0) or exists(k0: Foo) { g(x0, k0) } }(x)"]
    );
}

#[test]
fn test_proving_with_free_variable() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Bool = axiom
        let g: Bool = axiom

        axiom rule1(x: Foo) {
            f(x)
        }

        axiom rule2(x: Foo) {
            f(x) implies g
        }
            
        theorem goal {
            g
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { f(x0) }(Foo.bar)",
            "function(x0: Foo) { not f(x0) or g }(Foo.bar)",
            "function(x0: Foo) { not f(x0) }(Foo.bar)",
        ],
    );
}

#[test]
fn test_proving_plain_true() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"     
        theorem goal {
            true
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_proving_with_inheritance() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        typeclass F: Foo {
            foo_property: Bool
        }

        typeclass B: Bar extends Foo {
            bar_property: Bool
        }

        axiom bar_has_foo_property[B: Bar] {
            B.foo_property
        }

        typeclass Baz extends Bar {
            baz_property: Bool
        }

        theorem goal[B: Baz] {
            B.foo_property
        }
        "#,
    );

    // In non-poly mode, this is a passive contradiction with empty proof.
    // In poly mode, the axiom stays polymorphic and needs one instantiation step.
    // Either way, prove() verifies the certificate, so if it returns the proof is valid.
    prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_with_theorem_arg() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        typeclass T: Thing {
            add: (T, T) -> T

            add_comm(x: T, y: T) {
                x + y = y + x
            }

            add_assoc(x: T, y: T, z: T) {
                x + y + z = x + (y + z)
            }
        }

        theorem goal[T: Thing](a: T, b: T, c: T) {
            a + b + c = b + c + a
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function[T0: Thing](x0: T0, x1: T0, x2: T0) { x0 + x1 + x2 = x0 + (x1 + x2) }[T](a, b, c)",
            "function[T0: Thing](x0: T0, x1: T0) { x0 + x1 = x1 + x0 }[T](b + c, a)",
        ],
    );
}

#[test]
fn test_proving_with_duplicate_literals() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }

        let f: (Foo, Foo) -> Bool = axiom

        axiom rule1(x: Foo, y: Foo) {
            not f(x, y) or not f(y, x)
        }

        theorem goal {
            not f(Foo.foo, Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &["function(x0: Foo, x1: Foo) { not f(x0, x1) or not f(x1, x0) }(Foo.foo, Foo.foo)"],
    );
}

#[test]
fn test_proving_with_long_existential_definition() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom

        axiom rule {
            exists(y: Foo) {
                f(y) implies g(y) and h(y)
            }
        }
            
        theorem goal(x: Foo) {
            exists(y: Foo) {
                f(y) implies g(y) and h(y)
            } 
        }
        "#,
    );

    let _c = prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_using_unimported_function() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
        inductive Foo {
            foo
            bar
        }

        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            f(x) implies g(x)
        }

        axiom rule2(x: Foo) {
            g(x) implies h(x)
        }
        "#,
    );

    p.mock(
        "/mock/bar.ac",
        r#"
        from foo import Foo, f, h
        "#,
    );

    p.mock(
        "/mock/main.ac",
        r#"
        from bar import Foo, f, h

        theorem goal {
            f(Foo.foo) implies h(Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    let proof = c.proof.unwrap();
    assert_proof_lines(
        proof,
        &[
            "function(x0: Foo) { not lib(foo).g(x0) or h(x0) }(Foo.foo)",
            "function(x0: Foo) { not f(x0) or lib(foo).g(x0) }(Foo.foo)",
            "not lib(foo).g(Foo.foo)",
            "lib(foo).g(Foo.foo)",
        ],
    );
}

#[test]
fn test_proving_list_contains() {
    let text = r#"
        inductive List[T] {
            nil
            cons(T, List[T])
        }

        attributes List[T] {
            define contains(self, elem: T) -> Bool {
                match self {
                    List.nil {
                        false
                    }
                    List.cons(head, tail) {
                        if head = elem {
                            true
                        } else {
                            tail.contains(elem)
                        }
                    }
                }
            }
        }

        define finite_constraint[T](contains: T -> Bool) -> Bool {
            exists(superset: List[T]) {
                forall(x: T) {
                    contains(x) implies superset.contains(x)
                }
            }
        }

        theorem goal[T](ts: List[T]) {
            finite_constraint(ts.contains)
        }
        "#;

    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_proving_needing_templates() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        typeclass P: Pointed {
            origin: P
        }

        define foo[P: Pointed, Q: Pointed](x: P) -> Q {
            Q.origin
        }

        define is_const[T, U](f: T -> U) -> Bool {
            forall(x: T, y: T) {
                f(x) = f(y)
            }
        }

        theorem goal[P: Pointed, Q: Pointed] {
            is_const(foo[P, Q])
        }
        "#,
    );

    prove(&mut p, "main", "goal");
}

#[test]
fn test_core_proving_boolean_equality() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        let a: Bool = axiom
        let b: Bool = axiom

        axiom rule1 {
            a implies b
        }

        axiom rule2 {
            b implies a
        }

        theorem goal {
            a = b
        }
        "#,
    );

    prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_functional_structure_identity() {
    let text = r#"
        type Foo: axiom

        structure Bar {
            value: Foo -> Foo
        }

        let a: Bar = axiom
        let b: Bar = axiom

        axiom rule1 {
            a.value = b.value
        }

        theorem goal {
            a = b
        }
        "#;

    verify_succeeds(text);
}

/// Test that extensionality works without requiring a witness for uninhabited types.
///
/// This test uses a structure wrapper so that the proof MUST use extensionality.
/// The axiom `a.value = b.value` normalizes to `a.value(x) = b.value(x)`.
/// The goal `a = b` requires proving the structures are equal, which requires:
/// 1. Using extensionality to derive `a.value = b.value` from `a.value(x) = b.value(x)`
/// 2. Using the structure identity axiom to conclude `a = b`
///
/// Importantly, Elem is uninhabited (an axiom type with no constructors), so the prover
/// cannot instantiate x with a concrete value. Extensionality must work on the
/// universally quantified clause directly.
#[test]
fn test_extensionality_without_witness_for_uninhabited_type() {
    let text = r#"
        // Elem is uninhabited - it's an axiom type with no constructors
        type Elem: axiom

        // A wrapper structure containing a function over Elem
        structure Wrapper {
            value: Elem -> Elem
        }

        let a: Wrapper = axiom
        let b: Wrapper = axiom

        // Axiom that a.value = b.value (normalizes to a.value(x) = b.value(x))
        axiom values_equal {
            a.value = b.value
        }

        // Goal: prove a = b (requires extensionality to derive a.value = b.value first)
        theorem goal {
            a = b
        }
        "#;

    verify_succeeds(text);
}

#[test]
fn test_proving_implied_boolean_equality() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        let f: Bool -> Bool = axiom

        axiom rule1 {
            a implies (b = c)
        }

        axiom rule2 {
            a
        }

        theorem goal {
            f(b) = f(c)
        }
        "#,
    );

    prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_typical_functional_equality_shape() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        type Nat: axiom
        let f: (Nat, Nat) -> Nat = axiom
        let g: (Nat, Nat) -> Nat = axiom

        axiom results_equal(a: Nat, b: Nat) {
            f(a, b) = g(a, b)
        }

        theorem goal {
            f = g
        }
        "#,
    );

    prove(&mut p, "main", "goal");
}

#[test]
fn test_proving_and_inside_arg() {
    // The boxed_and definition can't be normalized to CNF directly.
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        structure BoxedBool {
            value: Bool
        }

        define boxed_and(a: BoxedBool, b: BoxedBool) -> BoxedBool {
           BoxedBool.new(a.value and b.value)
        }

        theorem boxed_and_true_true {
            boxed_and(BoxedBool.new(true), BoxedBool.new(true)) = BoxedBool.new(true)
        }
        "#,
    );

    prove(&mut p, "main", "boxed_and_true_true");
}

#[test]
fn test_verify_reflexivity() {
    verify_succeeds(
        r#"
        define is_reflexive[T](f: (T, T) -> Bool) -> Bool {
            forall(t: T) {
                f(t, t)
            }
        }
            
        define lte_from[T](lt: (T, T) -> Bool, x: T, y: T) -> Bool {
            lt(x, y) or x = y    
        }
            
        theorem lte_is_reflexive[T](lt: (T, T) -> Bool) {
            is_reflexive(lte_from(lt))
        } by {
            forall(x: T) {
                x = x
                lte_from(lt)(x, x)
            }
        }
        "#,
    );
}

// This test exercises a bug where rewrite patterns with variables that get renumbered
// during normalization would cause certificate creation to fail. The bug was that
// RewriteInfo stored the pre-normalization literal but used the post-normalization
// context, causing variable lookup failures.
//
// The pattern axiom `g(x, y) = g(y, x)` has two variables. When the rewritten literal
// only uses y (which becomes x0 after normalization), certificate reconstruction must
// use the correct context that matches the pre-normalization variable numbering.
#[test]
fn test_rewrite_with_variable_renumbering() {
    // The key is having a pattern where not all variables appear in the result,
    // causing normalization to renumber them. Here g(x, y) = g(y, x) is symmetric,
    // and the proof will use rewrites that exercise variable mapping.
    let text = r#"
        axiom g_sym(x: Thing, y: Thing) { g(x, y) = g(y, x) }
        axiom h_of_g_t { h(g(t, t2)) = t }
        theorem goal { h(g(t2, t)) = t }
    "#;
    // This uses verify_succeeds which calls make_cert and check_cert,
    // exercising the full certificate creation path including the Rewrite rule handling.
    verify_succeeds(&format!("{}\n{}", THING, text));
}
