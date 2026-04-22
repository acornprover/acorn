use crate::prover::Outcome;
use crate::tests::support::*;

// General prover coverage for language features.

#[test]
fn test_structure_new_equation() {
    let text = r#"
    structure Pair {
        first: Bool
        second: Bool
    }
    theorem goal(p: Pair) { p = Pair.new(Pair.first(p), Pair.second(p)) }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_structure_first_member_equation() {
    let text = r#"
    structure Pair {
        first: Bool
        second: Bool
    }
    theorem goal(a: Bool, b: Bool) { Pair.first(Pair.new(a, b)) = a }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_structure_second_member_equation() {
    let text = r#"
    structure Pair {
        first: Bool
        second: Bool
    }
    theorem goal(a: Bool, b: Bool) { Pair.second(Pair.new(a, b)) = b }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_inductive_no_confusion_property() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }
    theorem goal(a: Nat) { Nat.suc(a) != Nat.zero }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_inductive_canonical_form_principle() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }
    theorem goal(a: Nat) { a = Nat.zero or exists(b: Nat) { a = Nat.suc(b) } }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_inductive_constructors_injective() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }
    theorem goal(a: Nat, b: Nat) { Nat.suc(a) = Nat.suc(b) implies a = b }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_prover_gets_structural_induction() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }
    let f: Nat -> Bool = axiom
    axiom base {
        f(Nat.zero)
    }
    axiom step(k: Nat) {
        f(k) implies f(k.suc)
    }
    theorem goal(n: Nat) {
        f(n)
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_prover_typical_induction_pattern() {
    // This is how you'd typically expect induction proofs to be written.
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }
    let f: Nat -> Bool = axiom
    let g: Nat -> Bool = axiom
    axiom base {
        f(Nat.zero)
    }
    axiom step_first_half(k: Nat) {
        f(k) implies g(k)
    }
    axiom step_second_half(k: Nat) {
        g(k) implies f(k.suc)
    }
    theorem goal(n: Nat) {
        f(n)
    } by {
        forall(k: Nat) {
            if f(k) {
                f(k.suc)
            }
        }
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_proving_parametric_theorem_basic() {
    let text = r#"
    theorem goal[T](a: T, b: T, c: T) {
        a = b and b = c implies a = c
    } by {
        if (a = b and b = c) {
            a = c
        }
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_proving_parametric_theorem_no_block() {
    let text = r#"
    theorem goal[T](a: T, b: T, c: T) { a = b and b = c implies a = c }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_applying_parametric_function() {
    let text = r#"
    type Nat: axiom
    define foo[T](a: T) -> Bool { (a = a) }
    let zero: Nat = axiom
    theorem goal { foo(zero) }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_parametric_definition_and_theorem() {
    let text = r#"
    define foo[T](a: T) -> Bool { axiom }
    axiom foo_true[T](a: T) { foo(a) }
    type Nat: axiom
    let zero: Nat = axiom
    theorem goal { foo(zero) }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_parameter_name_can_change() {
    let text = r#"
    define foo[T](a: T) -> Bool { axiom }
    axiom foo_true[U](a: U) { foo(a) }
    type Nat: axiom
    let zero: Nat = axiom
    theorem goal { foo(zero) }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_proof_using_else() {
    let text = r#"
    let a: Bool = axiom
    let b: Bool = axiom
    let c: Bool = axiom
    if a {
        b
    } else {
        c
    }
    theorem goal { not a implies c }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_using_else_when_missing_if_block() {
    let text = r#"
    let a: Bool = axiom
    let b: Bool = axiom
    if a {
    } else {
        b
    }
    theorem goal { not a implies b }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_nested_if_else() {
    let text = r#"
    let a: Bool = axiom
    let b: Bool = axiom
    let c: Bool = axiom
    if a {
        if b {
            c
        } else {
            c
        }
    }
    theorem goal { a implies c }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_prove_impossible_constraint_is_allowed() {
    let text = r#"
    structure Foo {
        first: Bool
    } constraint {
        first and not first
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_new_can_use_late_constraint_witness() {
    let text = r#"
    inductive Option[T] {
        none
        some(T)
    }

    type Nat: axiom
    let zero: Nat = axiom
    let foo: Nat -> Bool = axiom

    structure FooNat {
        n: Nat
    } constraint {
        foo(n)
    }

    axiom foo_zero {
        foo(zero)
    }

    let Option.some(bar) = FooNat.new(zero)
    "#;
    verify_succeeds(text);
}

#[test]
fn test_new_for_constrained_structure_returns_option() {
    let text = r#"
    inductive Option[T] {
        none
        some(T)
    }

    structure Foo {
        value: Bool
    } constraint {
        value
    }

    theorem goal_some(b: Bool) {
        b implies exists(f: Foo) { Foo.new(b) = Option.some(f) }
    }

    theorem goal_none(b: Bool) {
        not b implies Foo.new(b) = Option.none[Foo]
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_constrained_new_some_projection_requires_option_match() {
    let text = r#"
    inductive Option[T] {
        none
        some(T)
    }

    type Foo: axiom
    let foo: Foo = axiom
    let foof: Foo -> Bool = axiom
    axiom {
        foof(foo)
    }

    structure Bar {
        f: Foo
    } constraint {
        foof(f)
    }
    theorem goal(f: Foo, b: Bar) {
        Bar.new(f) = Option.some(b) implies b.f = f
    }
    "#;
    verify_succeeds(text);
}
