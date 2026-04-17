use crate::prover::Outcome;
use crate::tests::support::*;

// Basic prover behavior and small smoke tests.

#[test]
fn test_specialization() {
    let text = r#"
            axiom f_all(x: Thing) { f(x) }
            theorem goal { f(t) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_backward_specialization_fails() {
    let text = r#"
            axiom f_one { f(t) }
            theorem goal(x: Thing) { f(x) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::ShallowExhausted);
}

#[test]
fn test_axiomatic_values_distinct() {
    let text = "theorem goal { t = t2 }";
    assert_eq!(prove_thing(text, "goal"), Outcome::ShallowExhausted);
}

#[test]
fn test_finds_example() {
    let text = r#"
            axiom f_one { f(t) }
            theorem goal { exists(x: Thing) { f(x) } }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_finds_negative_example() {
    let text = r#"
            axiom not_f(x: Thing) { not f(x) }
            theorem goal { not f(t) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_extends_equality() {
    let text = r#"
            axiom t_eq_t2 { t = t2 }
            theorem goal { f(t) = f(t2)  }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_composition() {
    let text = r#"
            axiom g_id(x: Thing) { g(x, x) = x }
            axiom f_t { f(t) }
            theorem goal { f(g(t, t)) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_negative_rewriting() {
    let text = r#"
            axiom not_f_t { not f(t) }
            axiom g_id(x: Thing) { g(x, x) = x }
            theorem goal { not f(g(t, t)) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_extends_ne() {
    let text = r#"
            axiom f_t_ne_f_t2 { f(t) != f(t2) }
            theorem goal { t != t2 }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_equality_resolution() {
    let text = r#"
            axiom foo(x: Thing) { x != t or f(t) }
            theorem goal { f(t) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_equality_factoring() {
    let text = r#"
            axiom foo(x: Thing, y: Thing) { x = t or y = t }
            theorem goal(x: Thing) { x = t2 }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_existence_of_nonequality() {
    // After normalization, this is the same problem as the equality
    // factoring test above. So if one of them works and one doesn't,
    // it's likely to be a prioritization dependency problem.
    let text = r#"
            axiom foo { exists(x: Thing) { x != t2 } }
            theorem goal { exists(x: Thing) { x != t } }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_prover_avoids_loops() {
    let text = r#"
            axiom trivial(x: Thing) { not f(h(x)) or f(h(x)) }
            axiom arbitrary(x: Thing) { f(h(x)) or f(x) }
            theorem goal { f(t) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::ShallowExhausted);
}

#[test]
fn test_synthesis_avoids_loops() {
    let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) or f(h(t)) }
            theorem goal { f(t2) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::ShallowExhausted);
}

#[test]
fn test_higher_order_unification() {
    let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) }
            theorem goal { f(t) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_second_literal_matches_goal() {
    let text = r#"
            axiom axiom1 { f(g(t, t)) or f(t2) }
            axiom axiom2 { not f(g(t, t)) or f(t2) }
            theorem goal { f(t2) }
        "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Success);
}

#[test]
fn test_closure_proof() {
    let text = r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
            theorem goal(a: Nat, b: Nat) { addx(a, b) = adder(a)(b) }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_prove_text_boolean_equality() {
    let text = r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define ltex(a: Nat, b: Nat) -> Bool { exists(c: Nat) { addx(a, c) = b } }
            define ltx(a: Nat, b: Nat) -> Bool { ltex(a, b) and a != b }
            theorem goal(a: Nat) { not ltx(a, a) }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_using_conditional_existence_theorem() {
    let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let suc: Nat -> Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            axiom one_neq_zero { one != zero }
            theorem goal { exists(x: Nat) { one = suc(x) } }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_instance_of_conditional_existence_theorem() {
    let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            theorem goal { y = zero or exists(b: Nat) { y = suc(b) } }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_another_instance_of_conditional_existence_theorem() {
    let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            axiom y_not_zero { y != zero }
            theorem goal { y = zero or exists(b: Nat) { y = suc(b) } }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_finding_inconsistency() {
    let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let foo: Nat -> Bool = axiom
            let bar: Nat -> Bool = axiom
            axiom foo_true { foo(zero) }
            axiom foo_false { not foo(zero) }
            theorem goal { bar(zero) }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
}

#[test]
fn test_using_true_and_false_in_a_proof() {
    let text = r#"
        theorem goal(b: Bool) { b = true or b = false }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_finding_mildly_nontrivial_inconsistency() {
    let text = r#"
            axiom bad { true = false }
            let b: Bool = axiom
            theorem goal { b }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
}

#[test]
fn test_explicit_false_mandatory() {
    let text = r#"
            let b: Bool = axiom
            let c: Bool = axiom
            if b != b {
                c
            }
        "#;
    assert_eq!(verify(text).unwrap(), Outcome::Inconsistent);
}
