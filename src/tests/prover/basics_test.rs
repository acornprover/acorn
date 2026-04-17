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
fn test_extracting_narrow_proof() {
    let text = r#"
            let b: Bool = axiom
            let f1: Bool -> Bool = axiom
            let f2: Bool -> Bool = axiom
            let f3: Bool -> Bool = axiom
            let f4: Bool -> Bool = axiom
            axiom a1 { f1(b) }
            axiom a12(x: Bool) { f1(x) implies f2(x) }
            axiom a23(x: Bool) { f2(x) implies f3(x) }
            axiom a34(x: Bool) { f3(x) implies f4(x) }
            theorem goal(x: Bool) { f4(b) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_rewriting_confluence_indirectly() {
    // The facts given by "axiom recursion_base" and "define add" are
    // each rewrite rules.
    // To prove add_zero_right, the naive way applies one backward and one
    // forward rewrite.
    // We need to be able to handle this somehow.
    let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }
            axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }
            define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }
            theorem add_zero_right(a: Nat) { add(a, zero) = a }
        "#;

    verify_succeeds(text);
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
fn test_proving_explicit_false_okay() {
    verify_succeeds(
        r#"
            let b: Bool = axiom
            if b != b {
                false
            }
        "#,
    );
}

#[test]
fn test_subsequent_explicit_false_ok() {
    verify_succeeds(
        r#"
            let b: Bool = axiom
            if b != b {
                b or not b
                false
            }
        "#,
    );
}

// Reproduces a bug where a claim BEFORE an explicit `false` fails with Inconsistent.
// The issue: when processing the claim, `includes_explicit_false` hasn't been set yet
// because `false` hasn't been processed. But the prover finds a contradiction from
// the hypothetical facts alone, which should be valid (it proves the claim vacuously).
#[test]
fn test_claim_before_explicit_false_with_inconsistent_assumptions() {
    // The key structure:
    // 1. Assume something that leads to inconsistency (a = b and a != b)
    // 2. Make a claim that can be proven from the inconsistency
    // 3. Have explicit `false` at the end
    verify_succeeds(
        r#"
            let a: Bool = axiom
            let b: Bool = axiom
            axiom a_eq_b { a = b }
            if a != b {
                // This claim should succeed - the assumptions are inconsistent,
                // so any claim is vacuously true. The prover will find the inconsistency
                // when trying to prove "a = b implies a = a", but since `false` comes
                // later, this should be allowed.
                a = b implies a = a
                false
            }
        "#,
    );
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

#[test]
fn test_verify_if_else_function() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            define sign(a: Nat) -> Nat {
                if a = zero {
                    zero
                } else {
                    one
                }
            }
            theorem goal(a: Nat) {
                sign(a) = zero or sign(a) = one
            }
        "#,
    );
}

#[test]
fn test_verify_complicated_theorem_application() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let a: Nat = axiom
            let b: Nat = axiom
            let c: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom trans(x: Nat, y: Nat, z: Nat) {
                f(x, y) and f(y, z) implies f(x, z)
            }
            axiom fab { f(a, b) }
            axiom fbc { f(b, c) }
            theorem goal {
                f(a, c)
            }
            "#,
    );
}

#[test]
fn test_verify_existence_theorem() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let a: Nat = axiom
            let f: Nat -> Bool = axiom
            let g: (Nat, Nat) -> Bool = axiom
            axiom foo(x: Nat) {
                f(x) implies exists(y: Nat) { g(x, y) and g(y, x) }
            }
            theorem goal {
                f(a) implies exists(y: Nat) { g(a, y) and g(y, a) }
            }
            "#,
    );
}

#[test]
fn test_finding_implied_exists() {
    verify_succeeds(
        r#"
            type Foo: axiom
            let b: Foo = axiom
            let foo: Foo -> Bool = axiom
            let bar: (Foo, Foo) -> Bool = axiom
            let qux: Foo -> Foo = axiom

            axiom foo_implies_exists(a: Foo) {
                foo(a) implies exists(i: Foo, j: Foo) {
                    bar(i, j) and bar(j, a) and qux(i) = qux(j)
                }
            }

            axiom foo_b {
                foo(b)
            }

            theorem goal {
                exists (i: Foo, j: Foo) {
                    bar(i, j) and bar(j, b) and qux(i) = qux(j)
                }
            }
            "#,
    );
}

#[test]
fn test_rewrite_consistency() {
    // In practice this caught an inconsistency that came from bad rewrite logic.
    verify_succeeds(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            let mulx: (Nat, Nat) -> Nat = axiom
            axiom add_suc(a: Nat, b: Nat) { addx(suc(a), b) = suc(addx(a, b)) }
            axiom suc_ne(a: Nat) { suc(a) != a }
            axiom mul_suc(a: Nat, b: Nat) { addx(a, mulx(a, b)) = mulx(a, suc(b)) }
            theorem goal(a: Nat) { suc(a) != a }
        "#,
    );
}

#[test]
fn test_basic_lambda_normalization() {
    // We can normalize lambdas inside function calls by synthesizing terms for them.
    verify_succeeds(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            define apply(f: Nat -> Nat, a: Nat) -> Nat { f(a) }
            theorem goal { apply(function(x: Nat) { x }, zero) = zero }
        "#,
    );
}

#[test]
fn test_functional_equality_definition() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let f: Nat -> Nat = axiom
            let g: Nat -> Nat = axiom
            theorem goal { forall(x: Nat) { f(x) = g(x) } implies f = g }
        "#,
    );
}

#[test]
fn test_verify_functional_definition() {
    verify_succeeds(
        r#"
            type Nat: axiom
            define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
            define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
            let p: Nat = axiom
            let f: Nat -> Bool = is_min(gcd_term(p))

            theorem goal { is_min(gcd_term(p)) = f }
        "#,
    );
}

#[test]
fn test_functional_substitution() {
    verify_succeeds(
        r#"
            type Nat: axiom
            define find(f: Nat -> Bool) -> Nat { axiom }
            define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
            define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
            let p: Nat = axiom
            let f: Nat -> Bool = is_min(gcd_term(p))
            theorem goal { find(is_min(gcd_term(p))) = find(f) }
        "#,
    );
}

#[test]
fn test_proving_with_partial_application() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem goal(f: Nat -> Nat) { f = addx(zero) implies f(zero) = addx(zero, zero) }
        "#,
    );
}

#[test]
fn test_backward_nonbranching_reasoning() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let suc: Nat -> Nat = axiom
            axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }
            let n: Nat = axiom
            axiom hyp { suc(n) != n }
            theorem goal { suc(suc(n)) != suc(n) }
        "#,
    )
}

#[test]
fn test_basic_unification() {
    verify_succeeds(
        r#"
            type Nat: axiom
            let zero: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom f_zero_right(x: Nat) { f(x, zero) }
            theorem goal { exists(x: Nat) { f(zero, x) } }
        "#,
    );
}

#[test]
fn test_indirect_proof_collapses() {
    let text = r#"
            let a: Bool = axiom
            let b: Bool = axiom
            axiom bimpa { b implies a }
            axiom bimpna { b implies not a }
            theorem goal { not b }
        "#;
    verify_succeeds(text);
}
