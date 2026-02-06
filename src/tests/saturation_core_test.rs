use super::common::*;
use crate::project::Project;
use crate::prover::Outcome;

fn assert_proof_lines(actual: Vec<String>, expected_small: &[&str], expected_big: &[&str]) {
    #[cfg(feature = "bigcert")]
    let _ = expected_small;
    #[cfg(not(feature = "bigcert"))]
    let _ = expected_big;

    let expected = {
        #[cfg(feature = "bigcert")]
        {
            expected_big
        }
        #[cfg(not(feature = "bigcert"))]
        {
            expected_small
        }
    };
    let expected = expected
        .iter()
        .map(|line| line.to_string())
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

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
    assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
}

#[test]
fn test_axiomatic_values_distinct() {
    let text = "theorem goal { t = t2 }";
    assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
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
    assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
}

#[test]
fn test_synthesis_avoids_loops() {
    let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) or f(h(t)) }
            theorem goal { f(t2) }
            "#;
    assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
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

#[test]
fn test_proof_generation_with_forall_goal() {
    let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg { forall(x: Nat) { f(x) implies g(x) } }
            axiom gimph { forall(x: Nat) { g(x) implies h(x) } }
            theorem goal { forall(x: Nat) { f(x) implies h(x) } }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_generation_with_intermediate_skolem() {
    let text = r#"
        type Nat: axiom
        let b: Bool = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom forg(x: Nat) { f(x) or g(x) }
        axiom fgimpb { forall(x: Nat) { f(x) or g(x) } implies b }
        theorem goal { b }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_assuming_lhs_of_implication() {
    verify_succeeds(
        r#"
            let a: Bool = axiom
            let b: Bool = axiom
            let c: Bool = axiom
            axiom aimpb { a implies b }
            axiom bimpc { b implies c }
            theorem goal { a implies c } by {
                b
            }
        "#,
    );
}

#[test]
fn test_templated_proof() {
    let text = r#"
            type Thing: axiom
            let t1: Thing = axiom
            let t2: Thing = axiom
            let t3: Thing = axiom

            define foo[T](x: T) -> Bool { axiom }

            axiom a12 { foo(t1) implies foo(t2) }
            axiom a23 { foo(t2) implies foo(t3) }
            theorem goal { foo(t1) implies foo(t3) }
            "#;

    verify_succeeds(text);
}

#[test]
fn test_proof_condensing_induction() {
    let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        let suc: Nat -> Nat = axiom
        axiom induction(f: Nat -> Bool) {
            f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) }
        }
        let foo: Nat -> Bool = axiom
        theorem goal { foo(zero) and forall(k: Nat) { foo(k) implies foo(suc(k)) } implies forall(n: Nat) { foo(n) } }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_condensing_false() {
    let text = r#"
        let a: Bool = axiom
        axiom a_true { a }
        if not a {
            false
        }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_condensing_combining_two_theorems() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom fimpg(x: Nat) { f(x) implies g(x) }
        axiom fa { f(a) }
        theorem goal { g(a) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proof_indirect_from_goal() {
    let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg(x: Nat) { f(x) implies g(x) }
            axiom gimph(x: Nat) { g(x) implies h(x) }
            axiom fimpnh(x: Nat) { f(x) implies not h(x) }
            theorem goal(x: Nat) { not f(x) }
        "#;

    verify_succeeds(text);
}

#[test]
fn test_no_verify_boolean_soup() {
    // This goal is not provable.
    // I'm not sure what ever went wrong, it's a mess of nested boolean formulas.
    let text = r#"
        theorem goal(a: Bool, b: Bool, c: Bool) {
            a = b or a = not c
        }
        "#;
    let outcome = verify(text).expect("verification errored");
    assert!(
        outcome == Outcome::Exhausted || outcome == Outcome::Timeout,
        "Expected Exhausted or Timeout, got {}",
        outcome
    );
}

#[test]
fn test_resolution_trap() {
    // This is a trap for the resolution algorithm, because repeated resolution
    // against the negated goal will give longer and longer formulas.
    let text = r#"
        type Nat: axiom
        let f: Nat -> Nat = axiom
        let g: Nat -> Bool = axiom
        let a: Nat = axiom
        axiom ga { g(a) }
        theorem goal {
            not forall(x: Nat) { g(x) implies g(f(x)) }
        }
        "#;
    verify_fails(text);
}

#[test]
fn test_verify_or_contraction() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define some(x: Nat) -> Bool { f(x) or g(x) or h(x) }
        axiom somea { f(a) or g(a) or h(a) }
        theorem goal { some(a) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_fimp_expansion() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }
        axiom fimpa { fimp(a) }
        theorem goal { f(a) implies (g(a) and h(a)) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_fimp_contraction() {
    let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }
        axiom fimpa { f(a) implies (g(a) and h(a)) }
        theorem goal { fimp(a) }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_definition_trap() {
    // This will infinite loop if you allow free resolutions against definition.
    let text = r#"
        type Nat: axiom
        let z: Nat = axiom
        let f: Nat -> Bool = axiom
        let suc: Nat -> Nat = axiom
        define decr(x: Nat) -> Bool { f(x) and not f(suc(x))}
        axiom fz { f(z) }
        theorem goal { exists(x: Nat) { decr(x) } }
        "#;
    verify_fails(text);
}

#[test]
fn test_verify_functional_existence() {
    // There are two tricky things about this resolution.
    // In one of the directions, you have to resolve x0(x1) against foo(a, b).
    // In the other direction, in the final literal-literal resolution, both sides
    // still have a free variable. So we don't find it via simplification.
    // Nevertheless, intuitively it is just one step.
    let text = r#"
        type Nat: axiom
        let is_min: (Nat -> Bool, Nat) -> Bool = axiom
        let foo: Nat -> (Nat -> Bool) = axiom
        axiom has_min(f: Nat -> Bool, n: Nat) {
            f(n) implies exists(m: Nat) { is_min(f, m) }
        }
        axiom foo_is_true_somewhere(a: Nat) {
            exists(b: Nat) { foo(a, b) }
        }
        let min_foo(a: Nat) -> b: Nat satisfy {
            is_min(foo(a), b)
        }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_free_simplification_trap() {
    // This will infinite loop if you let a 3-to-2 resolution plus a 2-to-1 simplification
    // be zero depth.
    let text = r#"
        type Nat: axiom
        let foo: Nat -> Nat = axiom
        let bar: Nat -> Bool = axiom
        let zap: Nat -> Bool = axiom
        axiom expander(x: Nat) {
            not zap(x) or not bar(x) or zap(foo(x))
        }
        axiom simplifier(x: Nat) {
            bar(foo(x))
        }
        theorem goal(a: Nat) {
            not zap(foo(a))
        }
        "#;
    verify_fails(text);
}

#[test]
fn test_verify_rewrite_trap() {
    // This will infinite loop if you allow complexifying rewrites.
    let text = r#"
        type Nat: axiom
        let f: (Nat, Nat) -> Nat = axiom
        let g: Nat -> Bool = axiom
        axiom fxx(x: Nat) { f(x, x) = x }
        theorem goal(a: Nat) { g(a) }
        "#;
    verify_fails(text);
}

#[test]
fn test_prove_with_imported_skolem() {
    let text = r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom

        axiom exists_a_fa {
            exists(a: Nat) { f(a) }
        }

        theorem goal {
            exists(a: Nat) { f(a) }
        }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_code_gen_not_losing_conclusion() {
    // Reproducing a bug found by Dan.
    // This confused the code generator because the final step of the proof
    // uses only a single source, so when you reverse it, it has no premise.
    // (It's using equality resolution to go from "x0 != constant" to a contradiction.)
    let text = r#"
            type Foo: axiom
            let zero: Foo = axiom
            let three: Foo = axiom
            let mul: (Foo, Foo) -> Foo = axiom

            define threeven(n: Foo) -> Bool {
                exists(d: Foo) {
                    mul(three, d) = n
                }
            }

            axiom mul_zero_right(a: Foo, b: Foo) {
                b = zero implies mul(a, b) = zero
            }

            theorem goal {
                threeven(zero)
            }
            "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_identity_is_surjective() {
    // To prove this, we need to instantiate the definitions of:
    // is_surjective[V, V]
    // identity[V]
    let text = r#"
            define is_surjective[T, U](f: T -> U) -> Bool {
                forall(y: U) {
                    exists(x: T) {
                        f(x) = y
                    }
                }
            }

            define identity[T](x: T) -> T {
                x
            }

            theorem identity_is_surjective[V] {
                is_surjective(identity[V])
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_lib_keyword() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
            type Foo: axiom
            let bar: Foo = axiom
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from foo import bar

            theorem goal {
                bar = lib(foo).bar
            }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_proving_rewrite_only() {
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

        axiom rule1 {
          f(Foo.foo) = f(Foo.bar)
        }

        axiom rule2 {
          f(Foo.bar) = f(Foo.baz)
        }
            
        theorem goal {
          f(Foo.foo) = f(Foo.baz)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), vec!["f(Foo.foo) != f(Foo.bar)"]);
}

#[test]
fn test_proving_modus_ponens_only() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
          bar
          baz
        }
            
        let f: Foo -> Bool = axiom

        axiom rule1 {
          f(Foo.foo) implies f(Foo.bar)
        }

        axiom rule2 {
          f(Foo.bar) implies f(Foo.baz)
        }
            
        theorem goal {
          f(Foo.foo) implies f(Foo.baz)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_proving_with_active_resolution() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom
            
        axiom rule(x: Foo) {
          f(x) and g(x) implies h(x)
        }
            
        theorem goal(y: Foo) {
          f(y) and g(y) implies h(y)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &["not g(y) or not f(y) or h(y)"],
        &["function(x0: Foo) { not g(x0) or not f(x0) or h(x0) }(y)"],
    );
}

#[test]
fn test_proving_exact_clause_match() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom
            
        axiom rule {
          f(Foo.foo) or g(Foo.foo) or h(Foo.foo)
        }
            
        theorem goal {
          f(Foo.foo) or g(Foo.foo) or h(Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_proving_an_or() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom
            
        axiom rule1 {
          f(Foo.foo) or g(Foo.foo) or h(Foo.foo)
        }

        axiom rule2 {
          not f(Foo.foo)
        }
            
        theorem goal {
          g(Foo.foo) or h(Foo.foo)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_eq!(c.proof.unwrap(), Vec::<String>::new());
}

#[test]
fn test_proving_removes_duplicates() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
          foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
            
        axiom rule1(x: Foo) {
          f(x) implies g(x)
        }

        axiom rule2(x: Foo) {
          f(x)
        }
            
        theorem goal(y: Foo) {
          g(y)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &["not f(y) or g(y)", "not f(y)", "f(y)"],
        &[
            "function(x0: Foo) { not f(x0) or g(x0) }(y)",
            "not f(y)",
            "function(x1: Foo) { f(x1) }(y)",
        ],
    );
}

#[test]
fn test_proving_with_passive_resolution() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
        }
            
        let f: Foo -> Bool = axiom
        let g: Foo -> Bool = axiom
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            g(x)
        }

        axiom rule2(x: Foo) {
            f(x) implies not g(x)
        }

        axiom rule3(x: Foo) {
            h(x) implies f(x)
        }
            
        theorem goal(y: Foo) {
            not h(y)
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &["not h(y) or f(y)", "f(y)", "not g(y) or not f(y)", "g(y)"],
        &[
            "function(x0: Foo) { not h(x0) or f(x0) }(y)",
            "f(y)",
            "function(x1: Foo) { not g(x1) or not f(x1) }(y)",
            "function(x2: Foo) { g(x2) }(y)",
        ],
    );
}

#[test]
fn test_proving_activating_rewrite_pattern() {
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
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            f(x) = g(x)
        }
            
        theorem goal(y: Foo) {
            h(f(y)) implies h(g(y))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &["g(y) = f(y)"],
        &["function(x0: Foo) { g(x0) = f(x0) }(y)"],
    );
}

#[test]
fn test_proving_with_passive_contradiction() {
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
        let h: Foo -> Bool = axiom

        axiom rule1(x: Foo) {
            h(f(Foo.foo))
        }
            
        theorem goal(y: Foo) {
            forall(x: Foo) { f(x) = g(x) } implies h(g(Foo.foo))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &["g(Foo.foo) = f(Foo.foo)", "not h(f(Foo.foo))"],
        &[
            "function(x0: Foo) { g(x0) = f(x0) }(Foo.foo)",
            "not h(f(Foo.foo))",
        ],
    );
}

#[test]
fn test_proving_with_multiple_rewrite() {
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

        axiom rule1(x: Foo) {
            f(x) = g(x)
        }
            
        theorem goal(y: Foo) {
            f(f(f(y))) = g(g(g(y)))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "g(y) = f(y)",
            "g(g(y)) = f(g(y))",
            "g(g(g(y))) = f(g(g(y)))",
        ],
        &[
            "function(x0: Foo) { g(x0) = f(x0) }(y)",
            "function(x1: Foo) { g(x1) = f(x1) }(g(y))",
            "function(x2: Foo) { g(x2) = f(x2) }(g(g(y)))",
        ],
    );
}

#[test]
fn test_proving_random_bug() {
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
        let h: Foo -> Foo = axiom
        let z: Foo = axiom

        axiom rule1(x: Foo) {
            f(x) = g(x) or f(x) = h(x) or f(x) = z
        }
            
        theorem goal(y: Foo) {
            g(y) = h(y) implies f(y) = h(y) or f(y) = z
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &["g(y) != f(y)", "f(y) = z or h(y) = f(y) or g(y) = f(y)"],
        &[
            "g(y) != f(y)",
            "function(x0: Foo) { z = f(x0) or h(x0) = f(x0) or g(x0) = f(x0) }(y)",
        ],
    );
}

#[test]
fn test_proving_with_equality_factoring_basic() {
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
        let h: Foo -> Foo = axiom

        axiom rule1(x: Foo) {
            f(x) != h(x)
        }

        axiom rule2(x: Foo) {
            g(x) = h(x)
        }
            
        theorem goal(y: Foo) {
            not (f(y) = g(y) or f(y) = h(y))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "h(y) != g(y) or g(y) = f(y)",
            "h(y) = g(y)",
            "g(y) = f(y)",
            "h(y) != f(y)",
        ],
        &[
            "h(y) != g(y) or g(y) = f(y)",
            "function(x0: Foo) { h(x0) = g(x0) }(y)",
            "g(y) = f(y)",
            "function(x1: Foo) { h(x1) != f(x1) }(y)",
        ],
    );
}

#[test]
fn test_proving_with_equality_factoring_mixed_forwards() {
    // This ends up being a tiny bit different than the previous one because the atoms
    // are normalized differently.
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
        let h: Foo -> Foo = axiom

        axiom rule1(x: Foo) {
            h(x) != f(x)
        }

        axiom rule2(x: Foo) {
            g(x) = h(x)  
        }
            
        theorem goal(y: Foo) {
            not (g(y) = f(y) or h(y) = f(y))
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "h(y) != g(y) or g(y) = f(y)",
            "h(y) = g(y)",
            "g(y) = f(y)",
            "h(y) != f(y)",
        ],
        &[
            "h(y) != g(y) or g(y) = f(y)",
            "function(x0: Foo) { h(x0) = g(x0) }(y)",
            "g(y) = f(y)",
            "function(x1: Foo) { h(x1) != f(x1) }(y)",
        ],
    );
}

#[test]
fn test_proving_with_equality_resolution() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        inductive Foo {
            foo
            bar
        }
            
        let f: (Foo, Foo) -> Bool = axiom
        let g: Foo -> Foo = axiom

        axiom rule1(x: Foo, y: Foo) {
            g(x) = g(y) implies f(x, y)
        }

        axiom rule2(x: Foo, y: Foo) {
            f(x, y) implies f(g(x), y)
        }
            
        theorem goal(x: Foo) {
            f(g(g(x)), x) 
        }
        "#,
    );

    let c = prove(&mut p, "main", "goal");
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "not f(x, x) or f(g(x), x)",
            "not f(g(x), x) or f(g(g(x)), x)",
            "not f(g(x), x)",
            "g(x) != g(x) or f(x, x)",
            "f(x, x)",
        ],
        &[
            "function(x0: Foo, x1: Foo) { not f(x0, x1) or f(g(x0), x1) }(x, x)",
            "function(x2: Foo, x3: Foo) { not f(x2, x3) or f(g(x2), x3) }(g(x), x)",
            "not f(g(x), x)",
            "function(x4: Foo, x5: Foo) { g(x4) != g(x5) or f(x4, x5) }(x, x)",
            "f(x, x)",
        ],
    );
}

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
    assert_proof_lines(
        c.proof.unwrap(),
        &["f(Foo.foo)", "f(Foo.bar)"],
        &[
            "function(x0: Foo) { f(x0) }(Foo.foo)",
            "function(x1: Foo) { f(x1) }(Foo.bar)",
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
    assert_proof_lines(
        c.proof.unwrap(),
        &["let s0: Foo satisfy { f(s0) }", "not f(s0)"],
        &[
            "let s0: Foo satisfy { f(s0) }",
            "function(x0: Foo) { not f(x0) }(s0)",
        ],
    );
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
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "let s0: Foo satisfy { f(s0) and g(s0) }",
            "not g(s0) or not f(s0)",
            "not f(s0)",
        ],
        &[
            "let s0: Foo satisfy { f(s0) and g(s0) }",
            "function(x0: Foo) { not g(x0) or not f(x0) }(s0)",
            "not f(s0)",
        ],
    );
}

#[test]
fn test_proving_with_skolem() {
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
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "let s0: Foo -> Foo satisfy { forall(x0: Foo) { not f(x0) or g(x0, s0(x0)) } }",
            "not g(x, s0(x))",
            "not f(x) or g(x, s0(x))",
        ],
        &[
            "let s0: Foo -> Foo satisfy { forall(x0: Foo) { not f(x0) or g(x0, s0(x0)) } }",
            "function(x1: Foo) { not g(x, x1) }(s0(x))",
            "function(x2: Foo) { not f(x2) or g(x2, s0(x2)) }(x)",
        ],
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
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "let s0: Foo satisfy { true }",
            "f(s0)",
            "not f(s0) or g",
            "not f(s0)",
        ],
        &[
            "let s0: Foo satisfy { true }",
            "function(x0: Foo) { f(x0) }(s0)",
            "function(x1: Foo) { not f(x1) or g }(s0)",
            "not f(s0)",
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
    assert_proof_lines(
        c.proof.unwrap(),
        &["a + (b + c) = a + b + c", "a + (b + c) = b + c + a"],
        &[
            "function(x0: T, x1: T, x2: T) { x0 + x1 + x2 = x0 + (x1 + x2) }(a, b, c)",
            "function(x3: T, x4: T) { x3 + x4 = x4 + x3 }(b + c, a)",
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
    assert_proof_lines(
        c.proof.unwrap(),
        &["not f(Foo.foo, Foo.foo) or not f(Foo.foo, Foo.foo)"],
        &["function(x0: Foo, x1: Foo) { not f(x0, x1) or not f(x1, x0) }(Foo.foo, Foo.foo)"],
    );
}

#[test]
fn test_proving_with_long_skolem_definition() {
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
    assert_proof_lines(
        c.proof.unwrap(),
        &[
            "not lib(foo).g(Foo.foo) or h(Foo.foo)",
            "not lib(foo).g(Foo.foo)",
            "not f(Foo.foo) or lib(foo).g(Foo.foo)",
        ],
        &[
            "function(x0: Foo) { not lib(foo).g(x0) or h(x0) }(Foo.foo)",
            "not lib(foo).g(Foo.foo)",
            "function(x1: Foo) { not f(x1) or lib(foo).g(x1) }(Foo.foo)",
        ],
    );
}

#[test]
fn test_proving_list_contains() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
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
        "#,
    );

    prove(&mut p, "main", "goal");
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
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
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
        "#,
    );

    prove(&mut p, "main", "goal");
}

/// Test that extensionality works without requiring a witness for uninhabited types.
///
/// This test uses a structure wrapper so that the proof MUST use extensionality.
/// The axiom `a.value = b.value` normalizes to `a.value(x) = b.value(x)`.
/// The goal `a = b` requires proving the structures are equal, which requires:
/// 1. Using extensionality to derive `a.value = b.value` from `a.value(x) = b.value(x)`
/// 2. Using the structure identity axiom to conclude `a = b`
///
/// Importantly, T is uninhabited (an axiom type with no constructors), so the prover
/// cannot instantiate x with a concrete value. Extensionality must work on the
/// universally quantified clause directly.
#[test]
fn test_extensionality_without_witness_for_uninhabited_type() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/main.ac",
        r#"
        // T is uninhabited - it's an axiom type with no constructors
        type T: axiom

        // A wrapper structure containing a function over T
        structure Wrapper {
            value: T -> T
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
        "#,
    );

    // This should succeed without needing a witness for T
    prove(&mut p, "main", "goal");
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

#[test]
fn test_backward_rewrite_specialization_regression() {
    use std::fs;
    use std::path::PathBuf;

    use crate::module::LoadState;
    use crate::processor::Processor;
    use crate::project::ProjectConfig;
    use crate::prover::ProverMode;

    let src_dir = PathBuf::from("vscode/extension/acornlib/src");
    let build_dir =
        std::env::temp_dir().join(format!("acorn_add_group_build_{}", std::process::id()));
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap();

    let mut project = Project::new(src_dir.clone(), build_dir, ProjectConfig::default()).unwrap();
    let target_path = src_dir.join("add_group.ac");
    project.add_target_by_path(&target_path).unwrap();

    let module_id = project
        .load_module_by_name("add_group")
        .expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("no module"),
    };

    let node = env.get_node_by_goal_name("inverse_add");
    let goal_env = node.goal_env().unwrap();

    let mut processor = Processor::with_imports(None, env).unwrap();
    processor.add_module_facts(&node).unwrap();
    let normalized_goal = node.normalized_goal().expect("missing normalized goal");
    processor.set_normalized_goal(normalized_goal);
    let outcome = processor.search(
        ProverMode::Interactive { timeout_secs: 5.0 },
        &normalized_goal.normalizer,
    );
    assert_eq!(outcome, Outcome::Success);

    let cert = processor
        .prover()
        .make_cert(&goal_env.bindings, &normalized_goal.normalizer, false)
        .expect("make_cert failed");
    processor
        .check_cert(
            &cert,
            None,
            &normalized_goal.normalizer,
            &project,
            &goal_env.bindings,
        )
        .expect("check_cert failed");
}
