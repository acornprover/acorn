use crate::tests::support::*;

// Proof generation and condensed-certificate regressions.

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
fn test_proof_generation_with_intermediate_existential() {
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
