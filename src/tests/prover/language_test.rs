use crate::prover::Outcome;
use crate::tests::support::*;

// General prover coverage for language features.

#[test]
fn test_proof_inside_theorem_block() {
    let text = r#"
    type Thing: axiom
    let t: Thing = axiom
    theorem reflexivity(x: Thing) {
        x = x
    } by {
        reflexivity(t)
    }
    "#;

    verify_succeeds(text);
}

#[test]
fn test_proof_inside_forall_block() {
    let text = r#"
    type Thing: axiom
    let t: Thing = axiom
    let foo: Thing -> Bool = axiom
    axiom foo_t { foo(t) }
    forall(x: Thing) {
        x = t implies foo(x)
    }
    "#;

    verify_succeeds(text);
}

#[test]
fn test_proof_inside_if_block() {
    let text = r#"
    type Thing: axiom
    forall(x: Thing, y: Thing) {
        if x = y {
            x = y
        }
    }
    "#;
    verify_succeeds(text);
}

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
fn test_citing_parametric_theorem() {
    verify_succeeds(
        r#"
    type Nat: axiom
    let zero: Nat = axiom
    theorem foo[T](a: T) { a = a }
    theorem goal { foo(zero) }
    "#,
    );
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
fn test_using_imported_axiom() {
    let text = r#"
    type Bar: axiom
    let bar: Bar = axiom
    let morph: Bar -> Bar = axiom
    axiom meq(b: Bar) { morph(b) = morph(bar) }

    theorem goal(a: Bar, b: Bar) { morph(a) = morph(b) }
    "#;
    verify_succeeds(text);
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
fn test_verify_function_satisfy() {
    let text = r#"
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one { zero != one }
    let flip(a: Nat) -> b: Nat satisfy {
        a != b
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_if_else_theorem() {
    let text = r#"
    type Nat: axiom
    let f: Nat -> Bool = axiom
    let g: Nat -> Bool = axiom
    let h: Nat -> Bool = axiom
    axiom fgh(a: Nat) {
        if f(a) {
            g(a)
        } else {
            h(a)
        }
    }
    theorem goal(a: Nat) {
        g(a) or h(a)
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_verify_function_satisfy_with_if_else() {
    let text = r#"
    type Nat: axiom
    let suc: Nat -> Nat = axiom
    let zero: Nat = axiom
    axiom base(a: Nat) {
        a = zero or exists(b: Nat) { a = suc(b) }
    }
    let pred(a: Nat) -> b: Nat satisfy {
        if a = zero {
            b = zero
        } else {
            suc(b) = a
        }
    } by {
        if a != zero {
            exists(b: Nat) { a = suc(b) }
        }
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_with_match_in_define() {
    let text = r#"
    inductive Foo {
        bar
        baz
    }
    define foo(f: Foo) -> Bool {
        match f {
            Foo.bar {
                true
            }
            Foo.baz {
                true
            }
        }
    }
    theorem goal(f: Foo) {
        foo(f)
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_with_match_in_let() {
    let text = r#"
    inductive Foo {
        bar
        baz
    }
    let foo: Bool = match Foo.bar {
        Foo.bar {
            true
        }
        Foo.baz {
            false
        }
    }
    theorem goal {
        foo
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_with_recursive_function() {
    let text = r#"
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
    theorem goal(n: Nat) {
        repeat(Nat.zero, Nat.suc, n) = n
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_with_anonymous_axiom() {
    let text = r#"
    let b: Bool = axiom
    axiom foo {
        b
    }
    theorem goal {
        b
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_easy_constraint() {
    let text = r#"
    structure Foo {
        first: Bool
        second: Bool
    } constraint {
        first or second
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_impossible_constraint() {
    let text = r#"
    structure Foo {
        first: Bool
    } constraint {
        first and not first
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_prove_constraint_equation() {
    let text = r#"
    structure Foo {
        first: Bool
        second: Bool
    } constraint {
        first or second
    }
    theorem goal(f: Foo) {
        f.first or f.second
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_constrained_member_equation() {
    let text = r#"
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
    theorem goal(f: Foo) {
        foof(f) implies Bar.new(f).f = f
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_member_equation_requires_constraint() {
    // This shouldn't work, because maybe Bar.new(f) doesn't meet the constraint.
    let text = r#"
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
    theorem goal(f: Foo) {
        Bar.new(f).f = f
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_prove_constrained_new_option_equations() {
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

    theorem goal_some_exists(b: Bool) {
        b implies exists(f: Foo) { Foo.new_option(b) = Option.some(f) }
    }

    theorem goal_some_value(b: Bool, f: Foo) {
        Foo.new_option(b) = Option.some(f) implies f.value = b
    }

    theorem goal_none(b: Bool) {
        not b implies Foo.new_option(b) = Option.none[Foo]
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_structure_constraint_attribute_equation() {
    let text = r#"
    structure Foo {
        value: Bool
    } constraint {
        value
    }

    theorem goal(b: Bool) {
        Foo.constraint(b) = b
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_destructuring_constrained_new_option_proves_member_equation() {
    let text = r#"
    type Int: axiom

    let zero: Int = axiom
    let one: Int = axiom
    let is_reduced: (Int, Int) -> Bool = axiom

    axiom zero_one_is_reduced {
        is_reduced(zero, one)
    }

    inductive Option[T] {
        none
        some(T)
    }

    structure Rat {
        num: Int
        denom: Int
    } constraint {
        is_reduced(num, denom)
    }

    let Option.some(alt_zero) = Rat.new_option(zero, one)

    theorem alt_zero_num {
        alt_zero.num = zero
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_constrained_new_option_round_trips_all_rats() {
    let text = r#"
    type Int: axiom

    let zero: Int = axiom
    let one: Int = axiom
    let is_reduced: (Int, Int) -> Bool = axiom

    axiom zero_one_is_reduced {
        is_reduced(zero, one)
    }

    inductive Option[T] {
        none
        some(T)
    }

    structure Rat {
        num: Int
        denom: Int
    } constraint {
        is_reduced(num, denom)
    }

    theorem goal(r1: Rat) {
        Rat.new_option(r1.num, r1.denom) = Option.some(r1)
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_boolean_equality() {
    let text = r#"
    let a: Bool = axiom
    let b: Bool = axiom
    axiom {
        a implies b
    }
    axiom {
        b implies a
    }
    theorem goal {
        a = b
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_implies_keyword() {
    let text = r#"
    let a: Bool = axiom
    theorem {
        a implies a
    }
    theorem {
        not a implies not a
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_generic_structure_definition() {
    // These theorems are direct implications of the structure definition.
    let text = r#"
    structure Pair[T, U] {
        first: T
        second: U
    }

    theorem check_first[T, U](t: T, u: U) {
        Pair.new(t, u).first = t
    }

    theorem check_second[T, U](t: T, u: U) {
        Pair.new(t, u).second = u
    }

    theorem check_new[T, U](p: Pair[T, U]) {
        Pair.new(p.first, p.second) = p
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prove_with_imported_generic_structure() {
    let text = r#"
    structure Pair[T, U] {
        first: T
        second: U
    }

    theorem check_first[T, U](t: T, u: U) {
        Pair.new(t, u).first = t
    }

    theorem check_second[T, U](t: T, u: U) {
        Pair.new(t, u).second = u
    }

    theorem check_new[T, U](p: Pair[T, U]) {
        Pair.new(p.first, p.second) = p
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_instance_of_generic_structure() {
    let text = r#"
    structure Pair[T, U] {
        first: T
        second: U
    }

    type Foo: axiom

    theorem foo_pair_first(a: Foo, b: Foo) {
        Pair.new(a, b).first = a
    }

    theorem foo_pair_second(a: Foo, b: Foo) {
        Pair.new(a, b).second = b
    }

    theorem foo_pair_new(p: Pair[Foo, Foo]) {
        Pair.new(p.first, p.second) = p
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_generic_constraint() {
    let text = r#"
    structure EqCheckedPair[T] {
        first: T
        second: T
        eq: Bool
    } constraint {
        eq implies first = second
    }

    type Foo: axiom

    theorem check_constraint(p: EqCheckedPair[Foo]) {
        p.eq implies p.first = p.second
    }
    "#;
    verify_succeeds(text);
}
