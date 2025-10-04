use super::common::*;
use crate::{project::Project, prover::Outcome};

// This file tests that the various language features work correctly in the prover.

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

    expect_proof(text, "reflexivity(t)", &[]);
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

    expect_proof(text, "x = t implies foo(x)", &[]);
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
    expect_proof(text, "x = y", &[]);
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
    let mut p = Project::new_mock();
    p.mock(
        "/mock/bar.ac",
        r#"
            type Bar: axiom
            let bar: Bar = axiom
            let morph: Bar -> Bar = axiom
            axiom meq(b: Bar) { morph(b) = morph(bar) }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            import bar
            theorem goal(a: bar.Bar, b: bar.Bar) { bar.morph(a) = bar.morph(b) }
        "#,
    );
    let (_, outcome, _) = prove_with_old_codegen(&mut p, "main", "goal");
    assert_eq!(outcome, Outcome::Success);
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
fn test_infix_addition_goes_left_to_right() {
    let text = r#"
        type Nat: axiom
        attributes Nat {
            define add(self, other: Nat) -> Nat { axiom }
        }
        theorem goal(a: Nat, b: Nat, c: Nat) { Nat.add(Nat.add(a, b), c) = a + b + c }
        theorem antigoal(a: Nat, b: Nat, c: Nat) { Nat.add(a, Nat.add(b, c)) = a + b + c }
        "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
    assert_eq!(prove_text(text, "antigoal"), Outcome::Exhausted);
}

#[test]
fn test_infix_mul_before_plus() {
    let text = r#"
        type Nat: axiom
        attributes Nat {
            define add(self, other: Nat) -> Nat { axiom }
            define mul(self, other: Nat) -> Nat { axiom }
        }
        theorem goal1(a: Nat, b: Nat, c: Nat) { Nat.add(Nat.mul(a, b), c) = a * b + c }
        theorem goal2(a: Nat, b: Nat, c: Nat) { Nat.add(a, Nat.mul(b, c)) = a + b * c }
        "#;
    assert_eq!(prove_text(text, "goal1"), Outcome::Success);
    assert_eq!(prove_text(text, "goal2"), Outcome::Success);
}
#[test]
fn test_ways_to_call_methods() {
    let text = r#"
        type Nat: axiom
        attributes Nat {
            define suc(self) -> Nat { axiom }
            define add(self, other: Nat) -> Nat { axiom }
        }
        theorem goal1(a: Nat) { a.suc.suc = Nat.suc(Nat.suc(a)) }
        theorem goal2(a: Nat) { a.suc.suc = Nat.suc(a).suc }
        theorem goal3(a: Nat, b: Nat) { (a + b).suc = Nat.suc(Nat.add(a, b)) }
        "#;
    assert_eq!(prove_text(text, "goal1"), Outcome::Success);
    assert_eq!(prove_text(text, "goal2"), Outcome::Success);
    assert_eq!(prove_text(text, "goal3"), Outcome::Success);
}

#[test]
fn test_bag_of_digits() {
    let text = r#"
        type Bag: axiom
        attributes Bag {
            let 1: Bag = axiom
            let 2: Bag = axiom
            define read(self, other: Bag) -> Bag { axiom }
        }
        numerals Bag
        axiom comm(a: Bag, b: Bag) { a.read(b) = b.read(a) }
        theorem goal { 12 = 21 }
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
fn test_prove_with_match_statement() {
    // An example found when migrating pre-match code.
    let text = r#"
        type Nat: axiom
        attributes Nat {
            define suc(self) -> Nat { axiom }
        }

        inductive Int {
            from_nat(Nat)
            neg_suc(Nat)
        }
        
        define abs_case_1(a: Int, n: Nat) -> Bool {
            a = Int.from_nat(n)
        }
        
        define abs_case_2(a: Int, n: Nat) -> Bool {
            exists(k: Nat) {
                a = Int.neg_suc(k) and n = k.suc
            }
        }
        
        define abs(a: Int) -> Nat {
            match a {
                Int.from_nat(n) {
                    n
                }
                Int.neg_suc(k) {
                    k.suc
                }
            }
        }
        
        theorem goal(a: Int) {
            abs_case_1(a, abs(a)) or abs_case_2(a, abs(a))
        } by {
            match a {
                Int.from_nat(n) {
                    abs_case_1(a, abs(a))
                }
                Int.neg_suc(k) {
                    abs_case_2(a, abs(a))
                }
            }
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
fn test_proving_with_generic_structure() {
    // Just testing that we can define something, then immediately prove the definition.
    let text = r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            attributes Pair[T, U] {
                define swap(self) -> Pair[U, T] {
                    Pair.new(self.second, self.first)
                }
            }

            theorem swap_def[T, U](p: Pair[T, U]) {
                p.swap = Pair.new(p.second, p.first)
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
    let mut p = Project::new_mock();
    p.mock(
        "/mock/pair.ac",
        r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from pair import Pair

            theorem check_first[T, U](t: T, u: U) {
                Pair.new(t, u).first = t
            }

            theorem check_second[T, U](t: T, u: U) {
                Pair.new(t, u).second = u
            }

            theorem check_new[T, U](p: Pair[T, U]) {
                Pair.new(p.first, p.second) = p
            }
        "#,
    );
    let (_, outcome, _) = prove_with_old_codegen(&mut p, "main", "check_first");
    assert_eq!(outcome, Outcome::Success);
    let (_, outcome, _) = prove_with_old_codegen(&mut p, "main", "check_second");
    assert_eq!(outcome, Outcome::Success);
    let (_, outcome, _) = prove_with_old_codegen(&mut p, "main", "check_new");
    assert_eq!(outcome, Outcome::Success);
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

#[test]
fn test_prover_handles_instance_let() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass T: TwoColored {
                is_red: T -> Bool
            }

            instance Z1: TwoColored {
                let is_red: Z1 -> Bool = function(z: Z1) {
                    true
                }
            }

            theorem goal {
                TwoColored.is_red(Z1.zero)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_prover_handles_instance_define() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass T: TwoColored {
                is_red: T -> Bool
            }

            instance Z1: TwoColored {
                define is_red(self) -> Bool {
                    true
                }
            }

            theorem goal {
                TwoColored.is_red(Z1.zero)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_prover_handles_parametrized_constants() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z1: Singleton {
                let value: Z1 = Z1.zero
            }

            theorem goal {
                Z1.zero = Singleton.value[Z1]
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_prover_fails_on_bad_instance() {
    let text = r#"
            inductive Z2 {
                zero
                one
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z2: Singleton {
                let value: Z2 = Z2.zero
            }
        "#;
    verify_fails(text);
}

#[test]
fn test_prover_succeeds_on_good_instance() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z1: Singleton {
                let value: Z1 = Z1.zero
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_prover_respects_typeclasses() {
    // Singleton.unique should not be misapplied to Z2.
    let text = r#"
            inductive Z2 {
                zero
                one
            }

            define is_equal[T](x: T, y: T) -> Bool {
                x = y
            }

            typeclass S: Singleton {
                element: S

                unique(x: S, y: S) {
                    is_equal(x, y)
                }
            }

            theorem goal {
                is_equal(Z2.zero, Z2.one)
            }
        "#;
    verify_fails(text);
}

#[test]
fn test_prover_can_use_typeclass_theorems() {
    // These axioms should be combinable via the instance relationship.
    let text = r#"
            typeclass F: Foo {
                foo: F -> Bool
            }

            axiom always_foo[F: Foo](x: F) {
                x.foo
            }

            inductive Bar {
                bar
            }

            let qux: Bool = axiom

            instance Bar: Foo {
                define foo(self) -> Bool {
                    qux
                }
            }

            theorem goal {
                qux
            } by {
                Foo.foo(Bar.bar)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_normalizing_instance_aliases() {
    let text = r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive Foo {
                foo
            }

            attributes Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }

            instance Foo: Magma {
                let mul: (Foo, Foo) -> Foo = Foo.mul
            }

            theorem goal(a: Foo) {
                Magma.mul(a, a) = a * a
            }
        "#;
    let (processor, outcome, _) = prove_as_main(text, "goal");
    assert_eq!(outcome, Outcome::Success);
    if let Some(final_step) = processor.prover().get_final_step() {
        // TODO: the goal should have just normalized to Foo.mul(x0, x0) = Foo.mul(x0, x0)
        // i.e. a trivial one.
        if !final_step.rule.is_assumption() {
            panic!("final step is not trivial: {:?}", final_step);
        }
    } else {
        panic!("expected a final step");
    }
}

#[test]
fn test_prover_handling_typeclasses() {
    let text = r#"
            typeclass F: FooTrue {
                foo: F -> Bool
                bar: F -> Bool

                foo_true(a: F) {
                    a.foo
                }

                foo_imp_bar(a: F) {
                    a.foo implies a.bar
                }
            }

            theorem bar_true[G: FooTrue](a: G) {
                a.bar
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_use_typeclass_axiom_on_instance() {
    let text = r#"
            typeclass F: FooTrue {
                b: Bool
            }

            define foo[T](t: T) -> Bool {
                axiom
            }

            axiom foo_true[F: FooTrue](a: F) {
                foo(a)
            }

            inductive Z1 {
                zero
            }

            instance Z1: FooTrue {
                let b: Bool = true
            }

            theorem goal(z: Z1) {
                foo(z)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_parametrized_constant() {
    let text = r#"
            typeclass P: PointedSet {
                point: P
            }
        
            let get_point1[P: PointedSet]: P = P.point
            let get_point2[P: PointedSet]: P = P.point
        
            theorem goal[P: PointedSet] {
                get_point1[P] = get_point2[P]
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_parametrized_inductive() {
    let text = r#"
            inductive List[T] {
                nil
                cons(T, List[T])
            }

            define any(bs: List[Bool]) -> Bool {
                match bs {
                    List.nil {
                        false
                    }
                    List.cons(b, bs) {
                        b or any(bs)
                    }
                }
            }

            theorem goal {
                exists(bs: List[Bool]) {
                    any(bs)
                }
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_using_list_contains() {
    let text = r#"
            inductive List[T] {
                nil
                cons(T, List[T])
            }

            attributes List[T] {
                define contains(self, item: T) -> Bool {
                    match self {
                        List.nil {
                            false
                        }
                        List.cons(head, tail) {
                            if head = item {
                                true
                            } else {
                                tail.contains(item)
                            }
                        }
                    }
                }
            }

            theorem tail_contains_imp_contains[T](head: T, tail: List[T], item: T) {
                tail.contains(item) implies List.cons(head, tail).contains(item)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_const_false() {
    let text = r#"
            define const_false[T](x: T) -> Bool {
                false
            }
            theorem goal[T](x: T) {
                not const_false(x)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_generic_let_attribute() {
    let text = r#"
            structure Box[T] {
                item: T
            }

            attributes Box[T] {
                let const_false: T -> Bool = function(x: T) {
                    false
                }
            }

            theorem goal {
                true
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_if_inside_match() {
    let text = r#"
            inductive List[T] {
                nil
                cons(T, List[T])
            }

            attributes List[T] {
                define remove_all(self, item: T) -> List[T] {
                    match self {
                        List.nil {
                            List.nil[T]
                        }
                        List.cons(head, tail) {
                            if head = item {
                                tail
                            } else {
                                List.cons(head, tail.remove_all(item))
                            }
                        }
                    }
                }
            }

            theorem nil_remove_all[T](item: T) {
                List.nil[T].remove_all(item) = List.nil[T]
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_typeclass_attribute_assigned_as_generic() {
    // This requires us to monomorphize to match equals[Color].
    let text = r#"
            typeclass F: Foo {
                op: (F, F) -> Bool

                self_true(x: F) {
                    x.op(x)
                }
            }

            define equals[T](x: T, y: T) -> Bool {
                x = y
            }

            inductive Color {
                red
                blue
            }

            instance Color: Foo {
                let op: (Color, Color) -> Bool = equals
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_multiple_type_variables() {
    let text = r#"
            inductive Nil[T] {
                nil
            }

            let map[T, U]: (Nil[T], T -> U) -> Nil[U] = axiom
            let morph[T]: Nil[T] -> Nil[T] = axiom

            theorem goal[T, U](items: Nil[T], f: T -> U) {
                map(items, f) = morph(map(items, f))
            } by {
                map(items, f) = Nil.nil[U]
                morph(map(items, f)) = Nil.nil[U]
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_mixin_instance() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/foo.ac",
        r#"
            inductive Foo {
                foo
            }
            let predicate[T]: T -> Bool = axiom

            typeclass S: Stuff {
                condition(s: S) {
                    predicate(s)
                }
            }
        "#,
    );
    p.mock(
        "/mock/bar.ac",
        r#"
            from foo import Foo, Stuff
            instance Foo: Stuff {}
        "#,
    );
    p.mock(
        "/mock/main.ac",
        r#"
            from foo import predicate
            from bar import Foo
            theorem goal {
                predicate(Foo.foo)
            }
        "#,
    );
    let (_processor, outcome, _) = prove_with_old_codegen(&mut p, "main", "goal");
    assert_eq!(outcome, Outcome::Success);
}

#[test]
fn test_proving_with_properties_of_base_typeclass() {
    let text = r#"
            typeclass F: Foo {
                property: Bool

                property_true {
                    F.property
                }
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            theorem goal[B: Bar] {
                B.property
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_deep_base_theorem() {
    let text = r#"
            typeclass F: Foo {
                add: (F, F) -> F

                comm(a: F, b: F) {
                    a + b = b + a
                }
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            typeclass B: Baz extends Bar {
                baz_property: Bool
            }

            theorem goal[B: Baz](a: B, b: B) {
                a + b = b + a
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_typeclass_attribute_semantics() {
    let text = r#"
            typeclass A: Addable {
                zero: A
                add: (A, A) -> A
            }
            
            attributes A: Addable {
                define plus_zero(self) -> A {
                    A.add(self, A.zero)
                }
            }
            
            theorem goal[A: Addable](x: A) {
                x.plus_zero = A.add(x, A.zero)
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_redefining_provided_attribute_works() {
    let text = r#"
            typeclass A: Arf {
                vacuous_condition {
                    true
                }
            }

            attributes A: Arf {
                define flag(self) -> Bool {
                    false
                }
            }

            inductive Foo {
                foo
            }

            instance Foo: Arf

            attributes Foo {
                define flag(self) -> Bool {
                    true
                }
            }

            theorem goal(f: Foo) {
                f.flag
            }
        "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_default_required_attribute() {
    let text = r#"
            typeclass A: Arf {
                foo: A
                bar: A
            }

            inductive Foo {
                foo
                bar
            }

            instance Foo: Arf

            let diff[A: Arf] = (A.foo != A.bar)

            theorem goal {
                diff[Foo]
            }
        "#;
    verify_succeeds(text);
}
