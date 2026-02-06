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
fn test_prover_handles_parameterized_constants() {
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

// Simpler test: polymorphic goal using polymorphic axiom (no typeclass)
#[test]
fn test_polymorphic_goal_with_polymorphic_axiom_no_typeclass() {
    let text = r#"
    define foo[T](x: T) -> Bool {
        axiom
    }

    axiom always_foo[T](x: T) {
        foo(x)
    }

    theorem goal[T](a: T) {
        foo(a)
    }
    "#;
    verify_succeeds(text);
}

// Simpler test: polymorphic goal using polymorphic axiom (with typeclass)
#[test]
fn test_polymorphic_goal_with_external_axiom() {
    let text = r#"
    typeclass F: Foo {
        foo: F -> Bool
    }

    axiom always_foo[F: Foo](x: F) {
        x.foo
    }

    theorem goal[G: Foo](a: G) {
        a.foo
    }
    "#;
    verify_succeeds(text);
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
fn test_proving_with_parameterized_constant() {
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
fn test_proving_with_parameterized_inductive() {
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
fn test_proving_with_typeclass_attribute_assigned_as_generic() {
    // This requires instantiating type parameters to match equals[Color].
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

    let module_id = p.load_module_by_name("main").expect("load failed");
    let env = match p.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    for cursor in env.iter_goals() {
        let goal_env = cursor.goal_env().unwrap();

        let mut processor = crate::processor::Processor::with_imports(None, env).unwrap();
        processor.add_module_facts(&cursor).unwrap();
        let normalized_goal = cursor.normalized_goal().expect("missing normalized goal");
        processor.set_normalized_goal(normalized_goal);

        let outcome =
            processor.search(crate::prover::ProverMode::Test, &normalized_goal.normalizer);
        assert_eq!(outcome, Outcome::Success);
        let cert = processor
            .prover()
            .make_cert(&goal_env.bindings, &normalized_goal.normalizer, true)
            .expect("make_cert failed");
        processor
            .check_cert(
                &cert,
                None,
                &normalized_goal.normalizer,
                &p,
                &goal_env.bindings,
            )
            .expect("check_cert failed");
    }
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

#[test]
fn test_proving_with_anonymous_function() {
    let text = r#"
    type Nat: axiom
    let z: Nat = axiom
    let f1: (Nat -> Nat) -> Bool = axiom
    let f2: (Nat -> Nat) -> Bool = axiom

    axiom a1 {
        f1(function(x: Nat) { z })
    }

    axiom a2(h: Nat -> Nat) {
        f1(h) implies f2(h)
    }

    theorem goal {
        f2(function(x: Nat) { z })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_destructuring() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }

    let one = Nat.suc(Nat.zero)
    let two = Nat.suc(one)
    let Nat.suc(one_again) = two

    theorem goal {
        one_again = one
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_can_fail_with_destructuring() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }

    let Nat.suc(negative_one) = Nat.zero
    "#;
    verify_fails(text);
}

#[test]
fn test_prover_can_use_instance_forwards() {
    // One of two paired tests.
    // This direction should work - we can use instance relationship in subsequent proofs.
    let text = r#"
    typeclass F: Foo {
        property: Bool
    }

    typeclass B: Bar extends Foo {
        vacuous_condition(b: B) {
            b = b
        }
    }

    type MyType: axiom

    let b: Bool = axiom

    instance MyType: Foo {
        let property: Bool = b
    }

    axiom ax[B: Bar] {
        B.property
    }

    instance MyType: Bar

    theorem goal {
        MyType.property
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_prover_cannot_use_instance_backwards() {
    // One of two paired tests.
    // This direction should not work - we cannot use an instance relationship before it is proven.
    let text = r#"
    typeclass F: Foo {
        property: Bool
    }

    typeclass B: Bar extends Foo {
        vacuous_condition(b: B) {
            b = b
        }
    }

    type MyType: axiom

    let b: Bool = axiom

    instance MyType: Foo {
        let property: Bool = b
    }

    axiom ax[B: Bar] {
        B.property
    }

    theorem goal {
        MyType.property
    }

    instance MyType: Bar
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_inhabit_arbitrary_type() {
    // You should not be able to prove that every type has an element
    // just by satisfying "true".
    let text = r#"
    let inhabitant[T]: T satisfy {
        true
    }
    "#;
    // This should fail because T is not provably inhabited
    verify_fails(text);
}

#[test]
fn test_cannot_inhabit_arbitrary_type_self_equality() {
    // Self-equality is always true, so this is equivalent to "true".
    // It should still be rejected.
    let text = r#"
    let inhabitant[T]: T satisfy {
        inhabitant = inhabitant
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_inhabit_arbitrary_type_const_true() {
    // This should be rejected because T might not be inhabited.
    // Unlike the other tests, this one is NOT caught during normalization because
    // the variable is still used in const_true(inhabitant). Instead, the prover
    // correctly refuses to conclude a contradiction from foralls over uninhabited types.
    let text = r#"
    define const_true[T](x: T) -> Bool {
        true
    }

    let inhabitant[T]: T satisfy {
        const_true(inhabitant)
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_avoid_inhabitedness_through_resolution() {
    // When T is not inhabited, ax1 and ax2 do not imply goal.
    let text = r#"
    let foo[T]: Bool = axiom
    let bar[T]: T -> Bool = axiom

    axiom ax1[T](x: T) {
        bar(x) implies foo[T]
    }

    axiom ax2[T](x: T) {
        not bar(x) implies foo[T]
    }

    theorem goal[T] {
        foo[T]
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_cannot_avoid_inhabitedness_through_equality_reduction() {
    // This should be rejected because T might not be inhabited at all.
    let text = r#"
    theorem bar_or_not_bar[T](bar: T -> Bool) {
        exists(x: T) {
            bar(x) or not bar(x)
        }
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_can_inhabit_arbitrary_type_of_typeclass() {
    // This should be accepted, since any arbitrary P: Pointed is inhabited.
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed]: P satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_can_inhabit_arbitrary_type_of_extended_typeclass() {
    // This should be accepted, since any arbitrary P: Pointed is inhabited.
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    typeclass Q: Qux extends Pointed {
        foo: Q -> Bool
    }

    let inhabitant[Q: Qux]: Q satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_can_inhabit_function_type_when_codomain_inhabited() {
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed, Q]: Q -> P satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_cannot_inhabit_function_type_when_only_domain_inhabited() {
    let text = r#"
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed, Q]: P -> Q satisfy {
        true
    }
    "#;
    verify_fails(text);
}

#[test]
fn test_can_inhabit_identity_function_type() {
    let text = r#"
    let inhabitant[T]: T -> T satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_can_inhabit_list_type() {
    let text = r#"
    inductive List[T] {
        cons(List[T])
        nil
    }
    let inhabitant[T]: List[T] satisfy {
        true
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_inhabited_const() {
    let text = r#"
    let inhabited[T]: Bool = exists(x: T) {
        true
    }
    "#;
    // This definition should fail to normalize because it involves an exists
    // over a potentially uninhabited type T.
    let result = verify(text);
    assert!(result.is_err(), "expected an error, got {:?}", result);
}

/// Regression test: when a certificate uses a typeclass constraint from a function
/// defined in another module, but the current module hasn't directly imported that
/// typeclass BY NAME, the code generator should use lib(module).TypeclassName syntax.
///
/// This mirrors the real bug in binomial.ac where:
/// - CommRing extends AddCommMonoid (through the hierarchy)
/// - binomial.ac imports CommRing but not AddCommMonoid by name
/// - The prover creates a synthetic with AddCommMonoid constraint
/// - Verification fails because AddCommMonoid isn't in name_to_typeclass
///
/// The fix is for the code generator to substitute type variables that aren't valid
/// type names with concrete types that implement the required typeclass.
#[test]
fn test_synthetic_with_unimported_typeclass_constraint() {
    let mut p = Project::new_mock();

    // Base typeclass
    p.mock(
        "/mock/monoid.ac",
        r#"
    typeclass M: Monoid {
        zero: M
        add: (M, M) -> M
    }

    // A function with Monoid constraint that has a forall (creates skolem)
    theorem monoid_thm[T: Monoid](f: T -> T, x: T) {
        (forall(y: T) { f(y) = y }) implies f(x) = x
    }
    "#,
    );

    // Extended typeclass
    p.mock(
        "/mock/ring.ac",
        r#"
    from monoid import Monoid

    typeclass R: Ring extends Monoid {
        one: R
        mul: (R, R) -> R
    }
    "#,
    );

    // Wrapper that exports monoid_thm but NOT Monoid by name
    p.mock(
        "/mock/wrapper.ac",
        r#"
    from monoid import monoid_thm
    "#,
    );

    // Main module:
    // - imports Ring from ring.ac (which imports Monoid, so typeclass_defs has Monoid)
    // - imports monoid_thm from wrapper (NOT from monoid.ac)
    // - does NOT directly import Monoid by name
    // So main has Monoid in typeclass_defs but NOT in name_to_typeclass
    p.mock(
        "/mock/main.ac",
        r#"
    from ring import Ring
    from wrapper import monoid_thm

    // This goal uses monoid_thm with Ring (which extends Monoid).
    // The prover creates a skolem with [T: Monoid] constraint.
    // The code generator must use lib(monoid).Monoid format.
    theorem goal[R: Ring](f: R -> R, x: R) {
        (forall(y: R) { f(y) = y }) implies f(x) = x
    } by {
        monoid_thm(f, x)
    }
    "#,
    );

    let module_id = p.load_module_by_name("main").expect("load failed");
    let env = match p.get_module_by_id(module_id) {
        crate::module::LoadState::Ok(env) => env,
        crate::module::LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    // Check that Monoid is NOT in name_to_typeclass
    assert!(
        !env.bindings.has_typeclass_name("Monoid"),
        "Monoid should NOT be in name_to_typeclass for main module"
    );

    // Run the prover and generate a certificate
    let cursor = env.iter_goals().next().expect("expected a goal in main");
    let goal_env = cursor.goal_env().unwrap();

    let mut processor = crate::processor::Processor::with_imports(None, env).unwrap();
    processor.add_module_facts(&cursor).unwrap();
    let normalized_goal = cursor.normalized_goal().expect("missing normalized goal");
    processor.set_normalized_goal(normalized_goal);

    let outcome = processor.search(crate::prover::ProverMode::Test, &normalized_goal.normalizer);
    assert_eq!(outcome, Outcome::Success);

    // Generate the certificate
    let cert = processor
        .prover()
        .make_cert(&goal_env.bindings, &normalized_goal.normalizer, true)
        .expect("make_cert failed");

    // Debug: print the certificate
    eprintln!("Certificate proof:");
    if let Some(proof) = &cert.proof {
        for (i, step) in proof.iter().enumerate() {
            eprintln!("  Step {}: {}", i, step);
        }
    }

    // The certificate should verify successfully
    // (If the code generator correctly uses lib(monoid).Monoid format)
    processor
        .check_cert(
            &cert,
            None,
            &normalized_goal.normalizer,
            &p,
            &goal_env.bindings,
        )
        .expect("check_cert should succeed");
}

/// Regression test: when a synthetic has multiple type parameters and a function type
/// between them (like `G -> H`), the code generator must preserve the correct order
/// of type parameters in all foralls within the synthetic definition.
///
/// This reproduces a bug in group.ac where `trivial_hom_is_hom[G: Group, H: Group]`
/// generates a certificate with swapped type parameters in one of the foralls:
/// - First forall correctly uses `x0: T0 -> T1`
/// - Second forall incorrectly uses `x3: T1 -> T0` (swapped!)
///
/// This causes type mismatch errors during certificate verification.
#[test]
fn test_synthetic_with_multiple_type_params_function_type() {
    verify_succeeds(
        r#"
    typeclass M: Monoid {
        1: M
        mul: (M, M) -> M

        mul_one_left(a: M) {
            M.mul(M.1, a) = a
        }

        mul_one_right(a: M) {
            M.mul(a, M.1) = a
        }
    }

    // A function that takes a mapping between two Monoid types
    // and checks if it preserves the operation
    define is_hom[G: Monoid, H: Monoid](f: G -> H) -> Bool {
        forall(a: G, b: G) {
            f(G.mul(a, b)) = H.mul(f(a), f(b))
        }
    }

    // The trivial homomorphism - maps everything to identity
    let trivial_hom[G: Monoid, H: Monoid]: G -> H = function(a: G) { H.1 }

    // This theorem creates a synthetic with two type parameters and a function type
    // The bug: type parameters get swapped in one of the foralls
    theorem trivial_hom_is_hom[G: Monoid, H: Monoid](a: G, b: G) {
        is_hom[G, H](trivial_hom[G, H])
    }
    "#,
    );
}

/// Reproduces a bug where value parameter `item` incorrectly gets type args `item[T]`.
/// Key ingredients: polymorphic theorem, value param `item: T`, local define with 2 params,
/// forall/if structure, and induction capturing `item`.
#[test]
fn test_value_param_incorrectly_gets_type_args() {
    verify_succeeds(
        r#"
    inductive MyList[T] {
        nil
        cons(T, MyList[T])
    }

    define contains[T](list: MyList[T], item: T) -> Bool {
        match list {
            MyList.nil[T] { false }
            MyList.cons(head, tail) { head = item or contains(tail, item) }
        }
    }

    // Removes duplicate elements - calls contains internally
    define dedup[T](list: MyList[T]) -> MyList[T] {
        match list {
            MyList.nil[T] { MyList.nil[T] }
            MyList.cons(head, tail) {
                if contains(tail, head) {
                    dedup(tail)
                } else {
                    MyList.cons(head, dedup(tail))
                }
            }
        }
    }

    theorem test[T](list: MyList[T], item: T) {
        contains(dedup(list), item) = contains(list, item)
    } by {
        define p(l: MyList[T], x: T) -> Bool {
            contains(dedup(l), x) = contains(l, x)
        }

        forall(head: T, tail: MyList[T]) {
            if p(tail, item) {
                if contains(tail, head) {
                    contains(tail, item) implies contains(MyList.cons(head, tail), item)
                    contains(MyList.cons(head, tail), item) = contains(tail, item)
                } else {
                    contains(MyList.cons(head, tail), item) implies contains(MyList.cons(head, dedup(tail)), item)
                    contains(MyList.cons(head, tail), item) = contains(MyList.cons(head, dedup(tail)), item)
                    p(MyList.cons(head, tail), item)
                }
                p(MyList.cons(head, tail), item)
            }
        }

        MyList.induction(function(l: MyList[T]) {
            p(l, item)
        })
    }
    "#,
    );
}

/// Reproduces a bug where `f(item)` claim is not obviously true.
/// Key: theorem has function param `f: T -> Bool` and value param `item: T`,
/// and `f(item)` appears in proof with induction capturing both.
#[test]
fn test_function_param_application_not_obvious() {
    let code = r#"
    inductive MyList[T] {
        nil
        cons(T, MyList[T])
    }

    define contains[T](list: MyList[T], item: T) -> Bool {
        match list {
            MyList.nil[T] { false }
            MyList.cons(head, tail) { head = item or contains(tail, item) }
        }
    }

    define filter[T](list: MyList[T], f: T -> Bool) -> MyList[T] {
        match list {
            MyList.nil[T] { MyList.nil[T] }
            MyList.cons(head, tail) {
                if f(head) {
                    MyList.cons(head, filter(tail, f))
                } else {
                    filter(tail, f)
                }
            }
        }
    }

    theorem test[T](list: MyList[T], f: T -> Bool, item: T) {
        contains(filter(list, f), item) implies (contains(list, item) and f(item))
    } by {
        define p(l: MyList[T], x: T) -> Bool {
            contains(filter(l, f), x) implies (contains(l, x) and f(x))
        }

        forall(head: T, tail: MyList[T]) {
            if p(tail, item) {
                if contains(filter(MyList.cons(head, tail), f), item) {
                    if contains(filter(tail, f), item) {
                    } else {
                        f(head)
                        head = item
                        f(item) and contains(MyList.cons(head, tail), item)
                    }
                }
                p(MyList.cons(head, tail), item)
            }
        }

        MyList.induction(function(l: MyList[T]) {
            p(l, item)
        })
    }
    "#;

    // Test the goal that was crashing with "f(item) not obviously true" before the fix
    // This goal uses a multi-literal short clause in resolution that wasn't being tracked
    assert_eq!(
        verify_line(code, "p(MyList.cons(head, tail), item)").unwrap(),
        Outcome::Success
    );
}

// Regression test for a bug where polymorphic structures containing functions with
// if-then-else expressions returning non-Bool types would cause a type mismatch
// during clause validation. The issue was with how synthetic atoms were typed when
// normalizing function definitions inside define statements.
#[test]
fn test_polymorphic_structure_with_function_if_then_else() {
    let text = r#"
    inductive Nat {
        zero
        suc(Nat)
    }

    structure Wrapper[T] {
        func: T -> Nat
    }

    attributes Wrapper[T] {
        define modify(self, item: T) -> Wrapper[T] {
            Wrapper.new(function(x: T) {
                if x = item {
                    self.func(x).suc
                } else {
                    self.func(x)
                }
            })
        }
    }

    theorem goal[T](w: Wrapper[T], item: T) {
        w.modify(item) = w.modify(item)
    }
    "#;
    verify_succeeds(text);
}

// Reproduces a bug where the prover needs to instantiate a polymorphic axiom
// with an arbitrary type, resulting in certificate code like "let s2: x0 satisfy { true }"
// which is invalid because x0 is not a valid type name.
#[test]
fn test_polymorphic_axiom_chain_needs_arbitrary_type() {
    let text = r#"
    let foo: Bool = axiom
    let baz: Bool = axiom

    define bar[T](x: T) -> Bool {
        axiom
    }

    axiom foo_imp_bar[T](x: T) {
        foo implies bar[T](x)
    }

    axiom bar_imp_baz[T](x: T) {
        bar[T](x) implies baz
    }

    theorem goal {
        foo implies baz
    }
    "#;
    verify_succeeds(text);
}

// Reproduces a bug with dependently typed synthetics in polymorphic let...satisfy.
// The synthetic s0 has type T0 where T0 is a type parameter.
//
// The code is valid as regular Acorn code (module loads fine), but the certificate
// checker fails with "value s0 has unresolved type".
//
// The original bug: cargo run --profile release --features polymorphic,validate -- reprove ordered_group
#[test]
fn test_dependently_typed_synthetic() {
    use crate::processor::Processor;

    let (processor, bindings, normalized_goal) = Processor::test_goal(
        r#"
        typeclass T: Grp {
            1: T
        }

        define has_finite_order[T: Grp](x: T) -> Bool { axiom }

        let is_torsion_free[T: Grp] = forall(x: T) { not has_finite_order(x) or x = T.1 }

        theorem goal[G: Grp] { is_torsion_free[G] }
        "#,
    );

    // This certificate line is valid Acorn code, but the certificate checker fails on it.
    // s0 has type T0 where T0 is a type parameter constrained to Grp.
    let cert_line = "let s0[T0: Grp]: T0 satisfy { forall(x0: T0) { not is_torsion_free[T0] or not has_finite_order(x0) or Grp.1[T0] = x0 } and (has_finite_order(s0) or is_torsion_free[T0]) and (s0 != Grp.1[T0] or is_torsion_free[T0]) }";

    processor.test_parse_code(cert_line, &bindings, &normalized_goal.normalizer);
}

// Reproduces a bug where a polymorphic synthetic causes
// "BoundVariable(0) in PDT search - should have been substituted".
//
// Based on the certificate from ordered_group for ordered_imp_torsion_free.
#[test]
fn test_polymorphic_synthetic_claim() {
    use crate::checker::Checker;
    use crate::processor::Processor;
    use crate::project::Project;
    use std::borrow::Cow;

    let (_processor, bindings, normalized_goal) = Processor::test_goal(
        r#"
        typeclass T: Grp {
            1: T
        }

        define has_finite_order[T: Grp](x: T) -> Bool { axiom }

        let is_torsion_free[T: Grp] = forall(x: T) { not has_finite_order(x) or x = T.1 }

        theorem goal[G: Grp] { is_torsion_free[G] }
        "#,
    );

    let project = Project::new_mock();
    let normalizer = normalized_goal.normalizer.clone();
    let mut normalizer_cow = Cow::Owned(normalizer);
    let mut bindings_cow = Cow::Borrowed(&bindings);

    // Parse the polymorphic synthetic
    Checker::parse_code_line(
        "let s0[T0: Grp]: T0 satisfy { forall(x0: T0) { not is_torsion_free[T0] or not has_finite_order(x0) or Grp.1[T0] = x0 } and (has_finite_order(s0) or is_torsion_free[T0]) and (s0 != Grp.1[T0] or is_torsion_free[T0]) }",
        &project,
        &mut bindings_cow,
        &mut normalizer_cow,
    )
    .expect("let-satisfy should parse");

    // Parse the claim - this triggers the bug when s0's type is looked up.
    // s0 has type Variable(T0) outside the let...satisfy block, so we need
    // explicit type params. Using G from the theorem's scope.
    Checker::parse_code_line(
        "has_finite_order[G](s0[G]) or is_torsion_free[G]",
        &project,
        &mut bindings_cow,
        &mut normalizer_cow,
    )
    .expect("claim should parse");
}

// Demonstrates that certificate type parameters are currently global, not step-local.
// If type params were scoped per line, both parse_code_line calls below would succeed.
#[test]
#[ignore = "demonstrates current bug: type params are not step-local across certificate steps"]
fn test_certificate_type_params_are_not_step_local() {
    use crate::checker::Checker;
    use crate::processor::Processor;
    use crate::project::Project;
    use std::borrow::Cow;

    let (_processor, bindings, normalized_goal) = Processor::test_goal(
        r#"
        typeclass T: Grp {
            1: T
        }

        define has_finite_order[T: Grp](x: T) -> Bool { axiom }

        let is_torsion_free[T: Grp] = forall(x: T) { not has_finite_order(x) or x = T.1 }

        theorem goal[G: Grp] { is_torsion_free[G] }
        "#,
    );

    let project = Project::new_mock();
    let normalizer = normalized_goal.normalizer.clone();
    let mut normalizer_cow = Cow::Owned(normalizer);
    let mut bindings_cow = Cow::Borrowed(&bindings);

    Checker::parse_code_line(
        "let s0[T0: Grp]: T0 satisfy { forall(x0: T0) { not is_torsion_free[T0] or not has_finite_order(x0) or Grp.1[T0] = x0 } and (has_finite_order(s0) or is_torsion_free[T0]) and (s0 != Grp.1[T0] or is_torsion_free[T0]) }",
        &project,
        &mut bindings_cow,
        &mut normalizer_cow,
    )
    .expect("first line should parse");

    // This currently fails because T0 remains bound globally after the first line.
    Checker::parse_code_line(
        "let s1[T0: Grp]: T0 satisfy { forall(x0: T0) { not is_torsion_free[T0] or not has_finite_order(x0) or Grp.1[T0] = x0 } and (has_finite_order(s1) or is_torsion_free[T0]) and (s1 != Grp.1[T0] or is_torsion_free[T0]) }",
        &project,
        &mut bindings_cow,
        &mut normalizer_cow,
    )
    .expect("second line should parse if type params were step-local");
}
