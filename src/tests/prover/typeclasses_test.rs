use crate::tests::support::*;
use crate::{project::Project, prover::Outcome};

// Prover coverage for instances, typeclasses, and related language features.

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
        any(List.cons(true, List.nil[Bool]))
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
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
        let normalized_goal = cursor.lowered_goal().expect("missing lowered goal");
        processor.set_lowered_goal(normalized_goal);
        let goal_kernel_context = &normalized_goal.kernel_context;

        let outcome = processor.search(crate::prover::ProverMode::Test, goal_kernel_context);
        assert_eq!(outcome, Outcome::Success);
        let cert = processor
            .prover()
            .make_cert(&goal_env.bindings, goal_kernel_context, true)
            .expect("make_cert failed");
        processor
            .check_cert(&cert, None, goal_kernel_context, &p, &goal_env.bindings)
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
fn test_semantics_of_let_satisfy_syntax() {
    let text = r#"
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one {
        zero != one
    }

    let witness: Nat satisfy {
        witness != one
    }

    theorem goal {
        witness != one
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_semantics_of_destructuring_unwrap_syntax() {
    let text = r#"
    type Nat: axiom

    inductive Option[T] {
        some(T)
        none
    }

    let n: Nat = axiom
    let wrapped = Option.some(n)
    let Option.some(unwrapped) = wrapped

    theorem goal {
        unwrapped = n
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_semantics_of_function_satisfy_syntax() {
    let text = r#"
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one {
        zero != one
    }

    let flip(a: Nat) -> b: Nat satisfy {
        a != b
    }

    theorem goal(a: Nat) {
        a != flip(a)
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_semantics_of_multivar_let_satisfy_syntax() {
    let text = r#"
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one {
        zero != one
    }

    let (x: Nat, y: Nat) satisfy {
        x != y
    }

    theorem goal {
        x != y
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
fn test_proving_with_polymorphic_destructuring() {
    let text = r#"
    type Int: axiom

    structure Rat {
        value: Int
    }

    inductive Option[T] {
        some(T)
        none
    }

    let i: Int = axiom
    let Option.some(rat_zero) = Option.some(Rat.new(i))

    theorem goal {
        rat_zero = Rat.new(i)
    }
    "#;
    verify_succeeds(text);
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
