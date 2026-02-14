use crate::elaborator::environment::Environment;

#[test]
fn test_env_with_typeclass() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
}

#[test]
fn test_env_with_bad_typeclass() {
    let mut env = Environment::test();
    env.bad(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> Magma
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_in_define_template() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define true_fn[T: Magma](a: T) -> Bool {
                true
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared[T: Magma](a: T) -> T {
                Magma.mul(a, a)
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_instance_methods() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared[T: Magma](a: T) -> T {
                a.mul(a)
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_in_theorem_template() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            theorem wrong_but_syntactic[Q: Magma](a: Q, b: Q) {
                a.mul(b) = b.mul(a)
            }
            "#,
    );
}

#[test]
fn test_env_typechecking_with_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
    env.bad(
        r#"
            theorem wrong_by_typecheck[Q: Magma](a: Q, b: Q) {
                a.mul(b) = b.mul
            }
            "#,
    );
}

#[test]
fn test_env_typeclass_in_structure() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            structure MagmaPair[T: Magma] {
                first: T
                second: T
            }

            attributes MagmaPair[T: Magma] {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
}

#[test]
fn test_env_typeclasses_match_between_structure_and_class() {
    let mut env = Environment::test();
    // Attributes can add more restrictive typeclass constraints than the base structure
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            structure MagmaPair[T] {
                first: T
                second: T
            }

            attributes MagmaPair[T: Magma] {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
}

#[test]
fn test_env_operator_on_typeclass() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            // Not true but syntactically valid
            theorem commutative[T: Magma](a: T, b: T) {
                a * b = b * a
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_define() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }

            instance State: Magma {
                define mul(self, other: State) -> State {
                    if self = State.clean and other = State.clean {
                        State.clean
                    } else {
                        State.dirty
                    }
                }
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_needs_all_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass B: Bimagma {
                mul1: (B, B) -> B
                mul2: (B, B) -> B
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    // Needs to also define mul2
    env.bad(
        r#"
            instance State: Bimagma {
                define mul1(self, other: State) -> State {
                    State.clean
                }
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_no_extra_define() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    env.bad(
        r#"
            instance State: Magma {
                define mul(self, other: State) -> State {
                    State.clean
                }
                define add(self, other: State) -> State {
                    State.clean
                }
            }
            "#,
    );
}

#[test]
fn test_env_instance_defines_must_match_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    env.bad(
        r#"
            instance State: Magma {
                define mul(self, other: State) -> Bool {
                    true
                }
            }
            "#,
    );
}

#[test]
fn test_env_using_typeclass_methods() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive State {
                clean
                dirty
            }

            instance State: Magma {
                define mul(self, other: State) -> State {
                    if self = State.clean and other = State.clean {
                        State.clean
                    } else {
                        State.dirty
                    }
                }
            }

            theorem commutative(a: State, b: State) {
                Magma.mul(a, b) = Magma.mul(b, a)
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_let() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }

            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
            }
            "#,
    );
}

#[test]
fn test_env_instance_statement_no_extra_let() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }
            "#,
    );
    env.bad(
        r#"
            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
                let other: Z2 = Z2.one
            }
            "#,
    );
}

#[test]
fn test_env_instance_lets_must_match_type() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }
            "#,
    );
    env.bad(
        r#"
            instance Z2: PointedSet {
                let basepoint: Bool = true
            }
            "#,
    );
}

#[test]
fn test_env_parametrizing_typeclass_constant() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }

            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
            }

            theorem goal {
                Z2.zero = PointedSet.basepoint[Z2]
            }
            "#,
    );
}

#[test]
fn test_env_forbid_instance_on_alias() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            type Foo: axiom
            type Bar: Foo
            "#,
    );
    env.bad(
        r#"
            instance Bar: Flagged {
                let flag: Bool = true
            }
            "#,
    );
}

#[test]
fn test_env_arbitrary_type_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            theorem goal[F: Flagged] {
                F.flag or not F.flag
            }
            "#,
    );
}

#[test]
fn test_env_bool_not_instance_of_anything() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        instance Foo: Flagged {
            let flag: Bool = true
        }
        define get_flag[F: Flagged](x: F) -> Bool {
            F.flag
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal {
            get_flag(true)
        }
        "#,
    );
}

#[test]
fn test_env_typechecking_captures_instance_relationships() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        type Bar: axiom
        instance Bar: Flagged {
            let flag: Bool = true
        }
        define get_flag[F: Flagged](x: F) -> Bool {
            F.flag
        }
        theorem goal_bar(b: Bar) {
            get_flag(b)
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal_foo(f: Foo) {
            get_flag(f)
        }
        "#,
    );
}

#[test]
fn test_env_typeclasses_can_have_conditions() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass S: Singleton {
            value: S

            unique(x: S) {
                x = S.value
            }
        }

        theorem are_equal[S: Singleton](a: S, b: S) {
            a = b
        } by {
            Singleton.unique(a)
            Singleton.unique(b)
        }
        "#,
    );
}

#[test]
fn test_env_instance_statement_accepts_by_block() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass S: Singleton {
            value: S

            unique(x: S) {
                x = S.value
            }
        }

        inductive Z1 {
            zero
        }

        instance Z1: Singleton {
            let value: Z1 = Z1.zero
        } by {
            forall(x: Z1) {
                x = Z1.zero
            }
        }
        "#,
    );
}

#[test]
fn test_env_must_resolve_typeclass_constants() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass P: PointedSet {
            zero: P
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal {
            PointedSet.zero = PointedSet.zero
        }
        "#,
    );
}

#[test]
fn test_env_let_statements_with_params() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass P: PointedSet {
            zero: P
        }

        let z[P: PointedSet]: P = P.zero

        define is_zero[P: PointedSet](x: P) -> Bool {
            z[P] = x
        }
        "#,
    );
}

#[test]
fn test_typeclass_codegen() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                inverse: F -> F
                add: (F, F) -> F
                bar: F
            }

            let qux[F: Foo]: Bool = axiom

            theorem goal[F: Foo](f: F) {
                true
            }
        "#,
    );

    env.get_bindings("goal").expect_good_code("f.inverse");
    env.get_bindings("goal").expect_good_code("f + f");
    env.get_bindings("goal").expect_good_code("F.bar");
    env.get_bindings("goal").expect_good_code("F.add");
    env.get_bindings("goal").expect_good_code("qux[F]");
}

#[test]
fn test_instance_codegen() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                inverse: F -> F
                bar: F
            }

            inductive Qux {
                qux
                quux
            }

            let other: Qux -> Qux = axiom

            instance Qux: Foo {
                let inverse: Qux -> Qux = other
                let bar: Qux = Qux.qux
            }
        "#,
    );

    env.bindings.expect_good_code("Qux.bar");
    env.bindings.expect_good_code("Qux.qux.inverse");
}

#[test]
fn test_env_handles_bad_typeclass_name_in_theorem() {
    let mut env = Environment::test();
    env.bad(
        r#"
            theorem goal[F: Foo] {
                true
            }
        "#,
    );
}

#[test]
fn test_env_handles_bad_typeclass_name_in_class_param() {
    let mut env = Environment::test();
    env.add(
        r#"
            inductive List[T] {
                nil
                cons(T, List[T])
            }
            "#,
    );
    env.bad(
        r#"
            attributes List[F: Foo] {
                let b: Bool = true
            }
        "#,
    );
}

#[test]
fn test_env_basic_typeclass_extension() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar extends Foo {
                property_true(b: B) {
                    b.property
                }
            }

            inductive Qux {
                qux
            }

            attributes Qux {
                define q(self) -> Bool {
                    true
                }
            }

            instance Qux: Foo {
                let property: Qux -> Bool = Qux.q
            }

            instance Qux: Bar {
            }
            "#,
    );
}

#[test]
fn test_env_instances_of_extended_must_be_base() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar extends Foo {
                property_true(b: B) {
                    b.property
                }
            }

            inductive Qux {
                qux
            }
        "#,
    );
    // Should fail because Qux is not a Foo.
    env.bad(
        r#"
            instance Qux: Bar {
            }
        "#,
    );
}

#[test]
fn test_env_no_redefining_property_in_extension() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
        "#,
    );
    // Should fail because property can't be redefined.
    env.bad(
        r#"
            typeclass B: Bar extends Foo {
                property: B -> Bool
            }
        "#,
    );
}

#[test]
fn test_env_empty_zero_extension_not_ok() {
    let mut env = Environment::test();
    env.bad(
        r#"
            typeclass F: Foo {
            }
        "#,
    );
}

#[test]
fn test_env_empty_single_extension_not_ok() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
        "#,
    );
    env.bad(
        r#"
            typeclass B: Bar extends Foo {
            }
        "#,
    );
}

#[test]
fn test_env_empty_double_extension_ok() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
            typeclass B: Bar {
                other_property: B -> Bool
            }
            typeclass Q: Qux extends Foo, Bar {
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_no_block_syntax() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }
            typeclass B: Bar {
                other_property: B -> Bool
            }
            typeclass Qux extends Foo, Bar
        "#,
    );
}

#[test]
fn test_env_instance_no_block_syntax() {
    let mut env = Environment::test();
    env.add(
        r#"
            // Define a simple type
            type Nat: axiom
            
            // A typeclass with only conditions, no constants
            typeclass T: Trivial {
                reflexive(x: T) {
                    x = x
                }
            }
            
            // This should work with no-block syntax since no definitions are needed
            instance Nat: Trivial
        "#,
    );
}

#[test]
fn test_env_extending_incompatible_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar {
                property: B -> Bool
            }
        "#,
    );
    // Should fail because Foo and Bar are incompatible.
    env.bad(
        r#"
            typeclass Q: Qux extends Foo, Bar {
            }
        "#,
    );
}

#[test]
fn test_env_allow_diamonds() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                property: F -> Bool
            }

            typeclass B: Bar extends Foo{
                bar_property: B -> Bool
            }

            typeclass Q: Qux extends Foo {
                qux_property: Q -> Bool
            }

            typeclass Z: Zap extends Bar, Qux {
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_with_numeral_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                0: F
            }

            typeclass B: Bar extends Foo{
                bar_property: B -> Bool
            }

            theorem goal[B: Bar](b: B) {
                B.0 = Foo.0[B]
            }
        "#,
    );
}

#[test]
fn test_env_numerals_in_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                0: F
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo {
                let 0: Bar = Bar.bar
            }
        "#,
    );
}

#[test]
fn test_env_type_inference_for_numerals_in_typeclasses() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                0: F
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo {
                let 0 = Bar.bar
            }
        "#,
    );
}

#[test]
fn test_env_basic_typeclass_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                trivial(x: F) {
                    x = x
                }
            }

            attributes F: Foo {
                let flag: Bool = false
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            theorem test_typeclass_attribute(b: Bar) {
                Foo.flag[Bar] = false
            }

            theorem test_instance_attribute(b: Bar) {
                Bar.flag = false
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_attributes_with_let_satisfy() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                trivial(x: F) {
                    x = x
                }
            }

            define ok[T: Foo](x: T) -> Bool {
                axiom
            }

            attributes F: Foo {
                let witness: F satisfy {
                    ok[F](witness)
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            theorem goal {
                ok[Bar](Foo.witness[Bar])
            } by {
                ok[Bar](Foo.witness[Bar])
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_attributes_with_function_satisfy() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                trivial(x: F) {
                    x = x
                }
            }

            attributes F: Foo {
                let choose(a: F) -> b: F satisfy {
                    a = b
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            theorem goal(b: Bar) {
                Foo.choose[Bar](b) = b
            } by {
                Foo.choose[Bar](b) = b
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_attributes_require_instance_name() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                trivial(x: F) {
                    x = x
                }
            }
        "#,
    );
    env.bad(
        r#"
            attributes Foo {
                let flag: Bool = false
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_attributes_no_type_params() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                trivial(x: F) {
                    x = x
                }
            }
        "#,
    );
    env.bad(
        r#"
            attributes F: Foo[T] {
                let flag: Bool = false
            }
        "#,
    );
}

#[test]
fn test_env_duplicate_typeclass_attributes_error() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass A: Alpha {
                shared_attr: A -> Bool
            }
            
            typeclass B: Beta {
                shared_attr: B -> Bool
            }
            
            inductive TestType {
                test_val
            }
            
            instance TestType: Alpha {
                let shared_attr = function(x: TestType) { true }
            }
            
            instance TestType: Beta {
                let shared_attr = function(x: TestType) { false }
            }
        "#,
    );

    // This should error because TestType.shared_attr is ambiguous
    env.bad(
        r#"
            theorem test_ambiguous_attribute(t: TestType) {
                t.shared_attr = true
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_attributes_with_self() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                trivial(x: F) {
                    x = x
                }
            }
            
            attributes F: Foo {
                define is_foo(self) -> Bool {
                    true
                }
            }
            
            inductive Bar {
                bar
            }
            
            instance Bar: Foo
            
            theorem test_bar_is_foo(b: Bar) {
                b.is_foo
            }
        "#,
    );
}

#[test]
fn test_env_typeclass_operators() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass A: Addable {
                flag: Bool
            }
            
            attributes A: Addable {
                define add(self, other: A) -> A {
                    self
                }
            }
            
            typeclass B: MoreAddable extends Addable {
                zero: B
            }
            
            inductive MyNum {
                zero
            }
            
            instance MyNum: Addable {
                let flag = true
            }
            
            instance MyNum: MoreAddable {
                let zero = MyNum.zero
            }
            
            // Test operator on concrete instance type
            theorem test_concrete_add {
                MyNum.zero + MyNum.zero = MyNum.zero
            }
            
            // Test operator on generic type with Addable constraint
            theorem test_generic_addable[T: Addable](a: T, b: T) {
                a + b = a
            }
            
            // Test operator on generic type with MoreAddable constraint
            theorem test_generic_more_addable[T: MoreAddable](a: T) {
                a + T.zero = a
            }
        "#,
    );
}

#[test]
fn test_env_constant_attributes_on_extensions() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                value: F -> Bool
            }
            
            attributes F: Foo {
                let flag: Bool = true
            }
            
            typeclass B: Bar extends Foo {
                other_value: B -> Bool
            }
            
            inductive TestType {
                test_val
            }
            
            instance TestType: Foo {
                let value = function(x: TestType) { true }
            }
            
            instance TestType: Bar {
                let other_value = function(x: TestType) { false }
            }
            
            theorem test_bar_flag {
                Bar.flag[TestType] = true
            }
            
            theorem test_instance_flag(t: TestType) {
                TestType.flag = true
            }
        "#,
    );
}

#[test]
fn test_accessing_inherited_required_attributes() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                foo: F -> Bool
                foo_flag: Bool
            }

            typeclass B: Bar extends Foo {
                bar_flag: Bool
            }

            theorem goal[B: Bar](b: B) {
                b.foo = B.foo_flag
            }
        "#,
    );
}

#[test]
fn test_required_attributes_default_to_same_name() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                flag: Bool
            }

            inductive Bar {
                bar
            }

            attributes Bar {
                let flag: Bool = true
            }

            instance Bar: Foo
        "#,
    );
}

#[test]
fn test_required_attributes_type_mismatch() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                flag: Bool
            }

            inductive Bar {
                bar
            }

            attributes Bar {
                let flag: Bar = Bar.bar
            }
        "#,
    );
    env.bad(
        r#"
            instance Bar: Foo
        "#,
    );
}

#[test]
fn test_method_binding_in_typeclass_conditions() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom

            // Helper function for testing
            let cardinality_is[T]: Nat -> Bool = axiom

            typeclass F: FiniteField {
                n: Nat

                has_cardinality {
                    cardinality_is<F>(F.n)
                }
            }
        "#,
    );

    // This should fail with a helpful error message
    let error = env.bad(
        r#"
            typeclass F2: FiniteField2 {
                n: Nat

                alt_has_cardinality(f: F2) {
                    cardinality_is<F2>(f.n)
                }
            }
        "#,
    );

    // Should get a helpful message about accessing via the type, not the value
    assert!(
        error.contains("type-level attribute") || error.contains("Use 'F2.n'"),
        "unexpected error message: {}",
        error
    );
}

#[test]
fn test_attribute_with_typeclass_parameter() {
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome

        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        // Actually use the splits method on Set[Color]
        theorem test_splits_on_color_set(s: Set[Color]) {
            s.splits or not s.splits
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_method_usage() {
    // Test that we can actually call the method on concrete types that satisfy the typeclass
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome

        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }

            define has_both(self, a: T, b: T) -> Bool {
                self.contains(a) and self.contains(b)
            }
        }

        let color_set: Set[Color] = axiom

        theorem test_call_splits {
            color_set.splits = color_set.splits
        }

        theorem test_call_has_both {
            color_set.has_both(Color.red, Color.blue) or true
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_with_multiple_instances() {
    // Test that attributes work on multiple types that implement the typeclass
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome
        instance Size: Twosome

        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        let color_set: Set[Color] = axiom
        let size_set: Set[Size] = axiom

        // Both should work since both Color and Size implement Twosome
        theorem test_color_splits {
            color_set.splits or not color_set.splits
        }

        theorem test_size_splits {
            size_set.splits or not size_set.splits
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_with_type_params() {
    // Test that typeclass-constrained attributes can have additional type parameters
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome

        attributes Set[T: Twosome] {
            define map_to<U>(self, f: T -> U) -> Set[U] {
                Set[U].new(function(u: U) {
                    exists(t: T) {
                        self.contains(t) and f(t) = u
                    }
                })
            }
        }

        type Nat: axiom
        let color_set: Set[Color] = axiom
        let f: Color -> Nat = axiom

        theorem test_map_to {
            color_set.map_to(f) = color_set.map_to(f)
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_type_syntax() {
    // Test different ways to access typeclass-constrained attributes
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome

        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        let color_set: Set[Color] = axiom

        // Both syntaxes should work
        theorem test_dot_syntax {
            color_set.splits or not color_set.splits
        }

        theorem test_type_syntax {
            Set.splits(color_set) or not Set.splits(color_set)
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_should_fail_on_non_instance() {
    // Test that typeclass-constrained attributes don't work on types that don't implement the typeclass
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        type Nat: axiom
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome
        // Note: Nat does NOT implement Twosome

        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        let nat_set: Set[Nat] = axiom
        "#,
    );

    // This should fail because Nat doesn't implement Twosome
    env.bad(
        r#"
        theorem test_nat_splits {
            nat_set.splits
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_combining_with_generic() {
    // Test that we can have both generic and typeclass-constrained attributes on the same type
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome

        // Generic attribute that works on all Set[K]
        attributes Set[K] {
            define is_empty(self) -> Bool {
                forall(k: K) {
                    not self.contains(k)
                }
            }
        }

        // Typeclass-constrained attribute that only works on Set[T: Twosome]
        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        let color_set: Set[Color] = axiom

        // Both should work on Set[Color]
        theorem test_generic_method {
            color_set.is_empty or not color_set.is_empty
        }

        theorem test_typeclass_method {
            color_set.splits or not color_set.splits
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_with_recursive_method() {
    // Test typeclass-constrained attributes with recursive structures
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive List[T] {
            nil
            cons(T, List[T])
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome

        attributes List[T: Twosome] {
            define has_distinct_pair(self) -> Bool {
                match self {
                    List.nil {
                        false
                    }
                    List.cons(head, tail) {
                        match tail {
                            List.nil {
                                false
                            }
                            List.cons(second, rest) {
                                head != second or tail.has_distinct_pair
                            }
                        }
                    }
                }
            }
        }

        let color_list: List[Color] = axiom

        theorem test_distinct_pair {
            color_list.has_distinct_pair or not color_list.has_distinct_pair
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_with_concrete_params() {
    // Test that we can have attributes on Set[Color] AND Set[T: Twosome]
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        inductive Size {
            small
            large
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        instance Color: Twosome
        instance Size: Twosome

        // Attribute specific to Set[Color]
        attributes Set[Color] {
            define has_red(self) -> Bool {
                self.contains(Color.red)
            }
        }

        // Attribute for all Set[T: Twosome]
        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        let color_set: Set[Color] = axiom
        let size_set: Set[Size] = axiom

        // Set[Color] should have both has_red (specific) and splits (typeclass)
        theorem test_color_has_red {
            color_set.has_red or not color_set.has_red
        }

        theorem test_color_splits {
            color_set.splits or not color_set.splits
        }

        // Set[Size] should only have splits (typeclass), not has_red
        theorem test_size_splits {
            size_set.splits or not size_set.splits
        }
        "#,
    );

    // This should fail - Set[Size] doesn't have has_red
    env.bad(
        r#"
        theorem test_size_has_red {
            size_set.has_red
        }
        "#,
    );
}

#[test]
fn test_typeclass_attribute_multiple_constraints() {
    // Test attributes with multiple typeclass constraints
    let mut env = Environment::test();
    env.add(
        r#"
        inductive Color {
            red
            blue
        }
        structure Set[K] {
            contains: K -> Bool
        }

        typeclass T: Twosome {
            has_two {
                exists(a: T, b: T) {
                    a != b
                }
            }
        }

        typeclass T: HasDefault {
            default_value: T
        }

        instance Color: Twosome
        instance Color: HasDefault {
            let default_value: Color = Color.red
        }

        attributes Set[T: Twosome] {
            define splits(self) -> Bool {
                exists(a: T, b: T) {
                    self.contains(a) and not self.contains(b)
                }
            }
        }

        attributes Set[T: HasDefault] {
            define contains_default(self) -> Bool {
                self.contains(HasDefault.default_value)
            }
        }

        let color_set: Set[Color] = axiom

        // Set[Color] should have both attributes since Color implements both typeclasses
        theorem test_splits {
            color_set.splits or not color_set.splits
        }

        theorem test_contains_default {
            color_set.contains_default or not color_set.contains_default
        }
        "#,
    );
}

#[test]
fn test_env_recursive_instance_function() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass I: Identity {
            id: I -> I
        }

        inductive Nat {
            zero
            suc(Nat)
        }

        instance Nat: Identity {
            define id(self) -> Nat {
                match self {
                    Nat.zero {
                        Nat.zero
                    }
                    Nat.suc(pred) {
                        id(pred).suc
                    }
                }
            }
        }
        "#,
    );
}

#[test]
fn test_env_proving_with_recursive_instance() {
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass I: Identity {
            id: I -> I
        }

        inductive Nat {
            zero
            suc(Nat)
        }

        instance Nat: Identity {
            define id(self) -> Nat {
                match self {
                    Nat.zero {
                        Nat.zero
                    }
                    Nat.suc(pred) {
                        id(pred).suc
                    }
                }
            }
        }

        theorem id_zero {
            Nat.zero.id = Nat.zero
        }

        theorem id_suc(n: Nat) {
            n.suc.id = n.id.suc
        }
        "#,
    );
}

#[test]
fn test_env_typeclass_digits_with_numerals() {
    // Typeclasses should be able to provide digits that work with the numerals keyword.
    // A "Zero" typeclass that provides a 0 digit should allow types implementing it
    // to use 0 as a numeral.
    let mut env = Environment::test();
    env.add(
        r#"
        typeclass Z: Zero {
            0: Z
        }

        inductive Nat {
            zero
            suc(Nat)
        }

        instance Nat: Zero {
            let 0: Nat = Nat.zero
        }

        attributes Nat {
            define read(self, other: Nat) -> Nat {
                // For this test we don't need a real implementation
                self
            }
        }

        numerals Nat

        // This should work - 0 should resolve to Nat.zero via the Zero typeclass
        theorem zero_is_zero {
            0 = Nat.zero
        }
        "#,
    );
}
