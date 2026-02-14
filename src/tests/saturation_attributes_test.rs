use super::common::*;
use crate::prover::Outcome;

// This file tests that the attributes feature works correctly in the prover.

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
fn test_proving_with_let_satisfy_attribute() {
    let text = r#"
    inductive One {
        one
    }
    attributes One {
        let witness: One satisfy {
            witness = One.one
        }
    }
    theorem goal {
        One.witness = One.one
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_function_satisfy_attribute() {
    let text = r#"
    inductive One {
        one
    }
    attributes One {
        let identity(a: Bool) -> b: Bool satisfy {
            b = a
        }
    }
    theorem goal(a: Bool) {
        One.identity(a) = a
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
fn test_proving_with_attribute_params() {
    let text = r#"
    structure BoolPair {
        first: Bool
        second: Bool
    }

    attributes BoolPair {
        define apply_first<T>(self, f: Bool -> T) -> T {
            f(self.first)
        }
    }

    theorem type_attr_syntax(b: BoolPair, f: Bool -> Bool) {
        BoolPair.apply_first(b, f) = f(b.first)
    }

    theorem obj_attr_syntax(b: BoolPair, f: Bool -> Bool) {
        b.apply_first(f) = f(b.first)
    }

    structure Pair<T, U> {
        first: T
        second: U
    }

    attributes Pair<T, U> {
        define map_first<V>(self, f: T -> V) -> V {
            f(self.first)
        }
    }

    theorem type_attr_generic<A, B, C>(p: Pair<A, B>, f: A -> C) {
        Pair.map_first(p, f) = f(p.first)
    }

    theorem obj_attr_generic<A, B, C>(p: Pair<A, B>, f: A -> C) {
        p.map_first(f) = f(p.first)
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_generic_attribute_match() {
    let text = r#"
    inductive Option<T> {
        none
        some(T)
    }

    attributes Option<T> {
        define map<U>(self, f: T -> U) -> Option<U> {
            match self {
                Option.none {
                    Option.none<U>
                }
                Option.some(t) {
                    Option.some(f(t))
                }
            }
        }
    }

    theorem goal<T, U>(t: T, f: T -> U) {
        Option.some(t).map(f) = Option.some(f(t))
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_generic_attribute_recursion() {
    let text = r#"
    inductive List<T> {
        nil
        cons(T, List<T>)
    }

    attributes List<T> {
        define map<U>(self, f: T -> U) -> List<U> {
            match self {
                List.nil {
                    List.nil<U>
                }
                List.cons(head, tail) {
                    List.cons(f(head), tail.map(f))
                }
            }
        }
    }

    theorem goal<T, U>(head: T, tail: List<T>, f: T -> U) {
        List.cons(head, tail).map(f) = List.cons(f(head), tail.map(f))
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_attributes_on_parameterized_types() {
    // Test that we can define attributes on specific instantiations of parameterized types
    let text = r#"
    inductive Color {
        red
        blue
    }

    inductive List<T> {
        nil
        cons(T, List<T>)
    }

    // Define an attribute specifically for List[Color]
    attributes List[Color] {
        define has_red(self) -> Bool {
            match self {
                List.nil {
                    false
                }
                List.cons(head, tail) {
                    if head = Color.red {
                        true
                    } else {
                        tail.has_red
                    }
                }
            }
        }
    }

    theorem red_list_has_red {
        List.cons(Color.red, List.nil<Color>).has_red
    }

    theorem blue_list_no_red {
        not List.cons(Color.blue, List.nil<Color>).has_red
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_typeclass_constrained_attributes() {
    // Test that we can define attributes with typeclass constraints (Foo[T: Bar] syntax)
    // and prove a simple theorem using them
    let text = r#"
    inductive Color {
        red
        blue
    }

    structure Set[K] {
        contains: K -> Bool
    }

    typeclass T: HasCompare {
        compare: (T, T) -> Bool
    }

    let color_compare: (Color, Color) -> Bool = axiom

    instance Color: HasCompare {
        let compare: (Color, Color) -> Bool = color_compare
    }

    // Define an attribute on Set[T: HasCompare]
    attributes Set[T: HasCompare] {
        define has_both(self, a: T, b: T) -> Bool {
            self.contains(a) and self.contains(b)
        }
    }

    // Just prove the definition expands correctly
    theorem has_both_def(s: Set[Color], a: Color, b: Color) {
        s.has_both(a, b) = (s.contains(a) and s.contains(b))
    } by {
        if s.has_both(a, b) {
            s.contains(a) and s.contains(b)
        }
        if s.contains(a) and s.contains(b) {
            s.has_both(a, b)
        }
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_with_complex_attributes() {
    // Test that we can define attributes with typeclass constraints (Foo[T: Bar] syntax)
    // and prove a simple theorem using them
    let text = r#"
    inductive Color {
        red
        blue
    }

    structure Set[K] {
        contains: K -> Bool
    }

    attributes Set[Color] {
        define has_red(self) -> Bool {
            exists(a: Color) {
                self.contains(Color.red)
            }
        }

        define has_non(self, c: Color) -> Bool {
            exists(a: Color) {
                self.contains(a) and a != c
            }
        }

        define red_splits(self) -> Bool {
            self.has_red and self.has_non(Color.red)
        }
    }

    define true_fn(c: Color) -> Bool {
        true
    }

    let universal = Set.new(true_fn)

    theorem goal {
        universal.red_splits
    } by {
        let b = Color.blue
        universal.contains(b) and b != Color.red
        universal.has_non(Color.red)
        universal.has_red
    }
    "#;
    verify_succeeds(text);
}
