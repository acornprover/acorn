use crate::prover::Outcome;
use crate::tests::support::*;

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
    assert_eq!(prove_text(text, "antigoal"), Outcome::ShallowExhausted);
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

    theorem goal(tail: List[Bool]) {
        tail.contains(true) implies List.cons(false, tail).contains(true)
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
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

    theorem goal {
        List.nil[Bool].remove_all(true) = List.nil[Bool]
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
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
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}

#[test]
fn test_proving_with_attributes_on_parameterized_types() {
    // Test that a specific instantiation of a parameterized type can recurse through an attribute.
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

    theorem goal {
        List.cons(Color.blue, List.cons(Color.red, List.nil<Color>)).has_red
    }
    "#;
    assert_eq!(prove_text(text, "goal"), Outcome::Success);
}
