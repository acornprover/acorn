use super::common::*;

// This file tests that normalization works correctly, by proving statements that require normalization to prove.

#[test]
fn test_proving_with_boxed_bool() {
    let text = r#"
    structure BoxedBool {
        value: Bool
    }

    define boxed_and(a: BoxedBool, b: BoxedBool) -> BoxedBool {
        BoxedBool.new(a.value and b.value)
    }

    theorem goal(b: BoxedBool) {
        not b.value implies not boxed_and(b, b).value
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_avoids_infinitely_nested_types() {
    let text = r#"
        structure Set[K] {
            contains: K -> Bool
        }

        structure Pair[K1, K2] {
            first: K1
            second: K2
        }

        define elem_in_product[K1,K2](a1: Set[K1], a2: Set[K2], p: Pair[K1,K2]) -> Bool {
            a1.contains(p.first) and a2.contains(p.second)
        }

        attributes Set[K1] {
            define mul[K2](self, a: Set[K2]) -> Set[Pair[K1,K2]] {
                Set[Pair[K1,K2]].new(elem_in_product(self, a))
            }
        }

        // This theorem could recurse into indefinitely nested types if not limited.
        theorem foo_5[K, L](a: Set[K], b1: Set[L], b2: Set[L]) {
            a.mul(b1).mul(b2) = a.mul(b1).mul(b2)
        }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_avoids_infinite_monomorphization_recursion() {
    // This is a regression test to ensure we don't crash when processing
    // nested generic attribute calls with multiple type parameters.
    // The theorem is not provable, but we should handle it gracefully.
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

    theorem foo_1<T, U>(items: List<T>, f: T -> U, g: U -> U, items_1: List<U>) {
        items.map(f).map(g) = items_1
    }
    "#;
    // This should not crash, even though the theorem is not provable
    verify_fails(text);
}

#[test]
fn test_proving_avoids_another_infinite_monomorphization_recursion() {
    let text = r#"
    structure Set[K] {
        contains: K -> Bool
    }

    define constant_false[K](x: K) -> Bool {
        false
    }

    attributes Set[K] {
        let empty_set = Set[K].new(constant_false[K])
    }

    structure Map[K, L] {
        in_space: Set[K]
        out_space: Set[L]
        fn: K -> L
    }

    attributes Map[K, L] {
        define is_surjective(self) -> Bool {
            forall(y: L) {
                self.out_space.contains(y) implies exists(x: K) {
                    self.in_space.contains(x) and self.fn(x) = y
                }
            }
        }
    }

    /// the set theory version of product_index
    define elem_in_product_index_map[I, K](m: Map[I, Set[K]], x: I -> K) -> Bool {
        forall(i: I) {
            m.in_space.contains(i) implies m.fn(i).contains(x(i))
        }
    }

    // We should be able to prove the goal, but this definition introduced new
    // types and causes an infinite recursion. (At the time the bug was reported.)
    define product_index_map[I, K](m: Map[I, Set[K]]) -> Set[I -> K] {
        Set[I -> K].new(elem_in_product_index_map(m))
    }

    attributes Set[K] {
        define superset(self, a: Set[K]) -> Set[K] {
            forall(x: K) {
                a.contains(x) implies self.contains(x)
            }
        }
    }

    define power_set[K](a: Set[K]) -> Set[Set[K]] {
        Set[Set[K]].new(a.superset)
    }

    type Nat: axiom
    let zero: Nat = axiom

    attributes Set[K] {
        define is_finite_set(self) -> Bool {
            if self = Set[K].empty_set {
                true
            } else {
                exists(num: Nat, m: Map[Nat, K]) {
                    m.out_space = self
                }
            }
        }
    }

    theorem goal[K] {
        exists(s: Set[K]) {
            s.is_finite_set
        }
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_function_as_argument() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom

    define foo(f: Thing -> Bool) -> Bool {
        true
    }

    theorem goal {
        foo(function(t: Thing) { t = u })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_function_equality() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom
    let f: (Thing -> Bool) -> Thing = axiom

    theorem goal {
        f(function(t: Thing) { t = u }) = f(function(t: Thing) { t = u })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_const_false() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom
    define not_apply_u(t: Thing -> Bool) -> Bool {
        not t(u)
    }

    theorem anon_const_false {
        not_apply_u(function(t: Thing) { false })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_const_true() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom
    define not_apply_u(t: Thing -> Bool) -> Bool {
        not t(u)
    }

    theorem anon_const_false {
        not not_apply_u(function(t: Thing) { true })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_more_anonymous_const_false() {
    let text = r#"
    structure Set[T] {
        contains: T -> Bool
    }

    attributes Set[K] {
        let ee = Set[K].new(function(x: K) { false })
    }

    theorem goal[K] {
        exists(d: Set[K]) {
            d = Set[K].ee
        }
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_long_if_condition() {
    let text = r#"
    type Nat: axiom
    let f: Nat -> Bool = axiom

    define or_switch(a: Nat, b: Nat, c: Nat, d: Nat) -> Nat {
        if f(a) or f(b) {
            c
        } else {
            d
        }
    }

    theorem goal(a: Nat) {
        or_switch(a, a, a, a) = a
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_nested_lambdas() {
    let text = r#"
    type Nat: axiom
    type ListNat: axiom
    let range: Nat -> ListNat = axiom
    let sum: ListNat -> Nat = axiom
    let map: (ListNat, Nat -> Nat) -> ListNat = axiom

    define double_sum_1(n: Nat, m: Nat, f: (Nat, Nat) -> Nat) -> Nat {
        sum(map(range(n), function(i: Nat) {
            sum(map(range(m), function(j: Nat) { f(i, j) }))
        }))
    }

    define double_sum_2(n: Nat, m: Nat, f: (Nat, Nat) -> Nat) -> Nat {
        sum(map(range(n), function(i: Nat) {
            sum(map(range(m), function(j: Nat) { f(i, j) }))
        }))
    }

    theorem goal(a: Nat, b: Nat, f: (Nat, Nat) -> Nat) {
        double_sum_1(a, b, f) = double_sum_2(a, b, f)
    }
    "#;
    verify_succeeds(text);
}

// The prover should be able to do this without the proof body.
#[test]
fn test_proof_with_unifying_closures() {
    let text = r#"
    type Nat: axiom
    let foo: (Nat -> Nat) -> Bool = axiom
    let bar: (Nat, Nat) -> Nat = axiom

    axiom ax(a: Nat) {
        foo(function(b: Nat) {
            bar(b, a)
        })
    }

    theorem goal(a: Nat) {
        foo(function(b: Nat) {
            bar(b, a)
        })
    } by {
        ax(a)
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_nested_ifs() {
    let text = r#"
    type Nat: axiom
    let f: Nat -> Bool = axiom

    define foo(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat) -> Nat {
        if f(a) {
            b
        } else {
            if f(c) {
                d
            } else {
                e
            }
        }
    }

    theorem goal(a: Nat) {
        foo(a, a, a, a, a) = a
    } by {
        if f(a) {
            foo(a, a, a, a, a) = a
        } else {
            foo(a, a, a, a, a) = a
        }
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_conjunction_goal() {
    let text = r#"
    type Color: axiom
    let a: Color = axiom
    let b: Color = axiom
    let c: Color = axiom
    let d: Color = axiom
    let e: Color = axiom

    let f: (Color, Color) -> Bool = axiom

    axiom a1(x: Color) {
        f(a, x) implies f(b, x)
    }

    axiom a2(x: Color) {
        f(a, x) implies f(c, x)
    }

    axiom a3(x: Color) {
        f(a, x) implies f(d, x)
    }

    theorem goal {
        f(a, e) implies (f(b, e) and f(c, e) and f(d, e))
    }
    "#;
    verify_succeeds(text);
}

// This currently fails due to lack of step completeness.
// Unfortunately we normalize this in such a way that it is not obvious.
// The normalized task is to derive a contradiction from:
//
// axiom:
//   (a or c) and (b or c) and (a or d) and (b or d)
//
// negated goal:
//   (not a or not b) and (not c or not d)
//
// It seems like some sort of monotonic-complexity-reducing reasoning might do it.
//
#[test]
#[ignore = "known normalization/prover gap: axiom and identical theorem normalize into a hard search shape"]
fn test_complex_boolean() {
    let text = r#"
    let a: Bool = axiom
    let b: Bool = axiom
    let c: Bool = axiom
    let d: Bool = axiom

    axiom ax {
        (a and b) or (c and d)
    }

    theorem goal {
        (a and b) or (c and d)
    }
    "#;
    verify_succeeds(text);
}

// Similar lack-of-step-completeness issue, but with an existential witness.
// Intuitively this should be immediate from the axiom, but after normalization
// and negation we may get clause sets that don't line up in an obvious way for
// the current prover search strategy.
//
#[test]
#[ignore = "known normalization/prover gap with existential disjunction shape"]
fn test_exists_disjunction_same_as_axiom() {
    let text = r#"
    type Nat: axiom
    let f: Nat -> Bool = axiom
    let g: Nat -> Bool = axiom
    let h: Nat -> Bool = axiom
    let i: Nat -> Bool = axiom

    axiom ax {
        exists(x: Nat) {
            (f(x) and g(x)) or (h(x) and i(x))
        }
    }

    theorem goal {
        exists(x: Nat) {
            (f(x) and g(x)) or (h(x) and i(x))
        }
    }
    "#;
    verify_succeeds(text);
}

// This test exercises bugs where structures with methods containing
// nested lambdas with if-then-else expressions would crash during normalization.
// The issues were:
// 1. Lambda bodies containing IfThenElse weren't being converted to Terms properly
//    (the Lambda case called .to_term() but IfThenElse returns ExtendedTerm::If)
// 2. Type parameters were incorrectly being collected as value arguments for
//    synthesized atoms representing if-expressions
#[test]
fn test_lambda_with_if_then_else() {
    // Test that definitions with if-then-else inside lambdas are processed correctly.
    let text = r#"
    type Nat: axiom
    let zero: Nat = axiom
    let suc: Nat -> Nat = axiom

    structure Counter {
        count: Bool -> Nat
    }

    define increment(counter: Counter, item: Bool) -> Counter {
        Counter.new(function(x: Bool) {
            if x = item {
                suc(counter.count(x))
            } else {
                counter.count(x)
            }
        })
    }

    let c: Counter = axiom

    // Verify the increment function can be used
    theorem goal {
        increment(c, true) = increment(c, true)
    }
    "#;
    verify_succeeds(text);
}

// Test that compose with higher-order functions generates checkable certificates.
// This test catches a bug where in polymorphic mode, the certificate generator
// incorrectly handles curried function application after compose.
// The bug manifests as compose(f, g)(x) being treated as compose(f, g, x) with wrong arity.
#[test]
fn test_compose_with_higher_order_result() {
    let text = r#"
    type Nat: axiom
    let one: Nat = axiom

    // mul is curried: mul(a) returns a function that multiplies by a
    let mul: Nat -> (Nat -> Nat) = axiom

    // from_nat: Nat -> Nat
    let from_nat: Nat -> Nat = axiom

    // compose[T, U, V](f: U -> V, g: T -> U) returns function(x: T) { f(g(x)) }
    define compose[T, U, V](f: U -> V, g: T -> U) -> T -> V {
        function(x: T) {
            f(g(x))
        }
    }

    // compose(mul, from_nat) has type Nat -> (Nat -> Nat)
    // Applying it to `one` gives mul(from_nat(one)) : Nat -> Nat
    theorem goal {
        compose[Nat, Nat, Nat -> Nat](mul, from_nat)(one) = mul(from_nat(one))
    }
    "#;
    verify_succeeds(text);
}
