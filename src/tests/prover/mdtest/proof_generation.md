# Proof Generation

## Proof Generation With Forall Goal

Proof generation and condensed-certificate regressions.

```acorn
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg { forall(x: Nat) { f(x) implies g(x) } }
            axiom gimph { forall(x: Nat) { g(x) implies h(x) } }
            theorem goal { forall(x: Nat) { f(x) implies h(x) } }
        
```

## Proof Generation With Intermediate Existential

```acorn
        type Nat: axiom
        let b: Bool = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom forg(x: Nat) { f(x) or g(x) }
        axiom fgimpb { forall(x: Nat) { f(x) or g(x) } implies b }
        theorem goal { b }
        
```

## Replay Of A Let Satisfy Cert Line

```acorn
        type Thing: axiom
        type Nat: axiom
        let zero: Nat = axiom
        let p: Nat -> Bool = axiom
        let q: (Thing, Nat) -> Bool = axiom

        axiom pos_implies_nonzero(n: Nat) {
            p(n) implies n != zero
        }

        axiom exists_helper(t: Thing) {
            exists(n: Nat) {
                p(n) and q(t, n)
            }
        }

        theorem goal(t: Thing) {
            exists(n: Nat) {
                n != zero and q(t, n)
            }
        } by {
            let (n: Nat) satisfy {
                p(n) and q(t, n)
            }
            n != zero
        }
    
```

## Replay Of Generic Partial Application Cert Line

```acorn
inductive Point {
    point
}

define constant[T, U](u: U, t: T) -> U {
    u
}

define apply_fn[T, U](f: T -> U, x: T) -> U {
    f(x)
}

theorem partial_constant_replay(a: Point, x: Point) {
    apply_fn(constant[Point, Point](a), x) = a
}
```

## Eval Handcrafted Nested Pointwise Function Argument Cert

The handcrafted eval policy can find a proof that unfolds a pointwise function
whose second argument is itself a pointwise function. Certificate generation must
serialize the function-valued argument, not its application at the current point.

```acorn eval-handcrafted
type Nat: axiom

let mul: (Nat, Nat) -> Nat = axiom

axiom mul_assoc(a: Nat, b: Nat, c: Nat) {
    mul(mul(a, b), c) = mul(a, mul(b, c))
}

axiom mul_comm(a: Nat, b: Nat) {
    mul(a, b) = mul(b, a)
}

define pointwise_mul(f: Nat -> Nat, g: Nat -> Nat) -> (Nat -> Nat) {
    function(n: Nat) { mul(f(n), g(n)) }
}

theorem mul_swap_middle(a: Nat, b: Nat, c: Nat, d: Nat) {
    mul(mul(a, b), mul(c, d)) = mul(mul(a, c), mul(b, d))
} by {
    mul(mul(a, b), mul(c, d)) = mul(a, mul(b, mul(c, d)))
    mul(b, mul(c, d)) = mul(mul(b, c), d)
    mul(b, c) = mul(c, b)
    mul(mul(b, c), d) = mul(mul(c, b), d)
    mul(mul(c, b), d) = mul(c, mul(b, d))
    mul(b, mul(c, d)) = mul(c, mul(b, d))
    mul(a, mul(b, mul(c, d))) = mul(a, mul(c, mul(b, d)))
    mul(a, mul(c, mul(b, d))) = mul(mul(a, c), mul(b, d))
}

theorem pointwise_mul_product(
    f: Nat -> Nat, g: Nat -> Nat, a: Nat, b: Nat
) {
    pointwise_mul(f, g)(mul(a, b)) = mul(f(mul(a, b)), g(mul(a, b)))
}

theorem pointwise_mul_preserves_product(
    f: Nat -> Nat, g: Nat -> Nat, a: Nat, b: Nat
) {
    f(mul(a, b)) = mul(f(a), f(b)) and
    g(mul(a, b)) = mul(g(a), g(b))
        implies pointwise_mul(f, g)(mul(a, b)) =
            mul(pointwise_mul(f, g)(a), pointwise_mul(f, g)(b))
} by {
    if f(mul(a, b)) = mul(f(a), f(b)) and
        g(mul(a, b)) = mul(g(a), g(b)) {
        pointwise_mul(f, g)(mul(a, b)) = mul(f(mul(a, b)), g(mul(a, b)))
        pointwise_mul(f, g)(a) = mul(f(a), g(a))
        pointwise_mul(f, g)(b) = mul(f(b), g(b))
        mul(f(mul(a, b)), g(mul(a, b))) =
            mul(mul(f(a), f(b)), mul(g(a), g(b)))
        mul_swap_middle(f(a), f(b), g(a), g(b))
        mul(mul(f(a), f(b)), mul(g(a), g(b))) =
            mul(mul(f(a), g(a)), mul(f(b), g(b)))
        pointwise_mul(f, g)(mul(a, b)) =
            mul(pointwise_mul(f, g)(a), pointwise_mul(f, g)(b))
    }
}
```

## Closed Generic Typeclass Attribute Rewrite Cert Line

This is a red regression test for certificate serialization of a closed generic
claim used as a rewrite under a typeclass attribute relation. Proof search finds
the proof, but current certificate generation fails while trying to infer an
in-scope type argument for the closed generic claim.

```acorn
typeclass A: Add {
    add: (A, A) -> A
}

typeclass A: Zero {
    0: A
}

typeclass A: AddMonoid extends Add, Zero {
    add_identity_right(x: A) {
        x + A.0 = x
    }
}

typeclass A: HasLe {
    le: (A, A) -> Bool
}

attributes A: HasLe {
    define lt(self, other: A) -> Bool {
        A.le(self, other) and self != other
    }
}

structure Foo {
    value: Bool
}

instance Foo: Add {
    let add: (Foo, Foo) -> Foo = function(x: Foo, y: Foo) {
        x
    }
}

instance Foo: Zero {
    let 0: Foo = Foo.new(true)
}

instance Foo: AddMonoid

instance Foo: HasLe {
    let le: (Foo, Foo) -> Bool = function(x: Foo, y: Foo) {
        true
    }
}

let one: Foo = Foo.new(true)

define suc(x: Foo) -> Foo {
    one + x
}

theorem typeclass_attribute_rewrite_cert(m: Foo) {
    m < one implies m < suc(Foo.0)
}
```

## Assuming Lhs Of Implication

```acorn
            let a: Bool = axiom
            let b: Bool = axiom
            let c: Bool = axiom
            axiom aimpb { a implies b }
            axiom bimpc { b implies c }
            theorem goal { a implies c } by {
                b
            }
        
```

## Templated Proof

```acorn
            type Thing: axiom
            let t1: Thing = axiom
            let t2: Thing = axiom
            let t3: Thing = axiom

            define foo[T](x: T) -> Bool { axiom }

            axiom a12 { foo(t1) implies foo(t2) }
            axiom a23 { foo(t2) implies foo(t3) }
            theorem goal { foo(t1) implies foo(t3) }
            
```

## Proof Condensing Induction

```acorn
        type Nat: axiom
        let zero: Nat = axiom
        let suc: Nat -> Nat = axiom
        axiom induction(f: Nat -> Bool) {
            f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) }
        }
        let foo: Nat -> Bool = axiom
        theorem goal { foo(zero) and forall(k: Nat) { foo(k) implies foo(suc(k)) } implies forall(n: Nat) { foo(n) } }
        
```

## Proof Condensing False

```acorn
        let a: Bool = axiom
        axiom a_true { a }
        if not a {
            false
        }
        
```

## Proof Condensing Combining Two Theorems

```acorn
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom fimpg(x: Nat) { f(x) implies g(x) }
        axiom fa { f(a) }
        theorem goal { g(a) }
        
```

## Proof Indirect From Goal

```acorn
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg(x: Nat) { f(x) implies g(x) }
            axiom gimph(x: Nat) { g(x) implies h(x) }
            axiom fimpnh(x: Nat) { f(x) implies not h(x) }
            theorem goal(x: Nat) { not f(x) }
        
```

## Definition Equation With Forall Body Alpha Rename

Regression test for [acornlib PR #603](https://github.com/acornprover/acornlib/pull/603).
When the body of a `define` is a `forall`, an in-proof equation
`f(args) = forall(...) { ... }` should produce a cert that re-verifies
even though the kernel may alpha-rename the bound variables in the
generated certificate line.

```acorn
type Nat: axiom
type Real: axiom
let lt: (Real, Real) -> Bool = axiom
let lte: (Nat, Nat) -> Bool = axiom
let real_dist: (Real, Real) -> Real = axiom

typeclass M: Metric {
    distance: (M, M) -> Real
}

instance Real: Metric {
    let distance: (Real, Real) -> Real = real_dist
}

define cauchy_bound[M: Metric](q: Nat -> M, n: Nat, eps: Real) -> Bool {
    forall(i: Nat, j: Nat) {
        lte(n, i) and lte(n, j) implies lt(q(i).distance(q(j)), eps)
    }
}

theorem goal(q: Nat -> Real, n: Nat, eps: Real) {
    cauchy_bound(q, n, eps) implies forall(i: Nat, j: Nat) {
        lte(n, i) and lte(n, j) implies lt(real_dist(q(i), q(j)), eps)
    }
} by {
    cauchy_bound(q, n, eps) = forall(i: Nat, j: Nat) {
        lte(n, i) and lte(n, j) implies lt(q(i).distance(q(j)), eps)
    }
}
```
