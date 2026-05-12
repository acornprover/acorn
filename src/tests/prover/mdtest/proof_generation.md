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
