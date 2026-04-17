# Search

## Verify Or Contraction

```acorn
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define some(x: Nat) -> Bool { f(x) or g(x) or h(x) }
        axiom somea { f(a) or g(a) or h(a) }
        theorem goal { some(a) }
        
```

## Verify Fimp Expansion

```acorn
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }
        axiom fimpa { fimp(a) }
        theorem thm { f(a) implies (g(a) and h(a)) }
        
```

## Verify Fimp Contraction

```acorn
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }
        axiom fimpa { f(a) implies (g(a) and h(a)) }
        theorem goal { fimp(a) }
        
```

## Verify Functional Existence

There are two tricky things about this resolution.
In one of the directions, you have to resolve x0(x1) against foo(a, b).
In the other direction, in the final literal-literal resolution, both sides
still have a free variable. So we don't find it via simplification.
Nevertheless, intuitively it is just one step.

```acorn
        type Nat: axiom
        let is_min: (Nat -> Bool, Nat) -> Bool = axiom
        let foo: Nat -> (Nat -> Bool) = axiom
        axiom has_min(f: Nat -> Bool, n: Nat) {
            f(n) implies exists(m: Nat) { is_min(f, m) }
        }
        axiom foo_is_true_somewhere(a: Nat) {
            exists(b: Nat) { foo(a, b) }
        }
        let min_foo(a: Nat) -> b: Nat satisfy {
            is_min(foo(a), b)
        }
        
```

## Prove With Imported Existential

```acorn
        type Nat: axiom

        let f: Nat -> Bool = axiom

        axiom exists_a_fa {
            exists(a: Nat) { f(a) }
        }

        theorem goal {
            exists(a: Nat) { f(a) }
        }
    
```

## Reopen Existential With Non Atomic Goal Term

This is a reduced repro of the `rat_base.ac` failure.

The `witness` axiom already has the existential we want. The failing step is
reopening that existential with the non-atomic term `g(Value.a)` on the left side
of the equality. If that term is first aliased to a local name, the proof succeeds.

```acorn
        inductive Value {
            a
            b
        }

        let p: Value -> Bool = axiom
        let h: (Value, Value) -> Value = axiom
        let g: Value -> Value = axiom

        axiom witness(m: Value) {
            exists(q: Value, r: Value) {
                p(r) and m = h(q, r)
            }
        }

        theorem goal {
            exists(q: Value, r: Value) {
                p(r) and g(Value.a) = h(q, r)
            }
        } by {
            let (q: Value, r: Value) satisfy {
                p(r) and g(Value.a) = h(q, r)
            }
        }
        
```

## Code Gen Not Losing Conclusion

Reproducing a bug found by Dan.
This confused the code generator because the final step of the proof
uses only a single source, so when you reverse it, it has no premise.
(It's using equality resolution to go from "x0 != constant" to a contradiction.)

```acorn
            type Foo: axiom
            let zero: Foo = axiom
            let three: Foo = axiom
            let mul: (Foo, Foo) -> Foo = axiom

            define threeven(n: Foo) -> Bool {
                exists(d: Foo) {
                    mul(three, d) = n
                }
            }

            axiom mul_zero_right(a: Foo, b: Foo) {
                b = zero implies mul(a, b) = zero
            }

            theorem goal {
                threeven(zero)
            }
            
```

## Proving Identity Is Surjective

To prove this, we need to instantiate the definitions of:
is_surjective[V, V]
identity[V]

```acorn
            define is_surjective[T, U](f: T -> U) -> Bool {
                forall(y: U) {
                    exists(x: T) {
                        f(x) = y
                    }
                }
            }

            define identity[T](x: T) -> T {
                x
            }

            theorem identity_is_surjective[V] {
                is_surjective(identity[V])
            }
        
```

## Nested Define Expansion

Regression test for https://github.com/acornprover/acorn/issues/42
When an inner define has a complex exists-forall body, expanding the
outer define must stay shallow so the prover finds the proof within
the shallow activation budget.

```acorn
        type Elem: axiom
        let s: Elem -> Bool = axiom
        let f: Elem -> Elem = axiom
        let close: (Elem, Elem, Elem) -> Bool = axiom
        let pos: Elem -> Bool = axiom

        define inner(x: Elem) -> Bool {
            s(x) and
            forall(eps: Elem) {
                pos(eps) implies exists(delta: Elem) {
                    pos(delta) and forall(x1: Elem) {
                        s(x1) and close(x1, x, delta) implies
                        close(f(x1), f(x), eps)
                    }
                }
            }
        }

        define outer(dummy: Elem) -> Bool {
            forall(x: Elem) {
                s(x) implies inner(x)
            }
        }

        theorem goal(x: Elem) {
            outer(x) and s(x) implies inner(x)
        }
        
```
