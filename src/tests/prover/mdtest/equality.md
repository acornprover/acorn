# Equality

## Proving Functional Structure Identity

```acorn
        type Foo: axiom

        structure Bar {
            value: Foo -> Foo
        }

        let a: Bar = axiom
        let b: Bar = axiom

        axiom rule1 {
            a.value = b.value
        }

        theorem goal {
            a = b
        }
        
```

## Extensionality Without Witness For Uninhabited Type

Test that extensionality works without requiring a witness for an uninhabited type.

This test uses a structure wrapper so that the proof must use extensionality.
The axiom `a.value = b.value` normalizes to `a.value(x) = b.value(x)`.
The goal `a = b` requires:
1. Using extensionality to derive `a.value = b.value` from `a.value(x) = b.value(x)`
2. Using the structure identity axiom to conclude `a = b`

`Elem` is uninhabited, so the prover cannot instantiate `x` with a concrete value.
Extensionality has to work on the universally quantified clause directly.

```acorn
        // Elem is uninhabited - it's an axiom type with no constructors
        type Elem: axiom

        // A wrapper structure containing a function over Elem
        structure Wrapper {
            value: Elem -> Elem
        }

        let a: Wrapper = axiom
        let b: Wrapper = axiom

        // Axiom that a.value = b.value (normalizes to a.value(x) = b.value(x))
        axiom values_equal {
            a.value = b.value
        }

        // Goal: prove a = b (requires extensionality to derive a.value = b.value first)
        theorem goal {
            a = b
        }
        
```

## Verify Reflexivity

```acorn
        define is_reflexive[T](f: (T, T) -> Bool) -> Bool {
            forall(t: T) {
                f(t, t)
            }
        }
            
        define lte_from[T](lt: (T, T) -> Bool, x: T, y: T) -> Bool {
            lt(x, y) or x = y    
        }
            
        theorem lte_is_reflexive[T](lt: (T, T) -> Bool) {
            is_reflexive(lte_from(lt))
        } by {
            forall(x: T) {
                x = x
                lte_from(lt)(x, x)
            }
        }
        
```

## Rewrite With Variable Renumbering

This reproduces a certificate-generation bug in rewrite handling.

The pattern axiom `g(x, y) = g(y, x)` has two variables, but the rewritten literal
only keeps one of them. Normalization renumbers the surviving variable, so replay
has to preserve the pre-normalization variable context rather than mixing it with
post-normalization numbering.

```acorn
        type Thing: axiom
        let t: Thing = axiom
        let t2: Thing = axiom
        let f: Thing -> Bool = axiom
        let g: (Thing, Thing) -> Thing = axiom
        let h: Thing -> Thing = axiom

        axiom g_sym(x: Thing, y: Thing) { g(x, y) = g(y, x) }
        axiom h_of_g_t { h(g(t, t2)) = t }
        theorem goal { h(g(t2, t)) = t }
        
```

## Boolean Equality From Mutual Implication

This reproduces the current `unique_preserves_contains` shape from `list_base.ac`.
The prover can separately prove `A implies B` and `B implies A`, but it does not
close the bare Boolean equality goal `A = B` when `A` and `B` are applied terms.

It would be nice to have this eventually.

```text
        type Foo: axiom

        let a: Foo -> Bool = axiom
        let b: Foo -> Bool = axiom

        axiom a_imp_b(x: Foo) {
            a(x) implies b(x)
        }

        axiom b_imp_a(x: Foo) {
            b(x) implies a(x)
        }

        theorem prove_a_imp_b(x: Foo) {
            a(x) implies b(x)
        }

        theorem prove_b_imp_a(x: Foo) {
            b(x) implies a(x)
        }

        theorem prove_eq(x: Foo) {
            a(x) = b(x)
        }

```
