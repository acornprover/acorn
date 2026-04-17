# Elaboration Normalization

## Polymorphic Axiom Chain With Typeclass

Test that typeclass constraints still work when the prover has to instantiate
with an arbitrary type. This is similar to
`test_polymorphic_axiom_chain_needs_arbitrary_type`, but with typeclass constraints.

If the prover incorrectly uses a `Bool` placeholder for a typeclass-constrained type,
this case would fail because `Bool` does not satisfy the typeclass.

```acorn
        type Nat: axiom
        let zero: Nat = axiom

        typeclass N: Neg {
            neg: N -> N
        }

        let nat_neg: Nat -> Nat = axiom

        instance Nat: Neg {
            let neg: Nat -> Nat = nat_neg
        }

        let foo: Bool = axiom
        let baz: Bool = axiom

        define bar[T: Neg](x: T) -> Bool {
            axiom
        }

        axiom foo_imp_bar[T: Neg](x: T) {
            foo implies bar[T](x)
        }

        axiom bar_imp_baz[T: Neg](x: T) {
            bar[T](x) implies baz
        }

        theorem goal {
            foo implies baz
        }
        
```

## Polymorphic Generated Witness Type Var Ordering

Reproduces a bug where certificate replay disagreed about the type-parameter
ordering for a polymorphic generated witness.

Negating `all_contain[K, I](f, x)` produces a witness shape whose clauses keep
the type parameters in scope as pinned locals. Even when the function type uses
`I` before `K`, every normalized clause for that witness must preserve the
declaration order `[K, I]`, or the replayed claim no longer matches.

```acorn
        structure Container[T] {
            member: T -> Bool
        }

        // Mirrors and_family[K, I](f: I -> Set[K], x: K) -> Bool
        // Note: K comes first in type params but I comes first in function type
        define all_contain[K, I](f: I -> Container[K], x: K) -> Bool {
            forall(i: I) {
                f(i).member(x)
            }
        }

        type Nat: axiom
        type Item: axiom

        // This axiom forces proof search into the generated witness pattern
        // When negated: not all_contain[K,I](f,x) creates exists(i:I) { not f(i).member(x) }
        axiom all_contain_witness[K, I](f: I -> Container[K], x: K) {
            not all_contain[K, I](f, x) implies exists(i: I) { not f(i).member(x) }
        }

        let f: Nat -> Container[Item] = axiom
        let x: Item = axiom

        // For this theorem, prover must use the all_contain_witness axiom
        // This requires replaying the generated witness clauses with the same
        // pinned type-parameter order.
        theorem goal {
            not all_contain[Item, Nat](f, x) implies exists(n: Nat) { not f(n).member(x) }
        }
        
```
