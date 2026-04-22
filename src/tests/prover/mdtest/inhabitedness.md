# Inhabitedness

## Can Inhabit Arbitrary Type Of Typeclass

This should be accepted, since any arbitrary P: Pointed is inhabited.

```acorn
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed]: P satisfy {
        true
    }
    
```

## Can Inhabit Arbitrary Type Of Extended Typeclass

This should be accepted, since any arbitrary P: Pointed is inhabited.

```acorn
    typeclass P: Pointed {
        point: P
    }

    typeclass Q: Qux extends Pointed {
        foo: Q -> Bool
    }

    let inhabitant[Q: Qux]: Q satisfy {
        true
    }
    
```

## Can Inhabit Function Type When Codomain Inhabited

```acorn
    typeclass P: Pointed {
        point: P
    }

    let inhabitant[P: Pointed, Q]: Q -> P satisfy {
        true
    }
    
```

## Can Inhabit Identity Function Type

```acorn
    let inhabitant[T]: T -> T satisfy {
        true
    }
    
```

## Can Inhabit List Type

```acorn
    inductive List[T] {
        cons(List[T])
        nil
    }
    let inhabitant[T]: List[T] satisfy {
        true
    }
    
```

## Inhabited Const

```acorn
    let inhabited[T]: Bool = exists(x: T) {
        true
    }
    
```

## Passive Contradiction Cert Replays Outer Function Capture

```acorn
        inductive Foo {
            c0
        }

        theorem goal(h: Foo -> Bool) {
            (forall(x: Foo) { h(x) }) implies exists(y: Foo) { h(y) }
        }
        
```

## Polymorphic Structure With Function If Then Else

Regression test for a bug where polymorphic structures containing functions with
if-then-else expressions returning non-Bool types would cause a type mismatch
during clause validation. The issue was with how normalization tracked the local
type-parameter slots inside function definitions in `define` statements.

```acorn
    inductive Nat {
        zero
        suc(Nat)
    }

    structure Wrapper[T] {
        func: T -> Nat
    }

    attributes Wrapper[T] {
        define modify(self, item: T) -> Wrapper[T] {
            Wrapper.new(function(x: T) {
                if x = item {
                    self.func(x).suc
                } else {
                    self.func(x)
                }
            })
        }
    }

    theorem goal[T](w: Wrapper[T], item: T) {
        w.modify(item) = w.modify(item)
    }
    
```

## Polymorphic Axiom Chain Needs Arbitrary Type

Reproduces a bug where the prover needs to instantiate a polymorphic axiom
with an arbitrary type, resulting in certificate code like "let w2: x0 satisfy { true }"
which is invalid because x0 is not a valid type name.

```acorn
    let foo: Bool = axiom
    let baz: Bool = axiom

    define bar[T](x: T) -> Bool {
        axiom
    }

    axiom foo_imp_bar[T](x: T) {
        foo implies bar[T](x)
    }

    axiom bar_imp_baz[T](x: T) {
        bar[T](x) implies baz
    }

    theorem goal {
        foo implies baz
    }
    
```

## Subgroup Identity Existence Cert Generation

Regression: certificates generated while proving a polymorphic structure
constructor definition must check with the goal's type parameters in scope.

```acorn
        inductive Option[T] {
            none
            some(T)
        }

        typeclass G: Group {
            1: G
        }

        define subgroup_constraint[G: Group](contains: G -> Bool) -> Bool {
            contains(G.1)
        }

        define is_identity[G: Group](g: G) -> Bool {
            g = G.1
        }

        theorem identity_subgroup_constraint[G: Group] {
            subgroup_constraint(is_identity[G])
        }

        structure Subgroup[G: Group] {
            contains: G -> Bool
        } constraint {
            subgroup_constraint(contains)
        }

        let identity_subgroup[G: Group]: Subgroup[G] satisfy {
            Subgroup.new(is_identity[G]) = Option.some(identity_subgroup)
        }
        
```
