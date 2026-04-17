# Basics

## Extracting Narrow Proof

```acorn
            let b: Bool = axiom
            let f1: Bool -> Bool = axiom
            let f2: Bool -> Bool = axiom
            let f3: Bool -> Bool = axiom
            let f4: Bool -> Bool = axiom
            axiom a1 { f1(b) }
            axiom a12(x: Bool) { f1(x) implies f2(x) }
            axiom a23(x: Bool) { f2(x) implies f3(x) }
            axiom a34(x: Bool) { f3(x) implies f4(x) }
            theorem goal(x: Bool) { f4(b) }
        
```

## Rewriting Confluence Indirectly

The facts given by "axiom recursion_base" and "define add" are
each rewrite rules.
To prove add_zero_right, the naive way applies one backward and one
forward rewrite.
We need to be able to handle this somehow.

```acorn
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }
            axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }
            define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }
            theorem add_zero_right(a: Nat) { add(a, zero) = a }
        
```

## Proving Explicit False Okay

```acorn
            let b: Bool = axiom
            if b != b {
                false
            }
        
```

## Subsequent Explicit False Ok

```acorn
            let b: Bool = axiom
            if b != b {
                b or not b
                false
            }
        
```

## Claim Before Explicit False With Inconsistent Assumptions

Reproduces a bug where a claim BEFORE an explicit `false` fails with Inconsistent.
The issue: when processing the claim, `includes_explicit_false` hasn't been set yet
because `false` hasn't been processed. But the prover finds a contradiction from
the hypothetical facts alone, which should be valid (it proves the claim vacuously).
The key structure:
1. Assume something that leads to inconsistency (a = b and a != b)
2. Make a claim that can be proven from the inconsistency
3. Have explicit `false` at the end

```acorn
            let a: Bool = axiom
            let b: Bool = axiom
            axiom a_eq_b { a = b }
            if a != b {
                // This claim should succeed - the assumptions are inconsistent,
                // so any claim is vacuously true. The prover will find the inconsistency
                // when trying to prove "a = b implies a = a", but since `false` comes
                // later, this should be allowed.
                a = b implies a = a
                false
            }
        
```

## Verify If Else Function

```acorn
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            define sign(a: Nat) -> Nat {
                if a = zero {
                    zero
                } else {
                    one
                }
            }
            theorem goal(a: Nat) {
                sign(a) = zero or sign(a) = one
            }
        
```

## Verify Complicated Theorem Application

```acorn
            type Nat: axiom
            let a: Nat = axiom
            let b: Nat = axiom
            let c: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom trans(x: Nat, y: Nat, z: Nat) {
                f(x, y) and f(y, z) implies f(x, z)
            }
            axiom fab { f(a, b) }
            axiom fbc { f(b, c) }
            theorem goal {
                f(a, c)
            }
            
```

## Verify Existence Theorem

```acorn
            type Nat: axiom
            let a: Nat = axiom
            let f: Nat -> Bool = axiom
            let g: (Nat, Nat) -> Bool = axiom
            axiom foo(x: Nat) {
                f(x) implies exists(y: Nat) { g(x, y) and g(y, x) }
            }
            theorem goal {
                f(a) implies exists(y: Nat) { g(a, y) and g(y, a) }
            }
            
```

## Finding Implied Exists

```acorn
            type Foo: axiom
            let b: Foo = axiom
            let foo: Foo -> Bool = axiom
            let bar: (Foo, Foo) -> Bool = axiom
            let qux: Foo -> Foo = axiom

            axiom foo_implies_exists(a: Foo) {
                foo(a) implies exists(i: Foo, j: Foo) {
                    bar(i, j) and bar(j, a) and qux(i) = qux(j)
                }
            }

            axiom foo_b {
                foo(b)
            }

            theorem goal {
                exists (i: Foo, j: Foo) {
                    bar(i, j) and bar(j, b) and qux(i) = qux(j)
                }
            }
            
```

## Rewrite Consistency

In practice this caught an inconsistency that came from bad rewrite logic.

```acorn
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            let mulx: (Nat, Nat) -> Nat = axiom
            axiom add_suc(a: Nat, b: Nat) { addx(suc(a), b) = suc(addx(a, b)) }
            axiom suc_ne(a: Nat) { suc(a) != a }
            axiom mul_suc(a: Nat, b: Nat) { addx(a, mulx(a, b)) = mulx(a, suc(b)) }
            theorem goal(a: Nat) { suc(a) != a }
        
```

## Basic Lambda Normalization

We can normalize lambdas inside function calls by synthesizing terms for them.

```acorn
            type Nat: axiom
            let zero: Nat = axiom
            define apply(f: Nat -> Nat, a: Nat) -> Nat { f(a) }
            theorem goal { apply(function(x: Nat) { x }, zero) = zero }
        
```

## Functional Equality Definition

```acorn
            type Nat: axiom
            let f: Nat -> Nat = axiom
            let g: Nat -> Nat = axiom
            theorem goal { forall(x: Nat) { f(x) = g(x) } implies f = g }
        
```

## Verify Functional Definition

```acorn
            type Nat: axiom
            define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
            define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
            let p: Nat = axiom
            let f: Nat -> Bool = is_min(gcd_term(p))

            theorem goal { is_min(gcd_term(p)) = f }
        
```

## Functional Substitution

```acorn
            type Nat: axiom
            define find(f: Nat -> Bool) -> Nat { axiom }
            define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
            define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
            let p: Nat = axiom
            let f: Nat -> Bool = is_min(gcd_term(p))
            theorem goal { find(is_min(gcd_term(p))) = find(f) }
        
```

## Proving With Partial Application

```acorn
            type Nat: axiom
            let zero: Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem goal(f: Nat -> Nat) { f = addx(zero) implies f(zero) = addx(zero, zero) }
        
```

## Backward Nonbranching Reasoning

```acorn
            type Nat: axiom
            let suc: Nat -> Nat = axiom
            axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }
            let n: Nat = axiom
            axiom hyp { suc(n) != n }
            theorem goal { suc(suc(n)) != suc(n) }
        
```

## Basic Unification

```acorn
            type Nat: axiom
            let zero: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom f_zero_right(x: Nat) { f(x, zero) }
            theorem goal { exists(x: Nat) { f(zero, x) } }
        
```

## Indirect Proof Collapses

```acorn
            let a: Bool = axiom
            let b: Bool = axiom
            axiom bimpa { b implies a }
            axiom bimpna { b implies not a }
            theorem goal { not b }
        
```
