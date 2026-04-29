# Typeclasses

## Prover Handles Instance Let

Prover coverage for instances, typeclasses, and related language features.

```acorn
    inductive Z1 {
        zero
    }

    typeclass T: TwoColored {
        is_red: T -> Bool
    }

    instance Z1: TwoColored {
        let is_red: Z1 -> Bool = function(z: Z1) {
            true
        }
    }

    theorem goal {
        TwoColored.is_red(Z1.zero)
    }
    
```

## Prover Handles Instance Define

```acorn
    inductive Z1 {
        zero
    }

    typeclass T: TwoColored {
        is_red: T -> Bool
    }

    instance Z1: TwoColored {
        define is_red(self) -> Bool {
            true
        }
    }

    theorem goal {
        TwoColored.is_red(Z1.zero)
    }
    
```

## Prover Handles Parameterized Constants

```acorn
    inductive Z1 {
        zero
    }

    typeclass S: Singleton {
        value: S

        unique(x: S) {
            x = S.value
        }
    }

    instance Z1: Singleton {
        let value: Z1 = Z1.zero
    }

    theorem goal {
        Z1.zero = Singleton.value[Z1]
    }
    
```

## Prover Succeeds On Good Instance

```acorn
    inductive Z1 {
        zero
    }

    typeclass S: Singleton {
        value: S

        unique(x: S) {
            x = S.value
        }
    }

    instance Z1: Singleton {
        let value: Z1 = Z1.zero
    }
    
```

## Prover Can Use Typeclass Theorems

These axioms should be combinable via the instance relationship.

```acorn
    typeclass F: Foo {
        foo: F -> Bool
    }

    axiom always_foo[F: Foo](x: F) {
        x.foo
    }

    inductive Bar {
        bar
    }

    let qux: Bool = axiom

    instance Bar: Foo {
        define foo(self) -> Bool {
            qux
        }
    }

    theorem goal {
        qux
    } by {
        Foo.foo(Bar.bar)
    }
    
```

## Polymorphic Goal With Polymorphic Axiom No Typeclass

Simpler test: polymorphic goal using polymorphic axiom (no typeclass)

```acorn
    define foo[T](x: T) -> Bool {
        axiom
    }

    axiom always_foo[T](x: T) {
        foo(x)
    }

    theorem goal[T](a: T) {
        foo(a)
    }
    
```

## Polymorphic Goal With External Axiom

Simpler test: polymorphic goal using polymorphic axiom (with typeclass)

```acorn
    typeclass F: Foo {
        foo: F -> Bool
    }

    axiom always_foo[F: Foo](x: F) {
        x.foo
    }

    theorem goal[G: Foo](a: G) {
        a.foo
    }
    
```

## Prover Handling Typeclasses

```acorn
    typeclass F: FooTrue {
        foo: F -> Bool
        bar: F -> Bool

        foo_true(a: F) {
            a.foo
        }

        foo_imp_bar(a: F) {
            a.foo implies a.bar
        }
    }

    theorem bar_true[G: FooTrue](a: G) {
        a.bar
    }
    
```

## Use Typeclass Axiom On Instance

```acorn
    typeclass F: FooTrue {
        b: Bool
    }

    define foo[T](t: T) -> Bool {
        axiom
    }

    axiom foo_true[F: FooTrue](a: F) {
        foo(a)
    }

    inductive Z1 {
        zero
    }

    instance Z1: FooTrue {
        let b: Bool = true
    }

    theorem goal(z: Z1) {
        foo(z)
    }
    
```

## Proving With Parameterized Constant

```acorn
    typeclass P: PointedSet {
        point: P
    }

    let get_point1[P: PointedSet]: P = P.point
    let get_point2[P: PointedSet]: P = P.point

    theorem goal[P: PointedSet] {
        get_point1[P] = get_point2[P]
    }
    
```

## Proving With Const False

```acorn
    define const_false[T](x: T) -> Bool {
        false
    }
    theorem goal[T](x: T) {
        not const_false(x)
    }
    
```

## Proving With Typeclass Attribute Assigned As Generic

This requires instantiating type parameters to match equals[Color].

```acorn
    typeclass F: Foo {
        op: (F, F) -> Bool

        self_true(x: F) {
            x.op(x)
        }
    }

    define equals[T](x: T, y: T) -> Bool {
        x = y
    }

    inductive Color {
        red
        blue
    }

    instance Color: Foo {
        let op: (Color, Color) -> Bool = equals
    }
    
```

## Proving With Multiple Type Variables

```acorn
    inductive Nil[T] {
        nil
    }

    let map[T, U]: (Nil[T], T -> U) -> Nil[U] = axiom
    let morph[T]: Nil[T] -> Nil[T] = axiom

    theorem goal[T, U](items: Nil[T], f: T -> U) {
        map(items, f) = morph(map(items, f))
    } by {
        map(items, f) = Nil.nil[U]
        morph(map(items, f)) = Nil.nil[U]
    }
    
```

## Proving With Properties Of Base Typeclass

```acorn
    typeclass F: Foo {
        property: Bool

        property_true {
            F.property
        }
    }

    typeclass B: Bar extends Foo {
        bar_property: Bool
    }

    theorem goal[B: Bar] {
        B.property
    }
    
```

## Proving With Deep Base Theorem

```acorn
    typeclass F: Foo {
        add: (F, F) -> F

        comm(a: F, b: F) {
            a + b = b + a
        }
    }

    typeclass B: Bar extends Foo {
        bar_property: Bool
    }

    typeclass B: Baz extends Bar {
        baz_property: Bool
    }

    theorem goal[B: Baz](a: B, b: B) {
        a + b = b + a
    }
    
```

## Proving With Default Required Attribute

```acorn
    typeclass A: Arf {
        foo: A
        bar: A
    }

    inductive Foo {
        foo
        bar
    }

    instance Foo: Arf

    let diff[A: Arf] = (A.foo != A.bar)

    theorem goal {
        diff[Foo]
    }
    
```

## Proving With Anonymous Function

```acorn
    type Nat: axiom
    let z: Nat = axiom
    let f1: (Nat -> Nat) -> Bool = axiom
    let f2: (Nat -> Nat) -> Bool = axiom

    axiom a1 {
        f1(function(x: Nat) { z })
    }

    axiom a2(h: Nat -> Nat) {
        f1(h) implies f2(h)
    }

    theorem goal {
        f2(function(x: Nat) { z })
    }
    
```

## Semantics Of Let Satisfy Syntax

```acorn
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one {
        zero != one
    }

    let witness: Nat satisfy {
        witness != one
    }

    theorem goal {
        witness != one
    }
    
```

## Semantics Of Destructuring Unwrap Syntax

```acorn
    type Nat: axiom

    inductive Option[T] {
        some(T)
        none
    }

    let n: Nat = axiom
    let wrapped = Option.some(n)
    let Option.some(unwrapped) = wrapped

    theorem goal {
        unwrapped = n
    }
    
```

## Semantics Of Function Satisfy Syntax

```acorn
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one {
        zero != one
    }

    let flip(a: Nat) -> b: Nat satisfy {
        a != b
    }

    theorem goal(a: Nat) {
        a != flip(a)
    }
    
```

## Semantics Of Multivar Let Satisfy Syntax

```acorn
    type Nat: axiom
    let zero: Nat = axiom
    let one: Nat = axiom
    axiom zero_neq_one {
        zero != one
    }

    let (x: Nat, y: Nat) satisfy {
        x != y
    }

    theorem goal {
        x != y
    }
    
```

## Proving With Destructuring

```acorn
    inductive Nat {
        zero
        suc(Nat)
    }

    let one = Nat.suc(Nat.zero)
    let two = Nat.suc(one)
    let Nat.suc(one_again) = two

    theorem goal {
        one_again = one
    }
    
```

## Proving With Polymorphic Destructuring

```acorn
    type Int: axiom

    structure Rat {
        value: Int
    }

    inductive Option[T] {
        some(T)
        none
    }

    let i: Int = axiom
    let Option.some(rat_zero) = Option.some(Rat.new(i))

    theorem goal {
        rat_zero = Rat.new(i)
    }
    
```

## Prover Can Use Instance Forwards

One of two paired tests.
This direction should work - we can use instance relationship in subsequent proofs.

```acorn
    typeclass F: Foo {
        property: Bool
    }

    typeclass B: Bar extends Foo {
        vacuous_condition(b: B) {
            b = b
        }
    }

    type MyType: axiom

    let b: Bool = axiom

    instance MyType: Foo {
        let property: Bool = b
    }

    axiom ax[B: Bar] {
        B.property
    }

    instance MyType: Bar

theorem goal {
    MyType.property
}
    
```

## Prover Uses Parameterized Instance Scheme

```acorn
    typeclass F: Field {
        one: F
    }

    typeclass G: Group {
        id: G
    }

    type Foo: axiom
    let foo: Foo = axiom

    instance Foo: Field {
        let one: Foo = foo
    }

    structure NonZero[T] {
        value: T
    }

    instance NonZero[F: Field]: Group {
        let id: NonZero[F] = NonZero[F].new(Field.one[F])
    }

    theorem goal {
        Group.id[NonZero[Foo]] = Group.id[NonZero[Foo]]
    }
```
