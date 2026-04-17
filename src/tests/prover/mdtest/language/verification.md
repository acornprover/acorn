# Verification

Cases here exercise prover success for definitions, proof obligations, and control-flow constructs.

## Citing A Parametric Theorem

```acorn
type Nat: axiom
let zero: Nat = axiom
theorem foo[T](a: T) { a = a }
theorem goal { foo(zero) }
```

## Using An Imported Axiom

```acorn
type Bar: axiom
let bar: Bar = axiom
let morph: Bar -> Bar = axiom
axiom meq(b: Bar) { morph(b) = morph(bar) }

theorem goal(a: Bar, b: Bar) { morph(a) = morph(b) }
```

## Verify Function Satisfy

```acorn
type Nat: axiom
let zero: Nat = axiom
let one: Nat = axiom
axiom zero_neq_one { zero != one }
let flip(a: Nat) -> b: Nat satisfy {
    a != b
}
```

## Verify If-Else Theorem

```acorn
type Nat: axiom
let f: Nat -> Bool = axiom
let g: Nat -> Bool = axiom
let h: Nat -> Bool = axiom
axiom fgh(a: Nat) {
    if f(a) {
        g(a)
    } else {
        h(a)
    }
}
theorem goal(a: Nat) {
    g(a) or h(a)
}
```

## Verify Function Satisfy With If-Else

```acorn
type Nat: axiom
let suc: Nat -> Nat = axiom
let zero: Nat = axiom
axiom base(a: Nat) {
    a = zero or exists(b: Nat) { a = suc(b) }
}
let pred(a: Nat) -> b: Nat satisfy {
    if a = zero {
        b = zero
    } else {
        suc(b) = a
    }
} by {
    if a != zero {
        exists(b: Nat) { a = suc(b) }
    }
}
```

## Match In Define

```acorn
inductive Foo {
    bar
    baz
}
define foo(f: Foo) -> Bool {
    match f {
        Foo.bar {
            true
        }
        Foo.baz {
            true
        }
    }
}
theorem goal(f: Foo) {
    foo(f)
}
```

## Match In Let

```acorn
inductive Foo {
    bar
    baz
}
let foo: Bool = match Foo.bar {
    Foo.bar {
        true
    }
    Foo.baz {
        false
    }
}
theorem goal {
    foo
}
```

## Recursive Function

```acorn
inductive Nat {
    zero
    suc(Nat)
}
define repeat[T](n: Nat, f: T -> T, a: T) -> T {
    match n {
        Nat.zero {
            a
        }
        Nat.suc(pred) {
            repeat(pred, f, f(a))
        }
    }
}
theorem goal(n: Nat) {
    repeat(Nat.zero, Nat.suc, n) = n
}
```

## Anonymous Axiom

```acorn
let b: Bool = axiom
axiom foo {
    b
}
theorem goal {
    b
}
```
