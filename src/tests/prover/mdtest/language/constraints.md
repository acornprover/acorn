# Constraints

These cases focus on structure constraints and the helper theorems they imply.

## Easy Constraint

```acorn
structure Foo {
    first: Bool
    second: Bool
} constraint {
    first or second
}
```

## Constraint Equation

```acorn
structure Foo {
    first: Bool
    second: Bool
} constraint {
    first or second
}
theorem goal(f: Foo) {
    f.first or f.second
}
```

## Constrained Member Equation

```acorn
type Foo: axiom
let foo: Foo = axiom
let foof: Foo -> Bool = axiom
axiom {
    foof(foo)
}

structure Bar {
    f: Foo
} constraint {
    foof(f)
}
theorem goal(f: Foo) {
    foof(f) implies Bar.new(f).f = f
}
```

## Constrained New Option Equations

```acorn
inductive Option[T] {
    none
    some(T)
}

structure Foo {
    value: Bool
} constraint {
    value
}

theorem goal_some_exists(b: Bool) {
    b implies exists(f: Foo) { Foo.new_option(b) = Option.some(f) }
}

theorem goal_some_value(b: Bool, f: Foo) {
    Foo.new_option(b) = Option.some(f) implies f.value = b
}

theorem goal_none(b: Bool) {
    not b implies Foo.new_option(b) = Option.none[Foo]
}
```

## Structure Constraint Attribute Equation

```acorn
structure Foo {
    value: Bool
} constraint {
    value
}

theorem goal(b: Bool) {
    Foo.constraint(b) = b
}
```

## Destructuring Constrained New Option

```acorn
type Int: axiom

let zero: Int = axiom
let one: Int = axiom
let is_reduced: (Int, Int) -> Bool = axiom

axiom zero_one_is_reduced {
    is_reduced(zero, one)
}

inductive Option[T] {
    none
    some(T)
}

structure Rat {
    num: Int
    denom: Int
} constraint {
    is_reduced(num, denom)
}

let Option.some(alt_zero) = Rat.new_option(zero, one)

theorem alt_zero_num {
    alt_zero.num = zero
}
```

## Constrained New Option Round Trips

```acorn
type Int: axiom

let zero: Int = axiom
let one: Int = axiom
let is_reduced: (Int, Int) -> Bool = axiom

axiom zero_one_is_reduced {
    is_reduced(zero, one)
}

inductive Option[T] {
    none
    some(T)
}

structure Rat {
    num: Int
    denom: Int
} constraint {
    is_reduced(num, denom)
}

theorem goal(r1: Rat) {
    Rat.new_option(r1.num, r1.denom) = Option.some(r1)
}
```
