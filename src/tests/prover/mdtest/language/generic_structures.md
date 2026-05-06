# Generic Structures

## Generic Structure Definition

The theorems below are direct implications of the structure definition.

```acorn
structure Pair[T, U] {
    first: T
    second: U
}

theorem check_first[T, U](t: T, u: U) {
    Pair.new(t, u).first = t
}

theorem check_second[T, U](t: T, u: U) {
    Pair.new(t, u).second = u
}

theorem check_new[T, U](p: Pair[T, U]) {
    Pair.new(p.first, p.second) = p
}
```

## Imported Generic Structure

```acorn
structure Pair[T, U] {
    first: T
    second: U
}

theorem check_first[T, U](t: T, u: U) {
    Pair.new(t, u).first = t
}

theorem check_second[T, U](t: T, u: U) {
    Pair.new(t, u).second = u
}

theorem check_new[T, U](p: Pair[T, U]) {
    Pair.new(p.first, p.second) = p
}
```

## Instance Of Generic Structure

```acorn
structure Pair[T, U] {
    first: T
    second: U
}

type Foo: axiom

theorem foo_pair_first(a: Foo, b: Foo) {
    Pair.new(a, b).first = a
}

theorem foo_pair_second(a: Foo, b: Foo) {
    Pair.new(a, b).second = b
}

theorem foo_pair_new(p: Pair[Foo, Foo]) {
    Pair.new(p.first, p.second) = p
}
```

## Generic Constraint

```acorn
structure EqCheckedPair[T] {
    first: T
    second: T
    eq: Bool
} constraint {
    eq implies first = second
}

type Foo: axiom

theorem check_constraint(p: EqCheckedPair[Foo]) {
    p.eq implies p.first = p.second
}
```

## Dependent Value Parameter Uses Earlier Typeclass Parameter

This covers structure family parameters where a later value parameter depends on
an earlier constrained type parameter.

```acorn
type Set[T]: axiom

typeclass T: Blah {
    marker: T -> Bool
}

structure Subspace[T: Blah, a: Set[T]] {
    value: T
}
```

## Dependent Structure Projections And Instances

```acorn
type Set[T]: axiom

typeclass T: Blah {
    marker: T -> Bool
}

structure Subspace[T: Blah, a: Set[T]] {
    value: T
}

theorem subspace_round_trip[T: Blah, a: Set[T]](x: T) {
    Subspace[T, a].new(x).value = x
}

typeclass X: AlwaysTrue {
    ok: X -> Bool

    ok_true(x: X) {
        x.ok
    }
}

instance Subspace[T: Blah, a: Set[T]]: AlwaysTrue {
    define ok(self) -> Bool {
        true
    }
}

theorem subspace_ok[T: Blah, a: Set[T]](x: Subspace[T, a]) {
    x.ok
}
```

## Function Satisfy Keeps Generic Structure Parameter Order

This covers a regression where symbol registration inferred type parameters in
alphabetical order rather than declaration order, swapping `O` and `M`.

```acorn
structure Inner[O, M] {
    a: M -> O
}

structure Outer[O, M] {
    first: Inner[O, M]
}

let make_outer[O, M](i: Inner[O, M]) -> result: Outer[O, M] satisfy {
    result = Outer.new(i)
}

theorem make_outer_first[O, M](i: Inner[O, M]) {
    make_outer(i).first = i
}
```
