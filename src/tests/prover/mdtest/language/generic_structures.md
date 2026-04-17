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
