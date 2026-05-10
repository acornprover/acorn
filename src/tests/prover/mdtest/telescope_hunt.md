# Telescope Hunt

## Higher Order Family Value Parameter Attribute

```acorn
    structure PredSet[T, p: T -> Bool] {
        value: T
    } constraint {
        p(value)
    }

    attributes PredSet[T, p: T -> Bool] {
        let predicate: T -> Bool = p

        define accepts(self) -> Bool {
            p(self.value)
        }
    }

    theorem predicate_attribute_tracks_hidden_function[T](p: T -> Bool, x: T) {
        PredSet[T, p].predicate(x) = p(x)
    }

    theorem accepts_uses_hidden_function[T](p: T -> Bool, x: PredSet[T, p]) {
        x.accepts
    }
```

## Multiple Same Typed Family Values Stay Distinct

```acorn
    type Nat: axiom

    structure Interval[lo: Nat, hi: Nat] {
        value: Nat
    }

    attributes Interval[lo: Nat, hi: Nat] {
        define lower(self) -> Nat {
            lo
        }

        define upper(self) -> Nat {
            hi
        }
    }

    theorem interval_bounds_remain_distinct(lo: Nat, hi: Nat, x: Interval[lo, hi]) {
        x.lower = lo and x.upper = hi
    }
```

## Nested Function Return Mentions Ambient Family Value

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    attributes Subspace[T, a: Set[T]] {
        let make_const: Subspace[T, a] -> T -> Subspace[T, a] = function(x: Subspace[T, a]) {
            function(value: T) {
                x
            }
        }
    }

    theorem nested_function_return_type[T](a: Set[T], x: Subspace[T, a], value: T) {
        x.make_const(value) = x
    }
```

## Top Level Nested Function Return Mentions Family Value

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    define make_const[T](a: Set[T], x: Subspace[T, a], value: T) -> Subspace[T, a] {
        x
    }

    theorem top_level_nested_function_return_type[T](a: Set[T], x: Subspace[T, a], value: T) {
        make_const[T](a, x, value) = x
    }
```

## Dependent Typeclass Method Well Typed

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    typeclass T: IdLike {
        id: T -> T
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    instance Subspace[T, a: Set[T]]: IdLike {
        let id: Subspace[T, a] -> Subspace[T, a] = function(x: Subspace[T, a]) {
            x
        }
    }

    theorem idlike_subspace_is_well_typed[T](a: Set[T], x: Subspace[T, a]) {
        x.id = x.id
    }
```

## Function Value Parameter Returning Dependent Family

The family value parameter `f` has a function type whose return type mentions
the earlier family value parameter `a`. Projecting `x.key` should infer the
hidden family value arguments without confusing the shifted reference to `a`
inside `f`'s return type with `f` itself.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    structure Fiber[T, U, a: Set[T], f: U -> Subspace[T, a]] {
        key: U
    } constraint {
        a.contains(f(key).value)
    }

    theorem fiber_key_projection_typechecks[T, U](
        a: Set[T], f: U -> Subspace[T, a], x: Fiber[T, U, a, f]) {
        x.key = x.key
    }
```

## Function Value Parameter Taking Dependent Family

The family value parameter `f` has a function type whose argument type mentions
the earlier family value parameter `a`. Projecting `x.point` should infer the
hidden family value arguments while matching a dependent function argument.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    structure Image[T, U, a: Set[T], f: Subspace[T, a] -> U] {
        point: Subspace[T, a]
    } constraint {
        f(point) = f(point)
    }

    theorem image_point_projection_typechecks[T, U](
        a: Set[T], f: Subspace[T, a] -> U, x: Image[T, U, a, f]) {
        x.point = x.point
    }
```

## Function Value Parameter With Dependent Argument And Return

This combines the previous two shapes: the family value parameter `f` takes a
dependent-family argument and returns that same dependent family under two
visible function binders.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    structure Transport[T, U, a: Set[T], f: (Subspace[T, a], U) -> Subspace[T, a]] {
        point: Subspace[T, a]
        key: U
    } constraint {
        a.contains(f(point, key).value)
    }

    theorem transport_projection_typechecks[T, U](
        a: Set[T], f: (Subspace[T, a], U) -> Subspace[T, a],
        x: Transport[T, U, a, f]) {
        x.point = x.point and x.key = x.key
    }
```

## Later Family Value Parameter Mentions Function Value Parameter

A later family value parameter may have a type that mentions an earlier
function-valued family parameter. This exercises the base telescope order before
that function's own visible binder shifts its return type.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    structure Fiber[T, U, a: Set[T], f: U -> Subspace[T, a]] {
        key: U
    } constraint {
        a.contains(f(key).value)
    }

    structure FiberBag[T, U, a: Set[T], f: U -> Subspace[T, a], bag: Set[Fiber[T, U, a, f]]] {
        item: Fiber[T, U, a, f]
    } constraint {
        bag.contains(item)
    }

    theorem fiber_bag_item_projection_typechecks[T, U](
        a: Set[T], f: U -> Subspace[T, a],
        bag: Set[Fiber[T, U, a, f]], x: FiberBag[T, U, a, f, bag]) {
        x.item = x.item
    }
```

## Attribute Uses Function Family Value Parameter

An attribute body can mention both a function-valued family parameter and a
field whose type depends on the same telescope.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    structure Fiber[T, U, a: Set[T], f: U -> Subspace[T, a]] {
        key: U
    } constraint {
        a.contains(f(key).value)
    }

    attributes Fiber[T, U, a: Set[T], f: U -> Subspace[T, a]] {
        define image_value(self) -> T {
            f(self.key).value
        }
    }

    theorem fiber_image_value_def[T, U](
        a: Set[T], f: U -> Subspace[T, a], x: Fiber[T, U, a, f]) {
        x.image_value = f(x.key).value
    }
```

## Top Level Curried Return With Explicit Value Argument

Ordinary declarations now put value parameters in `()`. Returning a curried
function should still preserve the explicit value argument `a` in the returned
function type.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    define make_curried[T](a: Set[T]) -> Subspace[T, a] -> T -> Subspace[T, a] {
        function(x: Subspace[T, a]) {
            function(value: T) {
                x
            }
        }
    }

    theorem top_level_curried_return_type[T](a: Set[T], x: Subspace[T, a], value: T) {
        make_curried(a)(x, value) = x
    }
```
