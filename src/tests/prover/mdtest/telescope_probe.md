# Telescope Probe

## Interleaved Family Parameters In Structure Constraint

This green control shows that the core ordered telescope survives a structure
constraint even when a value parameter appears between two type parameters.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Tagged[T, a: Set[T], U] {
        left: T
        right: U
    } constraint {
        a.contains(left)
    }

    theorem tagged_value_type[T, a: Set[T], U](x: Tagged[T, a, U]) {
        a.contains(x.left)
    }
```

## Later Value Parameter Depends On Earlier Value Parameter

This green control shows that a later value-parameter type can mention an
earlier value parameter through a nested dependent family.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    structure Nested[T, a: Set[T], u: Set[Subspace[T, a]]] {
        point: Subspace[T, a]
    } constraint {
        u.contains(point)
    }

    theorem nested_constraint[T, a: Set[T], u: Set[Subspace[T, a]], x: Nested[T, a, u]] {
        u.contains(x.point)
    }
```

## Dependent Value Parameter Nullary Typeclass Attribute

A nullary typeclass attribute should replay in strict certificate mode for an
instance whose receiver has a dependent value parameter.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    typeclass T: Marker {
        marked: Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    instance Subspace[T, a: Set[T]]: Marker {
        let marked: Bool = true
    }

    theorem subspace_marked[T, a: Set[T]] {
        Subspace[T, a].marked
    }
```

## Attributes Block With Dependent Value Parameter

An `attributes` block should be able to introduce a value parameter for a
dependent datatype family.

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
        let carrier: Subspace[T, a] -> T = function(x: Subspace[T, a]) {
            x.value
        }
    }

    theorem subspace_carrier[T, a: Set[T]](x: Subspace[T, a]) {
        x.carrier = x.value
    }
```

