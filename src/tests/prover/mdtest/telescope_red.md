# Telescope Regressions

## Attribute Let Satisfy Captures Dependent Family Value Parameter

This is equivalent to defining the dependent-family attribute directly. The
generated witness constant must be specialized by the ambient family value
parameter before the satisfy claim is exported.

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
        let ambient_set: Set[T] satisfy {
            ambient_set = a
        }
    }

    theorem ambient_set_is_family_parameter[T](a: Set[T]) {
        Subspace[T, a].ambient_set = a
    }
```

## Split Dependent Receiver Typeclass Instance

The value parameters `a` and `b` have different dependent types. The declaration
keeps all type parameters before value parameters while still checking that
distinct value parameters do not collide.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    typeclass T: HasFlag {
        flag: Bool
    }

    structure BiSubspace[T, U, a: Set[T], b: Set[U]] {
        left: T
        right: U
    } constraint {
        a.contains(left) and b.contains(right)
    }

    instance BiSubspace[T, U, a: Set[T], b: Set[U]]: HasFlag {
        let flag: Bool = true
    }

    theorem split_receiver_typeclass[T, U](a: Set[T], b: Set[U]) {
        BiSubspace[T, U, a, b].flag
    }
```

## Nested Dependent Receiver Typeclass Instance

A later family value parameter whose type mentions an earlier value parameter
must lower with the previous value parameters in scope.

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    typeclass T: HasFlag {
        flag: Bool
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

    instance Nested[T, a: Set[T], u: Set[Subspace[T, a]]]: HasFlag {
        let flag: Bool = true
    }

    theorem nested_receiver_typeclass[T](a: Set[T], u: Set[Subspace[T, a]]) {
        Nested[T, a, u].flag
    }
```

## Typeclass Method Uses Dependent Receiver Argument

The method implementation and generated definition must keep the receiver's
family value parameter distinct from the visible method argument.

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
