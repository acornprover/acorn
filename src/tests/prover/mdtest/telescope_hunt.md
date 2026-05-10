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

    theorem predicate_attribute_tracks_hidden_function[T, p: T -> Bool, x: T] {
        PredSet[T, p].predicate(x) = p(x)
    }

    theorem accepts_uses_hidden_function[T, p: T -> Bool](x: PredSet[T, p]) {
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

## Explicit Hidden Function Argument With Dependent Return

```acorn
    structure Set[T] {
        contains: T -> Bool
    }

    structure Subspace[T, a: Set[T]] {
        value: T
    } constraint {
        a.contains(value)
    }

    let pick_subspace[T, a: Set[T]]: Subspace[T, a] = axiom

    theorem explicit_hidden_arg_in_return[T, a: Set[T]] {
        pick_subspace[T, a] = pick_subspace[T, a]
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

    theorem nested_function_return_type[T, a: Set[T]](x: Subspace[T, a], value: T) {
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

    let make_const[T, a: Set[T]]: Subspace[T, a] -> T -> Subspace[T, a] =
        function(x: Subspace[T, a]) {
            function(value: T) {
                x
            }
        }

    theorem top_level_nested_function_return_type[T, a: Set[T]](x: Subspace[T, a], value: T) {
        make_const[T, a](x, value) = x
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

    theorem idlike_subspace_is_well_typed[T, a: Set[T]](x: Subspace[T, a]) {
        x.id = x.id
    }
```
