# Local Lets

Expression blocks can start with local lets and end with a final value expression.

## Define Body

```acorn
type Nat: axiom

define local_identity(n: Nat) -> Nat {
    let x = n
    let y: Nat = x
    y
}

theorem local_identity_reduces(n: Nat) {
    local_identity(n) = n
}
```

## Dependent Type Annotation

```acorn
type Nat: axiom

structure Box[n: Nat] {
    value: Nat
}

define local_dependent(n: Nat, box: Box[n]) -> Nat {
    let m = n
    let same: Box[m] = box
    same.value
}

theorem local_dependent_reduces(n: Nat, box: Box[n]) {
    local_dependent(n, box) = box.value
}
```

## If Branches

```acorn
type Nat: axiom

define local_if(p: Bool, a: Nat, b: Nat) -> Nat {
    if p {
        let x = a
        x
    } else {
        let y: Nat = b
        y
    }
}

theorem local_if_then(p: Bool, a: Nat, b: Nat) {
    p implies local_if(p, a, b) = a
}

theorem local_if_else(p: Bool, a: Nat, b: Nat) {
    not p implies local_if(p, a, b) = b
}
```

## Nested If Branches

```acorn
type Nat: axiom

define local_nested_if(p: Bool, q: Bool, a: Nat, b: Nat, c: Nat) -> Nat {
    if p {
        if q {
            let x = a
            x
        } else {
            let y = b
            y
        }
    } else {
        let z: Nat = c
        z
    }
}

theorem local_nested_if_then_then(p: Bool, q: Bool, a: Nat, b: Nat, c: Nat) {
    p and q implies local_nested_if(p, q, a, b, c) = a
}

theorem local_nested_if_then_else(p: Bool, q: Bool, a: Nat, b: Nat, c: Nat) {
    p and not q implies local_nested_if(p, q, a, b, c) = b
}

theorem local_nested_if_else(p: Bool, q: Bool, a: Nat, b: Nat, c: Nat) {
    not p implies local_nested_if(p, q, a, b, c) = c
}
```

## Match Branches

```acorn
type Nat: axiom

inductive Option[T] {
    none
    some(T)
}

define local_match(opt: Option[Nat], fallback: Nat) -> Nat {
    match opt {
        Option.none {
            let y = fallback
            y
        }
        Option.some(x) {
            let z: Nat = x
            z
        }
    }
}

theorem local_match_none(fallback: Nat) {
    local_match(Option.none[Nat], fallback) = fallback
}

theorem local_match_some(x: Nat, fallback: Nat) {
    local_match(Option.some(x), fallback) = x
}
```

## Destructuring Constructed Value

```acorn
type Nat: axiom

inductive Option[T] {
    none
    some(T)
}

define local_unwrap_constructed(n: Nat) -> Nat {
    let Option.some(x) = Option.some(n)
    x
}

theorem local_unwrap_constructed_reduces(n: Nat) {
    local_unwrap_constructed(n) = n
}
```

## Generic Destructuring

```acorn
inductive Option[T] {
    none
    some(T)
}

define local_generic_rebuild[T](value: T) -> Option[T] {
    let Option.some(x) = Option.some(value)
    Option.some(x)
}

theorem local_generic_rebuild_reduces[T](value: T) {
    local_generic_rebuild(value) = Option.some(value)
}
```

## Let Satisfy

```acorn
type Nat: axiom

define local_satisfy_identity(n: Nat) -> Nat {
    let x: Nat satisfy {
        x = n
    }
    x
}

theorem local_satisfy_identity_reduces(n: Nat) {
    local_satisfy_identity(n) = n
}
```

## Let Satisfy With Explicit Proof

```acorn
type Nat: axiom

axiom equal_witness_exists(n: Nat) {
    exists(x: Nat) {
        x = n
    }
}

define local_satisfy_with_proof(n: Nat) -> Nat {
    let x: Nat satisfy {
        x = n
    } by {
        equal_witness_exists(n)
    }
    x
}

theorem local_satisfy_with_proof_reduces(n: Nat) {
    local_satisfy_with_proof(n) = n
}
```

## Let Satisfy In Parameterized Attribute

```acorn
structure Box[T] {
    value: T
}

attributes Box[T] {
    define get(self) -> T {
        let x: T satisfy {
            x = self.value
        }
        x
    }
}

type Nat: axiom
let n: Nat = axiom

theorem attribute_local_satisfy_reduces {
    Box.get(Box.new(n)) = n
}
```

## Let Satisfy In If Branch

```acorn
type Nat: axiom

define local_satisfy_if(p: Bool, n: Nat, fallback: Nat) -> Nat {
    if p {
        let x: Nat satisfy {
            p and x = n
        }
        x
    } else {
        fallback
    }
}

theorem local_satisfy_if_then(p: Bool, n: Nat, fallback: Nat) {
    p implies local_satisfy_if(p, n, fallback) = n
}
```

## Let Satisfy With Proof In If Branch

```acorn
type Nat: axiom

axiom branch_witness_exists(p: Bool, n: Nat) {
    p implies exists(x: Nat) {
        x = n
    }
}

define local_satisfy_if_with_proof(p: Bool, n: Nat, fallback: Nat) -> Nat {
    if p {
        let x: Nat satisfy {
            x = n
        } by {
            branch_witness_exists(p, n)
        }
        x
    } else {
        fallback
    }
}

theorem local_satisfy_if_with_proof_then(p: Bool, n: Nat, fallback: Nat) {
    p implies local_satisfy_if_with_proof(p, n, fallback) = n
}
```

## Destructuring In Match Branch

```acorn
type Nat: axiom

inductive Option[T] {
    none
    some(T)
}

define local_unwrap_or(opt: Option[Nat], fallback: Nat) -> Nat {
    match opt {
        Option.none {
            fallback
        }
        Option.some(x) {
            let Option.some(y) = opt
            y
        }
    }
}

theorem local_unwrap_or_none(fallback: Nat) {
    local_unwrap_or(Option.none[Nat], fallback) = fallback
}

theorem local_unwrap_or_some(x: Nat, fallback: Nat) {
    local_unwrap_or(Option.some(x), fallback) = x
}
```

## Destructuring With Explicit Proof

```acorn
type Nat: axiom

inductive Option[T] {
    none
    some(T)
}

axiom every_option_some(y: Option[Nat]) {
    exists(x: Nat) {
        Option.some(x) = y
    }
}

define local_unwrap_with_proof(y: Option[Nat]) -> Nat {
    let Option.some(x) = y by {
        every_option_some(y)
    }
    x
}

theorem local_unwrap_with_proof_some(n: Nat) {
    local_unwrap_with_proof(Option.some(n)) = n
}
```

## Destructuring Structure

```acorn
type Nat: axiom

structure Pair {
    first: Nat
    second: Nat
}

define local_pair_rebuild(a: Nat, b: Nat) -> Pair {
    let Pair.new(x, y) = Pair.new(a, b)
    Pair.new(x, y)
}

theorem local_pair_rebuild_reduces(a: Nat, b: Nat) {
    local_pair_rebuild(a, b) = Pair.new(a, b)
}
```

## Local Satisfy Obligations In Let RHS

Local witnesses inside expression branches must still create proof obligations before the outer
`let` can use them.

```acorn
type Nat: axiom
let seed: Nat = axiom

let picked: Nat = if true {
    let x: Nat satisfy {
        x = seed
    }
    x
} else {
    seed
}

theorem picked_is_seed {
    picked = seed
}
```

## Local Satisfy In Dead Branch Returns Else

A witness that only appears in a dead branch is exported under that branch's result specification,
not as a top-level inhabitant of its type.

```acorn
type Empty: axiom
type Nat: axiom

let seed: Nat = axiom

define absurd(e: Empty) -> Nat {
    axiom
}

let picked: Nat = if false {
    let x: Empty satisfy {
        true
    }
    absurd(x)
} else {
    seed
}

theorem picked_uses_else {
    picked = seed
}

define choose_dead(p: Bool) -> Nat {
    if false {
        let x: Empty satisfy {
            true
        }
        absurd(x)
    } else {
        seed
    }
}

theorem choose_dead_uses_else(p: Bool) {
    choose_dead(p) = seed
}
```

## Local Satisfy In Dead Branch Cannot Inhabit Empty Type

Branch-local witnesses must not be exported as unconditional witnesses. In particular, a dead
branch cannot manufacture an inhabitant of an arbitrary type.

```acorn,fail
type Empty: axiom

let picked: Bool = if false {
    let x: Empty satisfy {
        true
    }
    true
} else {
    true
}

theorem impossible {
    exists(x: Empty) {
        x = x
    }
}
```

## Local Satisfy Cannot Inhabit Empty Let RHS

```acorn,fail
type Empty: axiom

let bad: Empty = if true {
    let x: Empty satisfy {
        true
    }
    x
} else {
    let y: Empty satisfy {
        true
    }
    y
}

theorem impossible {
    exists(x: Empty) {
        x = x
    }
}
```

## Local Satisfy Obligations In Typeclass Conditions

Typeclass condition claims are elaborated through the same scoped-value path as theorem claims, so
local witnesses there must not become free facts.

```acorn,fail
type Empty: axiom

typeclass B: Bad {
    bogus {
        if true {
            let x: Empty satisfy {
                true
            }
            x = x
        } else {
            true
        }
    }
}

inductive Unit {
    unit
}

instance Unit: Bad {}

theorem impossible {
    exists(x: Empty) {
        x = x
    }
}
```
