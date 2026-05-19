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
