# Proof Blocks

Small proof blocks are easier to scan as markdown than as a long Rust file.

## Proof Inside Theorem Block

```acorn
type Thing: axiom
let t: Thing = axiom
theorem reflexivity(x: Thing) {
    x = x
} by {
    reflexivity(t)
}
```

## Proof Inside Forall Block

```acorn
type Thing: axiom
let t: Thing = axiom
let foo: Thing -> Bool = axiom
axiom foo_t { foo(t) }
forall(x: Thing) {
    x = t implies foo(x)
}
```

## Proof Inside If Block

```acorn
type Thing: axiom
forall(x: Thing, y: Thing) {
    if x = y {
        x = y
    }
}
```

## Proof Inside Destructuring Let

```acorn
type Nat: axiom

inductive Option[T] {
    none
    some(T)
}

let y: Option[Nat] = axiom

let Option.some(x) = y by {
    let witness: Nat = axiom
    axiom witness_eq {
        Option.some(witness) = y
    }
    witness_eq
}

theorem destructured_value {
    Option.some(x) = y
}
```
