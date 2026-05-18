# Transport

## Exact Type

```acorn
type Item: axiom

theorem exact_type(x: Item) {
    true
} by {
    let y: Item = transport x
    y = x
}
```

## Indexed Structure

```acorn
type Nat: axiom

structure Box[n: Nat] {
    value: Nat
}

theorem indexed_structure(n: Nat, k: Nat, x: Box[n]) {
    n = k implies true
} by {
    if n = k {
        let y: Box[k] = transport x
        y.value = x.value
    }
}
```

## Function Over Indexed Structure

```acorn
type Nat: axiom
type Item: axiom

structure Fin[n: Nat] {
    value: Nat
}

theorem goal(n: Nat, k: Nat, v: Fin[n] -> Item) {
    n = k implies true
} by {
    if n = k {
        let w: Fin[k] -> Item = transport v
        forall(i: Fin[n], j: Fin[k]) {
            i.value = j.value implies w(j) = v(i)
        }
    }
}
```

## Requires Index Equality

```acorn fail
type Nat: axiom
type Item: axiom

structure Fin[n: Nat] {
    value: Nat
}

theorem bad(n: Nat, k: Nat, v: Fin[n] -> Item) {
    true
} by {
    let w: Fin[k] -> Item = transport v
}
```
