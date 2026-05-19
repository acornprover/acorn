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

## Prove Predicate About Transported Structure

```acorn
type Nat: axiom
let marked: Nat = axiom

structure Packet[n: Nat] {
    payload: Nat
}

define has_mark(n: Nat, p: Packet[n]) -> Bool {
    p.payload = marked
}

theorem transported_packet_has_mark(n: Nat, k: Nat, x: Packet[n]) {
    n = k implies has_mark(n, x) implies exists(y: Packet[k]) {
        has_mark(k, y)
    }
} by {
    if n = k {
        if has_mark(n, x) {
            let y: Packet[k] = transport x
            has_mark(k, y)
        }
    }
}
```

## Vector Tail

Acorn supports this vector shape as a value-indexed structure over `Fin[n]`.

```acorn
type Nat: axiom

define suc(n: Nat) -> Nat {
    axiom
}

structure Fin[n: Nat] {
    value: Nat
}

define fin_cast_suc(n: Nat, x: Fin[n]) -> Fin[suc(n)] {
    Fin[suc(n)].new(x.value)
}

theorem fin_cast_suc_value(n: Nat, x: Fin[n]) {
    fin_cast_suc(n, x).value = x.value
}

structure Vector[T, n: Nat] {
    entry: Fin[n] -> T
}

define vector_tail_entry[T](n: Nat, xs: Vector[T, suc(n)], i: Fin[n]) -> T {
    xs.entry(fin_cast_suc(n, i))
}

define vector_tail[T](n: Nat, xs: Vector[T, suc(n)]) -> Vector[T, n] {
    Vector[T, n].new(vector_tail_entry[T](n, xs))
}

theorem vector_tail_entry_eq[T](n: Nat, xs: Vector[T, suc(n)], i: Fin[n]) {
    vector_tail[T](n, xs).entry(i) = xs.entry(fin_cast_suc(n, i))
}

theorem transport_preserves_vector_tail[T](m: Nat, n: Nat, xs: Vector[T, suc(m)]) {
    m = n implies true
} by {
    if m = n {
        let ys: Vector[T, suc(n)] = transport xs
        let xt: Vector[T, m] = vector_tail[T](m, xs)
        let yt: Vector[T, n] = vector_tail[T](n, ys)
        let zt: Vector[T, n] = transport xt
        forall(i: Fin[m], j: Fin[n]) {
            if i.value = j.value {
                fin_cast_suc_value(m, i)
                fin_cast_suc_value(n, j)
                fin_cast_suc(m, i).value = fin_cast_suc(n, j).value
                yt.entry(j) = ys.entry(fin_cast_suc(n, j))
                xt.entry(i) = xs.entry(fin_cast_suc(m, i))
                ys.entry(fin_cast_suc(n, j)) = xs.entry(fin_cast_suc(m, i))
                yt.entry(j) = xt.entry(i)
            }
        }
    }
}
```

## Inductive Exact Type Tail

Acorn does not yet support value-indexed inductive families, so this uses exact-type transport over
an inductively defined list and checks that transporting a value also transports its tail coherently.

```acorn
inductive List[T] {
    nil
    cons(T, List[T])
}

attributes List[T] {
    define tail(self) -> List[T] {
        match self {
            List.nil {
                List.nil[T]
            }
            List.cons(head, tail) {
                tail
            }
        }
    }
}

theorem transport_preserves_inductive_tail[T](xs: List[T]) {
    exists(ys: List[T], txs: List[T]) {
        ys = xs and txs = xs.tail and ys.tail = txs
    }
} by {
    let ys: List[T] = transport xs
    let txs: List[T] = transport xs.tail
    ys = xs
    txs = xs.tail
    ys.tail = txs
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
