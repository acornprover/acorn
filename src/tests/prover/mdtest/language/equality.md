# Equality

## Boolean Equality

```acorn
let a: Bool = axiom
let b: Bool = axiom
axiom {
    a implies b
}
axiom {
    b implies a
}
theorem goal {
    a = b
}
```

## Implies Keyword

```acorn
let a: Bool = axiom
theorem {
    a implies a
}
theorem {
    not a implies not a
}
```
