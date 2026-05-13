# Empty-Codomain Surjectivity

## Cached Certificate Replay

`verify` must not write a certificate that `check` immediately rejects.

```acorn
define is_surjective_fn[T, U](f: T -> U) -> Bool {
    forall(y: U) {
        exists(x: T) {
            f(x) = y
        }
    }
}

theorem function_to_empty_is_surjective[T, U](f: T -> U) {
    not exists(y: U) { true } implies is_surjective_fn(f)
} by {
    if not exists(y: U) { true } {
        if not is_surjective_fn(f) {
            let y: U satisfy {
                not exists(x: T) {
                    f(x) = y
                }
            }
            exists(witness: U) {
                witness = y
            }
            false
        }
        is_surjective_fn(f)
    }
}
```
