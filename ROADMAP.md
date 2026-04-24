# The road to dependent types

## Philosophy on planning itself

There are three big goals here. In this order:

1. Acornlib needs to contain all known mathematics.

2. The Acorn language needs to be able to express every concept in mathematics.

3. The AI needs to be good enough to maintain acornlib on its own.

As we run into mathematics that the Acorn language can't handle, we learn what we need to add to the language.

As we add to acornlib, we use AI as much as possible, and learn what situations it can't handle.

Right now, the main blocker is dependent types.

The kernel is now built on dependent types, but they need to be exposed more thoroughly in the surface language.



We are not monomorphizing any more, which makes this more plausible.

### Dependent types frontend

Once the internals support all of the above, it's time to expose dependent types in the frontend in the ways that are useful.

We need to figure out a syntax that can handle things like defining:

```
Fin[k]

Zmod[k]

Vector[Real, k]
```

What else?

## Open Questions

### Generic instance relationships

Relations like:

```
instance Zmod[k]: AdditiveGroup
```

### Question mark syntax.

It seems nice to be able to do

```
let first_plus_last = list.first? + list.last?
```

Here the `?` requires proving that its argument is not none. Like syntactic sugar for

```
let Option.some(first) = list.first
let Option.some(last) = list.last
let first_plus_last = first + last
```

This way you can deal with options that happen inside an expression, not just options that happen inside a statement.

One issue is that the current prover is bad at proving "foo and bar" type goals. The harness could just give the prover one goal at a time when this happens. But we would need to change the interface so that a point in the code could be associated with multiple goals.

Another issue is that syntactically, not every expression can be associated with a proving goal, so this
syntax wouldn't be usable everywhere, which would lead to some confusion.

Another possibility would be to implement a more general solution, a way of expressing when one type could be converted into another type, and treat this as a case of converting an `Option[T]` into a `T`.

Another possibility is to simply punt on implementing this syntax and make the LLMs spell it out.
