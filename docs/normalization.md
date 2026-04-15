# Normalization

This document defines normalized kernel objects and normalized certificate claims.

Layer transitions and quote/lower roundtrip contracts live in [`lowering.md`](lowering.md).

## Term Normalization

Term normalization is the recursive, structure-preserving normalization of `Term`s.

It must:

- normalize every subterm of a normalized term
- beta-reduce head lambda applications
- eta-reduce lambdas that only forward their bound variables
- cancel double negation
- order fully applied equality terms
- recurse under binders

It must not:

- open leading quantifiers just because a term happens to be theorem-shaped
- do clause-level cleanup such as literal sorting or clause deduplication
- depend on proof-search heuristics or checker-specific conveniences

## Clause Normalization

Clause normalization runs on already-open clauses.

It may:

- normalize literal subterms using term normalization
- sort literals
- remove duplicates
- do best-effort free-variable renumbering

Clause normalization does not justify changing the generic local-variable slots of a certificate
claim. Certificate normalization must preserve those slots.

## Global Requirements

The system-wide normalization requirements are:

- every `ProofStep` must have its clause normalized
- in a normalized term or clause, every subterm must also be normalized
- for certificates, the generic clause in a `(clause, var_map)` claim must be normalized
- for certificates, each mapped term in a claim `var_map` must be term-normalized
- parsing a non-normalized certificate claim must normalize into that canonical `(clause, var_map)`
  object rather than preserving a merely display-equivalent surface shape
- serializing a certificate `(clause, var_map)` pair and deserializing it must recover the exact
  same normalized generic `(clause, var_map)` pair
- normalization canonicalizes the built-in commutative operators `=`, `and`, and `or` up to
  commutativity only
- clause normalization may deterministically renumber free variables to a preferred numbering, but
  that renumbering is best-effort only
- normalization must be idempotent

## Certificate-Specific Rules

Certificates sit at the boundary between quoted kernel objects and surface syntax.

For certificate claims:

- the stored generic clause is the canonical object
- the `var_map` is part of the canonical object
- `claim-with-args` syntax is only a surface serialization of that canonical `(clause, var_map)`
  object
- "display shape" is not a substitute for canonical normalization
- parser or codegen conveniences should not introduce a second, fuzzier notion of normalized form
- serializing a `claim-with-args` must use the normal quote/lower bridge:
  the generic body comes from `quote_clause`, and each mapped value argument uses the usual
  quoted-term form
- parsing a `claim-with-args` must use the normal normalization path on each part:
  the generic function body must lower and normalize to the canonical generic clause, and each
  supplied argument must lower and normalize before it is stored in `var_map`
- claim-with-args roundtripping should be expressed in terms of the normal body-clause roundtrip
  plus the normal argument-term roundtrip, not checker-specific equivalence notions

If a serializer/parser gap forces an exception, that exception should be described narrowly and
treated as technical debt, not as a new normalization layer.

## Change Checklist

If you change anything related to normalization, lowering, quoting, claim serialization, or claim
parsing, check all of the following:

- term normalization still normalizes all subterms
- normalization is still idempotent
- proof-step clauses are still normalized
- the clause codec still satisfies the `quote_clause + lower_clause` roundtrip contract
- certificate `(clause, var_map)` pairs still round-trip exactly in normalized form
- any special-case equivalence is really required by the surface syntax, not just convenient
- the tests cover the specific normalized shape that is being protected

If the intended contract changes, update this document, [`lowering.md`](lowering.md), and the
leading comments in `src/kernel/term_normalization.rs` together.
