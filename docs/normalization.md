# Normalization

This document defines the normalization contract for kernel terms, clauses, proof steps, and
certificate `(clause, var_map)` pairs.

The source implementation for term normalization lives in
`src/kernel/term_normalization.rs`, but the requirements here are broader than that one file.

## Scope

There are three distinct normalization layers:

1. Term normalization
2. Theorem lowering
3. Clause normalization

These layers are related, but they are not interchangeable.

## Term Normalization

Term normalization is the recursive, structure-preserving normalization of `Term`s.

It must:

- normalize every subterm of a normalized term
- beta-reduce head lambda applications
- cancel double negation
- order fully applied equality terms
- recurse under binders

It must not:

- open leading quantifiers just because a term happens to be theorem-shaped
- do clause-level cleanup such as literal sorting or clause deduplication
- depend on proof-search heuristics or checker-specific conveniences

## Theorem Lowering

Theorem lowering is stronger than term normalization.

It may:

- open leading universal binders
- lower clause-shaped propositions into clauses

It does not belong in `term_normalization.rs`.

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
- serializing a certificate `(clause, var_map)` pair and deserializing it must recover the exact
  same normalized generic `(clause, var_map)` pair
- normalization canonicalizes the built-in commutative operators `=`, `and`, and `or` up to
  commutativity only
- clause normalization may deterministically renumber free variables to a preferred numbering, but
  that renumbering is best-effort only
- normalization must be idempotent

## Certificate-Specific Rules

Certificates are especially sensitive because they sit at the boundary between kernel terms and
surface syntax.

For certificate claims:

- the stored generic clause is the canonical object
- the `var_map` is part of the canonical object
- “display shape” is not a substitute for canonical normalization
- parser or codegen conveniences should not introduce a second, fuzzier notion of normalized form

If a serializer/parser gap forces an exception, that exception should be described narrowly and
treated as technical debt, not as a new normalization layer.

## Change Checklist

If you change anything related to normalization, clausification, denormalization, claim
serialization, or claim parsing, check all of the following:

- term normalization still normalizes all subterms
- normalization is still idempotent
- proof-step clauses are still normalized
- certificate `(clause, var_map)` pairs still round-trip exactly in normalized form
- any special-case equivalence is really required by the surface syntax, not just convenient
- the tests cover the specific normalized shape that is being protected

If the intended contract changes, update this document and the leading comments in
`src/kernel/term_normalization.rs` together.
