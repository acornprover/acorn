# Normalization

This document defines the contract between the surface-language layers and the kernel layers.
It is the main reference for quoting, lowering, and normalization requirements.

The source implementation for kernel term normalization lives in
`src/kernel/term_normalization.rs`, but the contracts here are broader than that one file.

## Layers

The system moves between these representations:

1. Source text: `String`
2. Parsed syntax: `Expression`
3. Elaborated surface value: `AcornValue`
4. Kernel term: `Term`
5. Kernel clauses: `Vec<Clause>` or a single `Clause`

## Operations Between Layers

These are the conceptual names for the layer transitions:

- `parse: String -> Expression`
- `elaborate: Expression -> AcornValue`
- `lower_term: AcornValue -> Term`
- `lower_theorem: theorem-shaped AcornValue -> Vec<Clause>`
- `lower_proposition: proposition-shaped AcornValue -> Vec<Clause>`
- `lower_clause: clause-shaped AcornValue -> Clause`
- `quote_term: Term -> AcornValue`
- `quote_clause: Clause -> AcornValue`

These names describe contracts, not necessarily one public Rust function per line.
The current code already has all of these behaviors, even if some of them are implemented
by differently named or distributed APIs:

- `lower_term` is implemented today by `lower_value_to_term(...)`
- theorem lowering is not one public function today; it is distributed across
  `lower_fact(...)` / `lower_goal(...)` and their `KernelContext` methods
- proposition lowering currently flows through
  `KernelContext::lower_proposition_to_clauses(...)`
- `lower_clause` is implemented today by `KernelContext::lower_clause(...)`
- `quote_term` is implemented today by `KernelContext::quote_term_with_context(...)`
- `quote_clause` is implemented today by `KernelContext::quote_clause(...)`

The important point is conceptual, not just API naming: theorem lowering, proposition lowering,
and clause lowering are not the same contract.

Code generation is a separate step after quoting:

- `AcornValue -> String`

That step is not part of normalization.

## The Three Lowerings

There are three different boolean-lowering operations that matter.

`lower_term` is structure-preserving:

- `forall(...) { ... }` stays a kernel `ForAll`
- `exists(...) { ... }` stays a kernel `Exists`
- lambda structure stays lambda structure
- logical surface forms become their kernel logical heads

`lower_theorem` lowers a theorem as theorem syntax:

- theorem statement arguments are statement-level binders
- those binders become free variables in the lowered clause context
- theorem lowering is allowed to interpret the theorem-specific outer binder structure

Today theorem statements are first encoded into an external leading-`forall` form, and the
current clausifier opens those leading `forall`s as free variables. So today theorem lowering
reuses the same internal machinery as proposition lowering, but it is still a distinct concept.

`lower_proposition` is logical lowering:

- it starts from a boolean `AcornValue`
- it lowers to a `Term`
- it term-normalizes that `Term`
- it then lowers/clausifies into clauses
- top-level proposition structure may be opened, especially leading universals

`lower_clause` is the certificate/parsing case:

- it starts from a quoted clause-shaped `AcornValue`
- it reconstructs exactly one `Clause`
- it does not first apply the semantic term-normalization pass used by `lower_proposition`
- it is not merely “any proposition that happens to lower to clauses”
- this is the only lowering operation with an exact quote/lower roundtrip requirement

So:

- `lower_term` is the faithful surface-to-kernel term bridge
- `lower_theorem` and `lower_proposition` are semantic/logical lowerings
- `lower_clause` is the exact inverse of `quote_clause` for normalized clauses

Likewise, `quote_term` and `quote_clause` are related but not identical contracts:

- `quote_term` is general term-to-surface reconstruction
- `quote_clause` is the exact clause codec that must satisfy the clause roundtrip contract

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

## Clause Normalization

Clause normalization runs on already-open clauses.

It may:

- normalize literal subterms using term normalization
- sort literals
- remove duplicates
- do best-effort free-variable renumbering

Clause normalization does not justify changing the generic local-variable slots of a certificate
claim. Certificate normalization must preserve those slots.

## Roundtrip Contracts

Only clause lowering has a global exact roundtrip requirement.

The required contract is:

- normalized clause contract:
  quoting a normalized clause must produce a clause-shaped `AcornValue` whose clause-lowering
  result is exactly one normalized clause, and that clause must equal the original `c`

Equivalently:

- `lower_clause(quote_clause(c)) == c`

Theorem lowering and proposition lowering do not need to be exact inverses of quoting. They are
semantic lowerings, not exact serialization codecs.

The term bridge may still have its own local tests and expectations, but the system-wide exact
roundtrip requirement in this document is for clauses.

Example:

- a clause with one local variable of type `Nat` and body `foo(x0)` quotes to a value shaped like
  `forall(x: Nat) { foo(x) }`
- `lower_clause` must reopen that binder and recover the original clause with one free variable in
  its local context

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
- “display shape” is not a substitute for canonical normalization
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

If you change anything related to normalization, clausification, quoting, claim serialization, or
claim parsing, check all of the following:

- term normalization still normalizes all subterms
- normalization is still idempotent
- proof-step clauses are still normalized
- normalized clauses still satisfy the `quote_clause + lower_clause` roundtrip contract
- certificate `(clause, var_map)` pairs still round-trip exactly in normalized form
- any special-case equivalence is really required by the surface syntax, not just convenient
- the tests cover the specific normalized shape that is being protected

If the intended contract changes, update this document and the leading comments in
`src/kernel/term_normalization.rs` together.
