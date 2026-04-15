# Lowering

This document defines the only sanctioned elaborator/kernel boundary.

Lowering starts at `AcornValue`. Parsing, syntax, and elaboration are separate concerns and are
not part of this document.

All conversions between `AcornValue` and kernel `Term`/`Clause` objects must go through
`src/elaborator/lowering.rs`.

In particular, these are implementation details, not alternate lowering APIs:

- `src/elaborator/to_term.rs`
- `src/elaborator/term_bridge.rs`
- `src/kernel/clausifier.rs`

Do not import those modules directly from unrelated code.

Adding a new cross-boundary operation is strongly discouraged. The boundary should stay small,
coherent, and hard to misuse. If it grows casually, lowering semantics get duplicated across the
codebase and the elaborator/kernel split becomes sprawling, buggy, and hard to reason about.

If a new boundary operation is truly necessary, add it to `lowering.rs` deliberately and treat it
as a contract change, not a convenience helper.

Normalized-form invariants live in [`normalization.md`](normalization.md).

## Boundary API

These are the conceptual lowering operations:

- `lower_term: AcornValue -> Term`
- `lower_theorem: theorem-shaped AcornValue -> Vec<Clause>`
- `lower_proposition: proposition-shaped AcornValue -> Vec<Clause>`
- `lower_clause: clause-shaped AcornValue -> Clause`
- `quote_term: Term -> AcornValue`
- `quote_clause: Clause -> AcornValue`

These are contract names, not necessarily one public Rust function per line.

## Contracts

`lower_term` is structure-preserving:

- `forall` stays `ForAll`
- `exists` stays `Exists`
- lambda structure stays lambda structure
- logical surface forms become their kernel logical heads

`lower_theorem` lowers theorem syntax:

- theorem binders become free variables in the lowered clause context
- theorem-specific outer binder structure may be interpreted
- it is distinct from proposition lowering even when the implementation shares machinery

`lower_proposition` is semantic boolean lowering:

- it starts from a boolean `AcornValue`
- it lowers to a `Term`
- it normalizes that `Term`
- it lowers the normalized term to clauses
- top-level proposition structure may be opened, especially leading universals

`lower_clause` is the exact clause codec:

- it starts from a quoted clause-shaped `AcornValue`
- it reconstructs exactly one `Clause`
- it does not first apply the semantic normalization used by `lower_proposition`

`quote_term` is general term-to-surface reconstruction.

`quote_clause` is the clause codec paired with `lower_clause`.

## Roundtrip Contract

Only clause lowering has a global exact roundtrip requirement.

The required contract is:

- `lower_clause(quote_clause(c)) == c` for normalized clauses `c`

Theorem lowering and proposition lowering are semantic lowerings, not exact serialization codecs.
