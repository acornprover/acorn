# Lowering

This document defines the only sanctioned elaborator/kernel boundary.

Lowering starts at `AcornValue`. Parsing, syntax, and elaboration are separate concerns and are
not part of this document.

Term lowering crosses the boundary directly from `AcornValue`.
Proposition and theorem lowering use `Proposition` so type parameters and source/truthiness stay
attached to the value being lowered.

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

This document uses the Rust boundary names directly. The boundary surface today is:

- `KernelContext::lower_term(...)`
- `KernelContext::lower_theorem_to_clauses(...)`
- `KernelContext::lower_proposition_to_clauses(...)`
- `KernelContext::lower_clause(...)`
- `KernelContext::lower_claim_var_map(...)`
- `KernelContext::quote_term_with_context(...)`
- `KernelContext::quote_clause(...)`

There are also top-level wrappers for proposition and theorem lowering, but the core boundary API
is the `KernelContext` surface above.

## Contracts

`lower_term` is structure-preserving:

- `forall` stays `ForAll`
- `exists` stays `Exists`
- lambda structure stays lambda structure
- logical surface forms become their kernel logical heads

`lower_theorem_to_clauses` lowers theorem syntax:

- theorem binders become free variables in the lowered clause context
- theorem-specific outer binder structure may be interpreted
- it is distinct from proposition lowering even when the implementation shares machinery

`lower_proposition_to_clauses` is semantic boolean lowering:

- it starts from a `Proposition`
- it lowers to a `Term`
- it normalizes that `Term`
- it lowers the normalized term to clauses
- top-level proposition structure may be opened, especially leading universals

`lower_clause` is the exact clause codec:

- it starts from a quoted clause-shaped `AcornValue`
- it reconstructs exactly one `Clause`
- it does not first apply the semantic normalization used by `lower_proposition_to_clauses`

`lower_claim_var_map` is a special-purpose claim-codec operation:

- it lowers the type/value argument lists used by claim-with-args serialization
- it is not general proposition or clause lowering
- it interprets value args in the preloaded namespace where the claim's generic value binders are
  already available as free variables
- it produces the canonical `VariableMap` expected by `Claim`

`quote_term_with_context` is general term-to-surface reconstruction.

`quote_clause` is the clause codec paired with `lower_clause`.

## Roundtrip Contract

Only clause lowering has a global exact roundtrip requirement.

The required contract is:

- `lower_clause(quote_clause(c)) == c` for normalized clauses `c`

Claim-with-args has one additional exact codec requirement:

- if claim serialization emits a quoted clause together with type/value args, then
  `Claim::new(lower_clause(quoted_clause), lower_claim_var_map(type_args, value_args))`
  must reconstruct the canonical claim chosen by the serializer
- equivalently, canonical claim-with-args serialization must satisfy
  `deserialize_claim_with_args(serialize_claim_with_args(claim)) == claim`

Theorem lowering and proposition lowering are semantic lowerings, not exact serialization codecs.
