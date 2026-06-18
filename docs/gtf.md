# Good Trace Format

`gtf` is an experimental certificate payload gated by the Cargo feature `gtf`.
The goal is to move certificates toward explicit checker traces instead of the
legacy format where ordinary claim lines rely on the checker to perform hidden
closure.

## Shape

Certificate JSONL records keep the existing `goal` field. With `gtf` enabled,
generated or migrated records contain a compact `p` proof payload:

```json
{"goal":"goal","p":[{"c":"..."},{"r":"br","c":"...","f":[0]}]}
```

Each GTF step has:

- `r`: the checker rule. Omitted means `claim`.
- `c`: the Acorn-readable claim or witness declaration, when the rule needs one.
- `f`: premise step indexes, when the rule needs explicit premises.
- `g`: when present on a step, the step targets the generic clause parsed from
  `c`; otherwise it targets the specialized clause.

Current rules:

- `fact`: direct source/environment fact lookup.
- `claim`: direct exact/egraph lookup.
- `br`: one explicit boolean reduction from a previous step.
- `br_intro`: a claim accepted because the current checker state already
  contains the needed boolean-reduction closure.
- `eq`: local equality-graph check from listed premises.
- `er`: one equality-resolution step from a previous step.
- `ef`: one equality-factoring step from a previous step.
- `ext`: one extensionality step from a previous step.
- `inj`: one injectivity step from a previous step.
- `inst`: instantiate a generic claim from a previous step.
- `wit`: certificate-local witness declaration.
- `contra`: final contradiction marker.

## Migration Plan

The verifier migration path replays an existing legacy certificate in memory,
compiles the observed checker trace to GTF, prunes unreferenced auxiliary steps,
and writes a GTF-only certificate. Existing top-level `g`/`gtf` spellings and
the `from` premise spelling are accepted as aliases for early experimental files,
but new writes use `p`/`f`.

## Current Limitations

Migration is intentionally context-aware and runs through `verify --ignore-hash`
under the `gtf` feature, because compiling explicit traces requires the active
checker context for imports, local facts, goal assumptions, and witness
declarations. The old low-level wrapper that could only wrap legacy proof lines
has been removed.

Fresh proof-search generation still passes through the existing legacy
certificate-step serialization first, but under the `gtf` feature the builder
immediately compiles those generated proof lines into explicit GTF using the same
context-aware path. If that compilation fails, generation fails instead of
writing a legacy or transitional fallback.

`br_intro` remains an explicit rule for the small number of cases where the
target clause is justified because its boolean-reduction closure is already in
the checker state. Full acornlib migration currently emits this rule rarely.
