# Good Trace Format

`gtf` is an experimental certificate payload gated by the Cargo feature `gtf`.
The goal is to move certificates toward explicit checker traces instead of the
legacy format where ordinary claim lines rely on the checker to perform hidden
closure.

## Shape

Certificate JSONL records keep the existing `goal` field. With `gtf` enabled,
generated or migrated records contain a compact `g` payload:

```json
{"goal":"goal","g":[{"c":"..."},{"r":"br","c":"...","f":[0]}]}
```

Each GTF step has:

- `r`: the checker rule. Omitted means `claim`.
- `c`: the Acorn-readable claim or legacy certificate line, when the rule needs
  one.
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
- `legacy`: transitional escape hatch that checks one line with the legacy
  checker path. Context-aware migration is expected to compile old proofs to
  explicit non-legacy rules; `legacy` is for low-level experiments and old
  wrapper tests.

## Migration Plan

The verifier migration path replays an existing legacy certificate in memory,
compiles the observed checker trace to GTF, prunes unreferenced auxiliary steps,
and writes a GTF-only certificate. Existing `gtf`/`from` spellings are accepted
as aliases for early experimental files, but new writes use `g`/`f`.

## Current Limitations

The raw `gtf-migrate` command is still a low-level wrapper for old files. The
context-aware migration used for correctness is `verify --ignore-hash` under the
`gtf` feature, because compiling explicit traces requires the active checker
context for imports, local facts, goal assumptions, and witness declarations.

Fresh proof-search generation still passes through the existing
`ConcreteStep -> Certificate` path first, but under the `gtf` feature the
builder immediately compiles those generated legacy proof lines into explicit
GTF using the same context-aware path. If that compilation fails, generation
fails instead of writing a legacy or transitional fallback.

`br_intro` remains an explicit rule for the small number of cases where the
target clause is justified because its boolean-reduction closure is already in
the checker state. Full acornlib migration currently emits this rule rarely.
