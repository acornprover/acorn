---
name: "Explicate Feature Flag"
description: "Use when a proof/module verifies in baseline mode but reproving under a prover-affecting feature flag fails. Add explicit proof detail based on the working baseline proof until `cargo run --features <feature> -- verify ...` succeeds."
---

This is the feature-flag version of `explicate`.

Use it when:

- default/baseline reproving works
- a feature flag changes prover behavior
- feature-mode reproving fails or times out
- the right response is to add explicit proof steps to acornlib source, not to debug prover internals yet

This skill is for the `acorn` repo. Use `cargo run`, not the installed `acorn` binary.
Edit proofs only in the sibling library repo at `../acornlib/src`.
Do **not** edit the bundled copy under `vscode/extension/acornlib`.

## Scope

The goal is:

- baseline proof remains valid
- feature-mode reproving succeeds

The non-goal is:

- proving that feature+`validate` is fast

During the edit loop, do **not** use `validate`. Use feature-only reproving for speed.
Add only one proof line per iteration.
Only explicate at the location where the feature-flag prover is having trouble.
Do not inline a large proof body. The point is to make the local proof easier for the flagged prover to rediscover, not to copy an entire theorem proof into the file.

## Prerequisite

First confirm the baseline module is actually good:

```bash
cargo run --profile release -- verify MODULENAME --ignore-hash --read-only --fail-fast
```

If baseline fails, this is not an explication task.

Then confirm the feature-mode failure:

```bash
cargo run --profile release --features FEATURE -- verify MODULENAME --ignore-hash --read-only --fail-fast
```

If feature mode panics or crashes, stop. That is a prover/feature bug, not an explication task.

## Explicating One Module

Find the first failing line in feature mode:

```bash
cargo run --profile release --features FEATURE -- verify MODULENAME --ignore-hash --read-only --fail-fast
```

If this succeeds, the module is done.

If it fails, note the failing line and move to line-level proof inspection.

## Explicating One Line

Inspect the _working baseline_ proof, not the failing feature-mode proof:

```bash
cargo run --profile release -- select MODULENAME LINENUMBER
```

If `select` is too compressed, use:

```bash
cargo run --profile release -- verify MODULENAME:LINENUMBER --ignore-hash --read-only --print-proof
```

Use baseline proof steps whose reasons are:

- definitions
- theorems
- boolean reduction
- simplification

Add those statements to `../acornlib/src/...`:

- before the target line, or
- at the end of the target line’s `by` block, if it has one

Do not delete statements. Only add detail.
Add a single line at a time.
After you add one line, test immediately before adding another.

## Iteration Loop

After each edit:

1. Check the module in baseline mode, without `--read-only`:

```bash
cargo run --profile release -- verify MODULENAME --ignore-hash --fail-fast
```

2. Then check the module in feature mode:

```bash
cargo run --profile release --features FEATURE -- verify MODULENAME --ignore-hash --read-only --fail-fast
```

If baseline fails, the explication is wrong. Fix the proof shape first.

If feature mode still fails, use the new failure location to decide where the next single line goes:

- if the failing point is still the same target, add the next line immediately around that target
- if the failure moves earlier, the next added line should go before the previous insertion point
- if the failure moves later, the next added line should go after the previous insertion point

If feature mode now fails on a later line, move to that new line.

## Writing Cache

During this skill, every edit should be followed by baseline `verify` without `--read-only`.
That is the normal workflow, not a special case.

## Stopping Conditions

Keep explicating as long as the baseline proof still contains harvestable proof steps.

Only stop and report a feature bug when **both** are true:

1. the baseline version of the target line has been fully explicated, meaning `select`/`--print-proof` no longer gives you any useful proof steps to harvest for that line, and
2. feature-mode reproving of that same line still fails

In practice, "fully explicated" usually means the baseline target is trivial or nearly trivial and there are no remaining definition/theorem/boolean-reduction/simplification steps worth materializing.

Also stop and report a feature bug if:

- feature-mode verify panics
- the proof only fails under `validate`, while plain feature-mode reproving succeeds

That last case is not an explication target. It is a performance/debugging issue in validation mode.

## Final Check

When the module seems fixed, rerun:

```bash
cargo run --profile release --features FEATURE -- verify MODULENAME --ignore-hash --read-only --fail-fast
```

If it succeeds, the explication work for that module is done.
