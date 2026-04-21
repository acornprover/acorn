---
name: reproduce-prover-failure
description: "Use when a theorem or goal ought to prove but the prover fails in acornlib or an issue repro. Classify whether the failure is a shallow explosion or an interactive timeout/activation-cap case that should reproduce as `--shallow` exhaustion, then narrow it to a local repro and, once approved, turn a single positive `verify_succeeds` case into an mdtest."
---

Use this when:

- acornlib verification fails on something that should prove
- an issue report needs to be narrowed to a real prover repro
- the immediate job is to reproduce and minimize the failure, not to fix prover internals yet

This skill is for the `acorn` repo. Use `cargo run`, not the installed `acorn` binary.
Keep scratch work in `/tmp` or a scratch project. Do **not** edit the bundled library under
`vscode/extension/acornlib`.
If your scratch repro uses imports and those imports should resolve against the scratch library
rather than the default local `acornlib`, run with `--lib /path/to/scratch_project`.
Do not assume `verify /tmp/.../src/foo.ac` will make imports local by itself.

## Key Principle

In unit tests, `verify_succeeds` only accepts shallow success.
If shallow search fails, the helper may print a deep follow-up proof, but the test still fails.

Whether a proof is shallow is deterministic and does not change just because a lot of unrelated
context exists around it.

There are two reproducible shapes to aim for:

1. `ShallowExplosion`
   This can sometimes be reduced to a clean test repro, but not always. If the shallow frontier is
   merely very large, the right deliverable may be analysis rather than an mdtest.
2. Interactive `Timeout` or `ActivationCap` that should succeed shallowly
   Treat this as a shallow-exhaustion repro problem. Rerun with `--shallow` and preserve
   `ShallowExhausted` as the oracle while reducing. This should be reproducible in a separate local
   file and then in mdtests, because mdtests can reproduce shallow exhaustion.

## Classification

There are two cases:

1. `ShallowExplosion`
   First determine which kind of shallow explosion it is.
   Before minimizing, raise the activation cap and inspect the shallow activation trace for a
   single selected goal, for example:

   ```bash
   RUST_LOG=acorn::prover::activation=trace \
   cargo run --profile release -- verify MODULENAME:LINE --read-only --fail-fast --activations 20000 --verbose
   ```

   `--verbose` requires a single selected line.

   There are two subcases:

   - A single rule or pattern is generating a practically unbounded number of shallow steps.
     This is the shallow-explosion case that can often be minimized to a clean repro.
     You can identify it because even after materially raising `--activations`, you still do not
     reach the end of the shallow frontier.
     In this case, the reduced repro must also end in `ShallowExplosion`.
     Do **not** accept `ShallowExhausted`, `Exhausted`, activation-cap failures, or any other
     non-success outcome as "close enough".
   - The shallow frontier is just large.
     In this case, raising `--activations` eventually gets through the shallow frontier or leaves
     it, and the problem is not a cleanly reproducible unbounded shallow-generation bug.
     Usually this cannot be reduced to a useful unit test.
     The goal becomes explaining the shallow search rather than forcing a tiny repro:
     report how many shallow activations it takes to clear the frontier and what rules or
     patterns dominate those activations.

   For either subcase, keep minimizing or analyzing until you have tried removing every plausible
   part of the context and understand which declarations or rules are responsible.
2. Interactive `Timeout` or `ActivationCap`
   This should be turned into a shallow repro immediately.
   Rerun the original goal with `--shallow` and preserve `ShallowExhausted` as the intended
   outcome while reducing, for example:

   ```bash
   cargo run --profile release -- verify MODULENAME:LINE --ignore-hash --read-only --fail-fast --shallow
   ```

   If the `--shallow` rerun does **not** give `ShallowExhausted`, stop and reclassify the bug
   instead of pushing ahead with the wrong oracle.

   A true interactive-timeout-or-activation-cap repro for this skill should always reduce to:

   - a local scratch repro that still gives `ShallowExhausted` under `--shallow`
   - then a positive mdtest that fails under `verify_succeeds`

## Workflow

### 1. Reproduce Once In The Original Context

Use the smallest command that already shows the failure.
Prefer targeted commands over full-library runs.

For acornlib module failures, typical starting points are:

```bash
cargo run --profile release -- verify MODULENAME --ignore-hash --read-only --fail-fast
```

or, if you need the checker-style path:

```bash
cargo run --profile release -- check MODULENAME
```

Record:

- the failing module
- the failing goal or theorem
- the line number if you have one
- the observed shallow outcome if it is available

If the original command fails with interactive `Timeout` or `ActivationCap`, rerun the same target
with `--shallow` before you minimize anything. That `ShallowExhausted` result is the oracle you
are trying to preserve in the scratch repro and the mdtest.

For `ShallowExplosion`, also record:

- the activation cap you used
- whether raising `--activations` still leaves you in `ShallowExplosion`
- which activated rules or clause patterns dominate the shallow trace

### 2. Get It Running In A Scratch Repro

If the bug is in acornlib, copy a generous slice of relevant context into `/tmp` or a scratch
module first.
If the bug comes from an issue, start from the reported snippet and add only what is missing.

If the scratch repro has imports, make it a real scratch library root with `acorn.toml`, `src/`,
and `build/`, and verify it with `--lib` pointing at that root, for example:

```bash
cargo run --profile release -- --lib /tmp/repro verify src/repro.ac --read-only --fail-fast
```

Without `--lib`, imports may silently resolve against the default local `acornlib`, which does
not count as a local repro.

The first scratch repro does **not** need to be minimal.
It only needs to fail in the same way.

For an original `ShallowExplosion`, "the same way" is strict:

- the scratch repro should also end in `ShallowExplosion`
- if it changes to a different failure mode, treat that as a different bug shape, not progress
- keep the original shallow-explosion outcome visible as the invariant while reducing

But do this only for the unbounded-shallow-generation subcase.
If the investigation shows that the original issue is merely a very large but finite shallow
frontier, do not force a fake minimal repro.
Instead keep the larger local scratch context and use it to explain the shallow-step breakdown.

For an original interactive `Timeout` or `ActivationCap`, "the same way" means:

- the scratch repro should still give `ShallowExhausted` when run with `--shallow`
- you may use ordinary `verify` while exploring, but `--shallow` is the oracle that matters
- do not accept a repro that only fails in interactive mode but succeeds with `--shallow`

### 3. Narrow Aggressively

Reduce the scratch repro a small step at a time.
After each reduction, rerun the smallest repro immediately.
Assume the human wants exhaustive minimization by default.
Do **not** stop to ask whether to keep pushing.
Keep going until you have tried removing every plausible declaration, import, proof body,
definition detail, and module boundary that might still be irrelevant.

Preferred simplifications:

- remove declarations that come after the failing goal
- remove imports, definitions, theorems, and datatypes that are not used
- replace complicated definitions with `axiom`
- replace supporting theorems that you still use with `axiom`
- inline only the constants and types needed to keep the goal meaningful
- remove proof text that is not required for the failure
- split reductions apart instead of deleting many things at once, so you know exactly which piece
  preserves the failing outcome
- when the repro still spans multiple files, try collapsing each imported file independently and
  also try replacing the whole import with smaller local stand-ins

Do not preserve original structure for its own sake.
The target is a tiny self-contained repro, not a faithful miniature of acornlib.

For a final mdtest candidate, **everything must be local**.
Do not stop while the repro still imports from acornlib.
Copy over or replace imported support with local declarations, axioms, or tiny local theorems
until the failing snippet stands alone.

### 4. Preserve The Right Oracle

Keep the same intended successful goal.
For prover regressions, prefer a positive repro that should pass `verify_succeeds`.

That is the correct unit-test oracle because it fails when shallow search fails, even if deep
search could eventually succeed.

For a shallow-explosion investigation, preserve the exact shallow outcome as well as the goal.
A repro that merely fails differently is not yet reproducing the same issue.

For the large-finite-frontier shallow-explosion subcase, preserve the exact shallow outcome while
measuring it, but do not insist on turning it into a unit test.
The correct deliverable there is an explanation of the shallow search:

- how many shallow activations it takes to clear the frontier
- whether the search then succeeds, exhausts, or leaves the shallow fragment
- which rules, definitions, or clause families generate most of the shallow work

For interactive-`Timeout`/`ActivationCap` repros, do **not** relax the oracle to some other
non-success outcome. Preserve `ShallowExhausted` under `--shallow`; that is what makes the repro
suitable for both a standalone file and an mdtest.

Temporary debugging aids are fine while reducing, but the end state should be a small proof that
ought to verify.

When the theorem shape is `A implies B`, do **not** keep a leading `if A` unless you have already
checked that it is genuinely needed for the minimized bug.
Normally the `if` is redundant and should be removed.
If the failure only reproduces with the `if`, keep minimizing and treat that as a sign that the
repro is still carrying extra structure.

### 5. Decide Whether To Stop Or Escalate

You have a good repro when:

- the snippet is self-contained
- the failure still happens
- you have explicitly tried removing every plausible remaining piece of context
- every remaining deletion or simplification attempt changes the shape of the bug rather than
  simplifying it

If the reduced repro still fails shallowly, keep it.

But if the original issue was specifically `ShallowExplosion`, only keep the repro if it is still
`ShallowExplosion`.

If the original issue was interactive `Timeout` or `ActivationCap`, only keep the repro if it
still gives `ShallowExhausted` under `--shallow`.

If raising `--activations` shows that the shallow frontier is finite and the issue is really just
"too many shallow steps", do not keep pushing for a tiny mdtest-style repro.
Stop when you have:

- a local scratch context that exhibits the large shallow frontier
- a count or lower bound for how many shallow activations it takes to get through it
- a concrete breakdown of which rules or patterns account for most of that shallow work

If every reduced repro succeeds and only the large original context fails, treat that as evidence
of `ShallowExplosion` and bring it to a human instead of forcing a unit test.
When you stop, report what categories of reductions you tried so the human can see that the
minimization was exhaustive rather than merely "pretty small".

## Handoff

Once you have a minimal repro:

- share the snippet with the human first
- say whether it is a `ShallowExplosion` repro or a `--shallow` `ShallowExhausted` repro
- explain what was replaced with axioms and what was removed

If the result is a large-finite-frontier shallow explosion rather than an unbounded shallow
generation bug:

- share the local scratch context or target command instead of forcing a tiny snippet
- report the activation budgets you tried
- say whether the search eventually reaches `ShallowExhausted`, `ActivationCap`, `Success`, or
  another outcome once `--activations` is raised
- summarize which rules or clause families dominate the shallow activations

If the human agrees it is the right repro, turn any single positive `verify_succeeds` case into an
mdtest under `src/tests/prover/mdtest`.

## mdtest

Keep mdtests readable on GitHub:

- headings define case names
- each fenced `acorn` or `ac` block is a separate case
- add a little prose only when it clarifies what the proof is exercising

Run them with:

```bash
cargo test mdtests
```

Narrow to one fixture or heading with:

```bash
ACORN_MDTEST_FILTER=substring cargo test mdtests -- --nocapture
```

## Final Check

Before calling the reproduction done, make sure you can state clearly:

- what the minimal repro is
- why it still captures the original failure
- whether it is a `ShallowExplosion` repro or a `--shallow` `ShallowExhausted` repro
- whether it is ready to land as an mdtest after approval
