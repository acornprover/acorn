---
name: reproduce-prover-failure
description: "Use when a theorem or goal ought to prove but the prover fails in acornlib or an issue repro. Classify whether the failure is a shallow explosion or a unit-test-reproducible prover bug, then narrow it to a minimal self-contained repro and, once approved, turn a single positive `verify_succeeds` case into an mdtest."
---

Use this when:

- acornlib verification fails on something that should prove
- an issue report needs to be narrowed to a real prover repro
- the immediate job is to reproduce and minimize the failure, not to fix prover internals yet

This skill is for the `acorn` repo. Use `cargo run`, not the installed `acorn` binary.
Keep scratch work in `/tmp` or a scratch project. Do **not** edit the bundled library under
`vscode/extension/acornlib`.

## Key Principle

In unit tests, `verify_succeeds` only accepts shallow success.
If shallow search fails, the helper may print a deep follow-up proof, but the test still fails.

Whether a proof is shallow is deterministic and does not change just because a lot of unrelated
context exists around it.

So if an acornlib failure is **not** a shallow explosion, it should reduce to a red unit test.

## Classification

There are two cases:

1. `ShallowExplosion`
   This is usually not the kind of thing you can reproduce cleanly in a unit test.
   Once the evidence points here, stop narrowing and bring it to a human.
2. Ordinary prover failure
   Keep narrowing until you have a red repro.
   Do not accept "only fails in full acornlib" unless you have strong evidence that it is really
   a shallow explosion.

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

### 2. Get It Running In A Scratch Repro

If the bug is in acornlib, copy a generous slice of relevant context into `/tmp` or a scratch
module first.
If the bug comes from an issue, start from the reported snippet and add only what is missing.

The first scratch repro does **not** need to be minimal.
It only needs to fail in the same way.

### 3. Narrow Aggressively

Reduce the scratch repro a small step at a time.
After each reduction, rerun the smallest repro immediately.

Preferred simplifications:

- remove declarations that come after the failing goal
- remove imports, definitions, theorems, and datatypes that are not used
- replace complicated definitions with `axiom`
- replace supporting theorems that you still use with `axiom`
- inline only the constants and types needed to keep the goal meaningful
- remove proof text that is not required for the failure

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
- there is no obvious unused context left
- further deletions would change the shape of the bug rather than simplify it

If the reduced repro still fails shallowly, keep it.

If every reduced repro succeeds and only the large original context fails, treat that as evidence
of `ShallowExplosion` and bring it to a human instead of forcing a unit test.

## Handoff

Once you have a minimal repro:

- share the snippet with the human first
- say whether it looks like an ordinary prover bug or a shallow explosion
- explain what was replaced with axioms and what was removed

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
- whether it looks like `ShallowExplosion` or a normal prover bug
- whether it is ready to land as an mdtest after approval
