---
name: profile
description: Use when asked to profile Acorn prover or verifier performance, investigate where time is spent, or generate a top-down runtime breakdown from `perf` or `samply`.
---

# Profile

Use this skill when the user asks to profile the Acorn prover or verifier. The goal is a top-down summary that shows where sampled time is going.

## Scope

- Run all commands from the `acorn` repo root.
- Use this skill for profiling, performance-breakdown requests, and performance-sensitive changes
  that need release-mode timing baselines.
- If the target is not specified, ask whether to profile `profile_reprove` or `profile_check`.
- In sandboxed Codex runs, if `perf`, `cargo install samply`, or profile recording is blocked, request escalated permissions instead of working around it.
- After every successful profiling run, update `PROFILE.md` in the repo root.

## CLI semantics for performance work

- `check` is the thorough correctness check for existing proofs. It verifies cached certificates
  without relying on prover search. Treat it as the CI/release correctness operation and the main
  benchmark for certificate-checking scalability.
- `verify` is the normal incremental Acorn-code workflow. It uses cache/hash skipping when possible
  and searches for missing proofs when necessary. Use it to measure edit-loop and no-change
  incremental performance.
- `reprove` bypasses cached proofs and forces prover search. Use it only for testing prover behavior
  or measuring prover/search performance.

## Release-mode timing baselines

When evaluating performance-sensitive changes, first build in release mode:

```bash
cargo build --profile release
```

Then time the relevant CLI path:

```bash
time cargo run --profile release -- check
time cargo run --profile release -- verify
time cargo run --profile release -- reprove real.double_sum
```

Interpret these separately:

- `check` measures full existing-proof correctness throughput.
- `verify` measures incremental loading, manifest/hash skipping, and any necessary missing-proof search.
- `reprove real.double_sum` measures prover behavior on a representative search workload.

This is especially important after changes to core term or proof-search data structures, such as
`Term`, `EqualityGraph`, `Pdt`, or `FingerprintX`.

## Scaling notes

When discussing how performance scales as acornlib grows, separate these workloads:

- Existing-proof correctness: `check` should be evaluated as a full-library, certificate-checking
  workload. Track total certificates, certificates per second, and time spent loading/elaborating
  versus checking certificates.
- Incremental development: `verify` should be evaluated for no-change and small-change runs. Track
  modules skipped by manifest hash, cache loading time, dependency/hash walking cost, and any proof
  searches triggered by edits.
- Prover behavior: `reprove` should be evaluated by search success rate, timeout count, average and
  p95 search time, activation counts, and imported/visible fact counts per goal. A larger library can
  make individual goals harder if relevance filtering admits too many facts.

## Guardrail: abort on certificate-check failures

If a profiling run fails because certificate checking fails, the run is not a valid performance baseline.

When that happens:

- stop immediately
- tell the user the failing target and error
- do not continue profiling other targets in the same batch
- do not update `PROFILE.md`
- do not summarize the failed run as if it were a meaningful regression datapoint

## Available profiling targets

- `profile_reprove`: reprove `real.double_sum`, a representative prover/search workload
- `profile_check`: check-mode workload for existing cached certificates

## Recording results in `PROFILE.md`

`PROFILE.md` is the persistent record of the latest successful profiling baseline for each profiling target. Keep it updated after every successful profiling run.

The file should have a separate section for each profile script:

- `profile_reprove`
- `profile_check`

When you profile one target successfully, update that target's section with the latest run instead of leaving stale data in place.

Each section should include at least:

- date of the run
- git hash
- profile target and exact command used
- machine summary such as hostname, OS, CPU, and memory if easy to obtain
- wall-clock timing or other high-level runtime numbers gathered during the run
- a brief top-down performance summary
- the main breakdown or hottest components worth comparing later for regressions

## Platform detection

Check the platform first:

```bash
uname -s
```

- Linux: use the `perf` workflow
- Darwin: use the `samply` workflow

## Linux: `perf` workflow

### Build with frame pointers

Frame pointers are required for accurate call-graph profiling. Replace `TARGET` with `reprove` or `check`.

```bash
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_TARGET --profile=fastdev
```

### Record profile with `perf`

```bash
rm -f perf.data
perf record -g --call-graph fp -o perf.data target/fastdev/profile_TARGET
```

Exit code `1` can be expected; the profiled program may exit with an error.

### Generate top-down report

Inclusive-time breakdown:

```bash
perf report -i perf.data --stdio --percent-limit 0.5 2>&1 | grep -A 2000 "Samples: [0-9]*K" | head -300
```

Self-time breakdown:

```bash
perf report -i perf.data --stdio --no-children --percent-limit 0.3 2>&1 | grep -A 500 "Samples: [0-9]*K" | grep -E '^\s+[0-9]+\.[0-9]+%' | head -50
```

## macOS: `samply` workflow

### Prerequisite

Install `samply` once:

```bash
cargo install samply
```

### Build profiling binary

Replace `TARGET` with `reprove` or `check`.

```bash
cargo build --bin=profile_TARGET --profile=fastdev
```

### Record profile with `samply`

```bash
rm -f profile.json.gz profile.json.syms.json
samply record --save-only --unstable-presymbolicate -o profile.json.gz target/fastdev/profile_TARGET
```

This saves the profile as JSON without opening a browser. `--unstable-presymbolicate` also writes the `.syms.json` file needed for symbol resolution.

### Generate top-down report

```bash
python3 .agents/skills/profile/scripts/analyze_profile_topdown.py profile.json.gz
```

The script produces a top-down call tree and automatically uses the adjacent `.syms.json` file when present.

## Output format

Always present a top-down tree showing logical phases.

The tree should:

- start from the top-level function, for example `Verifier::run`
- show direct children with their percentage of total time
- drill into any component that is at least 10% of total time
- use indentation to show call hierarchy clearly

### Example for `profile_check`

```text
Top-Down Breakdown
============================================================

├──  93%  Verifier::run
│   └──  88%  Builder::build
│       └──  88%  Builder::verify_module
│           ├──  74%  Builder::verify_node
│           │   ├──  37%  verify_goal
│           │   │   └──  36%  Processor::check_cert
│           │   │       ├──  23%  Checker::check_cert
│           │   │       │   └──  14%  Certificate::to_concrete_proof
│           │   │       │       └──   8%  cloning
│           │   │       └──  10%  cloning
│           │   ├──  19%  Rc::make_mut
│           │   │   └──  19%  cloning
│           │   ├──  11%  Processor::add_fact
│           │   │   └──   7%  Checker::insert_clause
│           │   └──   7%  Rc::drop_slow
│           └──  13%  Processor::add_fact
└──   7%  Verifier::new
```

This should make the main costs obvious at each level, such as certificate checking, copy-on-write overhead, or fact insertion.

## Reporting guidelines

1. Always produce a top-down tree first.
2. Show any component that is at least 5% of total time.
3. Drill down into any component that is at least 10% of total time.
4. Keep the hierarchy readable; the point is to show where time goes, not dump raw profiler output.
5. After the tree, add a brief summary of the main takeaways.

## Bundled analysis scripts

- `scripts/analyze_profile_topdown.py`: primary output format for `samply` profiles
- `scripts/analyze_profile.py`: flat self-time and inclusive-time lists

## `profile_reprove` phase hints

For `profile_reprove`, common prover phases include:

- `PassiveSet::simplify`: subsumption checks
- `PassiveSet::push_batch`: adding clauses and building the fingerprint index
- `ActiveSet::activate`: generating inferences such as resolution and rewriting
- `ActiveSet::simplify`: forward simplification
