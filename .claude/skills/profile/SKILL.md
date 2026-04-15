---
description: Profile the prover and generate a top-down performance summary
triggers:
  - when the user asks to profile
  - when the user asks about performance
  - when the user wants to know where time is being spent
---

# Performance Profiling Workflow

Use this skill when the user asks to profile the Acorn prover. This generates a top-down summary showing where time is spent.

## Available profiling targets

- `profile_reprove` - Profiles reproving `real.double_sum` module (representative prover workload)
- `profile_check` - Profiles check mode

Ask the user which target to profile if not specified.

## Guardrail: abort on certificate-check failures

If a profiling run hits a certificate-check failure, stop immediately and report it.

- Do not continue to other profiling targets in the same batch.
- Do not update `PROFILE.md`.
- Do not treat the failed run as a usable performance baseline.

## Recording results in `PROFILE.md`

After every successful profiling run, update `PROFILE.md` in the repo root.

Keep one section per profile script:

- `profile_reprove`
- `profile_check`

For the target you just profiled successfully, replace stale results with the latest run details. Include the date, git hash, machine summary, exact command, runtime numbers, and a brief summary of the top-down breakdown so later runs can be compared for regressions.

## Platform detection

Check the platform first:
```bash
uname -s
```

- **Linux**: Use the perf workflow (below)
- **Darwin** (macOS): Use the samply workflow (further below)

---

# Linux: perf workflow

## Build with frame pointers

Frame pointers are required for accurate call graph profiling. Replace `TARGET` with `reprove` or `check`:

```bash
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_TARGET --profile=fastdev
```

## Record profile with perf

```bash
rm -f perf.data && perf record -g --call-graph fp -o perf.data target/fastdev/profile_TARGET
```

The exit code 1 is expected (the profiled program may exit with error).

## Generate top-down report

Get the inclusive time breakdown (with call graph):

```bash
perf report -i perf.data --stdio --percent-limit 0.5 2>&1 | grep -A 2000 "Samples: [0-9]*K" | head -300
```

Get self-time breakdown for the main event:

```bash
perf report -i perf.data --stdio --no-children --percent-limit 0.3 2>&1 | grep -A 500 "Samples: [0-9]*K" | grep -E '^\s+[0-9]+\.[0-9]+%' | head -50
```

---

# macOS: samply workflow

## Prerequisites

Install samply (one-time):
```bash
cargo install samply
```

## Build profiling binary

```bash
cargo build --bin=profile_TARGET --profile=fastdev
```

Replace `TARGET` with `reprove` or `check`.

## Record profile with samply

```bash
rm -f profile.json.gz profile.json.syms.json && samply record --save-only --unstable-presymbolicate -o profile.json.gz target/fastdev/profile_TARGET
```

This saves the profile to JSON without opening a browser. The `--unstable-presymbolicate` flag generates a `.syms.json` file with symbol information needed for name resolution.

## Generate top-down report

```bash
python3 .claude/skills/profile/analyze_profile_topdown.py profile.json.gz
```

This generates a top-down call tree showing where time is spent, automatically drilling down into any component >= 10%.

The script automatically uses the `.syms.json` file for symbol resolution.

---

## Output format

**Always present a top-down tree breakdown** showing what logical phases take time. The tree should:
- Start from the top-level function (e.g., `Verifier::run`)
- Show direct children with their percentage of total time
- Drill down into any component that is >= 10% of total
- Use indentation to show the call hierarchy

### Example output for `profile_check`:

```
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

This format makes it clear that:
- 37% of time is in `verify_goal` (certificate checking)
- 19% is `Rc::make_mut` (copy-on-write overhead)
- 11% is `add_fact` at the verify_node level
- The tree lines show the call hierarchy clearly

## Guidelines

1. **Always produce a top-down tree** - start from the root and drill down
2. Show any component >= 5% of total time
3. Drill down (show children) for any component >= 10%
4. The tree should make clear where time is going at each level
5. After the tree, you can add a brief summary of key insights

## Additional analysis scripts

- `analyze_profile.py` - Self-time and inclusive-time flat lists (useful for seeing which individual functions are hot)
- `analyze_profile_topdown.py` - Top-down tree breakdown (primary output format)

## Notes on reprove profiling

For `profile_reprove`, the main phases of the prover are:
- `PassiveSet::simplify` - checking if clauses are subsumed
- `PassiveSet::push_batch` - adding new clauses, building fingerprint index
- `ActiveSet::activate` - generating inferences (resolution, rewriting)
- `ActiveSet::simplify` - forward simplification
