# Profile Baselines

Keep this file focused on current performance baselines. Historical rollout notes and old-format
migration comparisons belong in git history, not in the active profiling record.

## How To Read Check Performance

Track `check` in two modes:

- `--jobs 1`: best for total work and code-level profiling. Phase times are easy to interpret and
  mostly additive.
- `--jobs 20` or default jobs: best for user-visible wall time. This captures scheduling,
  dependency ordering, memory pressure, and the long-pole effect.

In parallel `check`, printed phase counters are not a simple sum of wall time. A 20-thread run can
report target/module load and certificate checking counters that are each close to total wall time,
because module loading and module work are overlapped in the streaming build path. Use the total
measured time and slowest-module table for wall-time interpretation.

## profile_check

### 2026-07-01 Current Full-Library Check Baseline

- Git hash: `63a25b984a10fa20cca9f630dee4c937decb6ba4` plus the working-tree
  profiling/performance changes from this pass.
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF; 20 logical CPUs; 31 GiB RAM
- Scope: full acornlib cached certificate check, `605` modules, `93,462/93,462` cached
  certificates OK, `0` searches.

Commands:

```bash
cargo build --profile release
/usr/bin/time -v target/release/acorn check --jobs 1 --timing
/usr/bin/time -v target/release/acorn check --jobs 20 --timing
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=acorn --profile=fastdev
perf record -e cycles:u -g --call-graph fp -o perf.data target/fastdev/acorn check --jobs 1 --timing
```

Single-thread timing:

```text
target/module load: 40.793s
certificate checking: 60.327s
  cached cert checks: 35.779s
  other verification: 24.548s
total measured: 101.348s
certificate throughput: 1,549 certs/s
wall clock: 1:41.72
CPU: 100%
max RSS: 3.50 GiB
```

20-thread timing:

```text
target/module load counter: 10.370s
certificate checking counter: 11.889s
  cached cert checks: 59.308s summed worker time
total measured: 12.370s
certificate throughput: 7,861 certs/s
wall clock: 0:12.83
CPU: 1,224%
max RSS: 4.78 GiB
```

Slowest modules in the 20-thread wall-time run:

```text
int.lattice                         6.249s total, 4.157s cert time
function_product_algebra            4.614s total, 3.743s cert time
real.real_field                     2.542s total, 1.939s cert time
top100.theorem_071_order_of_a_subgroup
                                    2.458s total, 1.158s cert time
real.cauchy                         1.679s total, 1.186s cert time
set_lattice                         1.361s total, 1.019s cert time
submodule                           1.339s total, 1.048s cert time
set                                 1.244s total, 1.012s cert time
```

Single-thread perf summary from `cycles:u` sample:

```text
Verifier::run                                      99.9% children
├── Builder::process_module_work_batch             60.9%
│   ├── Certificate::check_usage_only              32.7%
│   │   ├── TraceChecker::check_step               31.5%
│   │   ├── TraceChecker::parse_required_claim...  19.9%
│   │   ├── Certificate::parse_code_line           18.6%
│   │   └── Checker::insert_clause_internal        18.5%
│   └── Processor::with_imports_for_checking       12.9%
└── Project::load_target_by_descriptor             38.5%
    └── module_loader::elaborate_and_lower_module  29.8%
```

Perf children percentages overlap because callers include callees. The main point is the shape:
single-thread check is split between verification and load/lower, and certificate replay is now
spread across claim parsing/lowering plus checker insertion/direct checking.

Hot self-time is broad rather than a single smoking gun:

```text
allocator work: _mi_page_malloc 11.37%, mi_free 7.16%, mi_heap_collect_ex 3.11%
copying: memmove 5.63%, Vec/AcornType/AcornValue clones spread across several symbols
term operations: TermRef::split_application_multi 2.45%, decompose 2.25%, Term::apply 1.04%
hashing/maps: DefaultHasher::write 2.65%, Hash::hash_slice 1.02%, im/hashbrown operations
syntax/loading: Token::scan_with_start_line 1.49%, Expression::parse 1.41%
normalization: split_symbol_application 1.67%, normalize_clause_term_with_polarity under callers
```

Current interpretation:

- Single-thread `check` is now about `40%` target/module load and `60%` verification. This is the
  best mode for understanding total work.
- Multi-thread `check` is the right user-visible benchmark. It now uses about `12` cores on average,
  and wall time is dominated by streaming load/check overlap plus the slowest modules.
- Certificate replay is no longer dominated by eager boolean-reduction expansion. Current replay
  cost is mostly parsing Acorn-readable trace claims, normalizing/lowering them, inserting them into
  the trace checker, and direct checker work.
- The slowest modules are a real long-pole limit: module-level parallelism cannot split
  `int.lattice` or `function_product_algebra` across workers.

Changes retained in this pass:

- Cached check no longer materializes display-oriented `CertificateLine`s. In isolation this moved
  single-thread total time from `135.325s` to `128.156s`, and cached cert replay from `42.472s` to
  `35.919s`.
- Streaming full-library check now passes a precomputed expanded target descriptor set into
  `take_lowered_modules_for_target_set`. This removes repeated target/dependency-closure rebuilding
  during load/check streaming. In isolation after the line-materialization change, single-thread
  target/module load moved from `67.403s` to `40.793s`, and 20-thread wall time moved from about
  `29.76s` to about `12.83s`.

Experiments reverted:

- A shared check-import processor cache reduced single-thread total time only slightly
  (`128.156s` to `126.444s`) while raising max RSS to `7.30 GiB` single-thread and `7.89 GiB`
  parallel. Parallel wall time did not improve.
- Increasing full-library loader workers from `jobs / 4` to `jobs / 2` reduced the load counter
  slightly but had no clear wall-time win and increased summed worker time and RSS.

Likely next performance work:

- Reduce trace replay parsing/normalization/direct-check costs. This is the main remaining
  verification-side bucket.
- Investigate whether very large modules can be split or scheduled more finely. Current parallel
  check is module-granular, so a few large modules set the wall-time floor.
- Look for more repeated load/elaboration bookkeeping now that the largest repeated target-set
  rebuild has been removed.

## profile_load

### 2026-07-01 Current Target Load Baseline

- Git hash: `63a25b984a10fa20cca9f630dee4c937decb6ba4` plus the working-tree
  profiling utility change from this pass.
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF; 20 logical CPUs; 31 GiB RAM
- Target: `real.double_sum`
- Mode: check-mode project loading (`UsageMode::Check`)

Commands:

```bash
cargo build --profile release --bin profile_load
/usr/bin/time -v target/release/profile_load
```

Timing:

```text
project setup: 59.7ms
  cache load: 58.9ms
target/dependency load: 8.367s
total measured: 8.426s
modules loaded: 596
targets: 117
wall clock: 0:08.75
CPU: 99%
max RSS: 3.55 GiB
```

Interpretation:

- Target/dependency load remains substantial on its own, even outside full-check streaming.
- `profile_load` does not exercise `take_lowered_modules_for_target_set` or certificate checking;
  use full `check --timing` for end-to-end streaming behavior.

## profile_verify

No current baseline collected in this pass. Refresh this section only when measuring edit-loop or
no-change `verify` performance.

## profile_reprove

No current baseline collected in this pass. Refresh this section only when measuring prover/search
performance.
