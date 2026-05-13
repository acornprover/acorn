# Profile Baselines

Keep this file updated with the most recent profiling result for each profiling target. Each section is the current baseline for that script, so replace stale data when a newer run is collected.

## profile_reprove

- Date:
- Git hash:
- Command:
- Machine:
- Timing:
- Summary:
- Breakdown:

## profile_verify

- Date: 2026-05-13
- Git hash: `bdbc9b47` plus local parallel verify cache-merge refactor
- Command: `/usr/bin/time -v target/release/profile_verify`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: full acornlib cached verify replay completed successfully in `0:32.06` wall with `548.19s` user time, `13.50s` system time, `1751%` CPU, and `4,950,528 KB` max RSS (`4.72 GiB`). The run rebuilt `356` modules, checked `64,140` cached certificates, performed `0` searches, and reported `64,140/64,140 OK`. A matching CLI timing sample, `/usr/bin/time -v target/release/acorn verify --ignore-hash --read-only --jobs 20 --timing`, reported `30.457s` measured time: `9.462s` target/module load, `30.213s` verification/search, and `61.701s` summed cached cert checks. The CLI sample peaked at `4,994,252 KB` max RSS (`4.76 GiB`) and `1806%` CPU.
- Summary: This baseline includes parallel verify processing with per-worker build-cache deltas merged back into the parent build cache. Compared with the previous sequential cached replay baseline (`3:10.77` wall, `190.575s` measured, `1,921,876 KB` max RSS, `99%` CPU), wall time is down `158.71s` (`83.2%`) on `profile_verify`, CLI measured time is down `160.118s` (`84.0%`), and CPU utilization rises from about one core to about eighteen cores. Peak RSS increases by about `3,028,652 KB` (`157.6%`) for `profile_verify`, which is the main tradeoff. For comparison, the no-change hash-skipping command `/usr/bin/time -v target/release/acorn verify --read-only --jobs 20 --timing` reported `5.080s` measured time, `4.816s` target/module load, `4.854s` verification/search, `356/356` modules cached, `2,128,884 KB` max RSS (`2.03 GiB`), and `0:05.35` wall at `466%` CPU.
- Breakdown:

```text
Current Verify Ignore-Hash Baseline (2026-05-13, parallel verify cache merge)
=============================================================================

profile command: /usr/bin/time -v target/release/profile_verify
profile result: 356 modules rebuilt, 64,140/64,140 certificates OK, 0 searches
profile max RSS: 4,950,528 KB = 4.72 GiB
profile wall clock: 0:32.06
profile user time: 548.19s
profile system time: 13.50s
profile CPU: 1751%

timing command: /usr/bin/time -v target/release/acorn verify --ignore-hash --read-only --jobs 20 --timing
timing result: 356 modules rebuilt, 64,140/64,140 certificates OK, 0 searches
timing max RSS: 4,994,252 KB = 4.76 GiB
total measured: 30.457s
wall clock: 0:30.75
user time: 546.16s
system time: 9.39s
CPU: 1806%
project setup: 17.5ms
cache load: 17.5ms
target/module load: 9.462s
build loading phase: 0.0ms
verification/search: 30.213s
cached cert checks: 61.701s summed worker time

No-change verify comparison:
├── command: /usr/bin/time -v target/release/acorn verify --read-only --jobs 20 --timing
├── result: 356/356 modules cached, 64,140 certificates cached, 0 searches
├── max RSS: 2,128,884 KB = 2.03 GiB
├── total measured: 5.080s
├── wall clock: 0:05.35
├── target/module load: 4.816s
└── verification/search: 4.854s

Slowest rebuilt modules by total processing time:
├── set_lattice: 17.264s total, 1.685s cert time
├── set: 15.221s total, 2.104s cert time
├── function_product_algebra: 13.373s total, 3.654s cert time
├── finite_group: 13.365s total, 254.4ms cert time
└── quotient_algebra: 12.387s total, 1.221s cert time
```

## profile_check

- Date: 2026-05-12
- Git hash: `822de623` plus local parallel dependency-DAG loader refactor
- Command: `/usr/bin/time -v target/release/acorn check --jobs 20 --timing`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: full acornlib check completed successfully with `11.547s` measured time: `7.183s` target/module load, `11.316s` certificate checking, and `31.815s` inside cached certificate checks. The run verified `361` modules, checked `64,140` cached certificates, performed `0` searches, elaborated `7` pending goals in `5` modules, and peaked at `3,713,600 KB` max RSS (`3.54 GiB`). `/usr/bin/time` reported `0:11.81` wall, `158.04s` user, `1.55s` system, and `1351%` CPU.
- Summary: This baseline includes the parallel dependency-DAG loader refactor: batch/all-target check parses dependencies, schedules module elaboration/lowering when imports have completed, feeds completed lowered modules into the existing checker pipeline with backpressure, and uses a smaller checker work queue. Loader parallelism is capped at `jobs / 4` while checker parallelism still uses `--jobs`. Compared with the previous cache-prioritized streaming baseline (`0:25.04` wall, `24.821s` measured, `2,523,708 KB` max RSS), wall time is down `13.23s` (`52.8%`), measured time is down `13.274s` (`53.5%`), CPU utilization is up from `476%` to `1351%`, and peak RSS is up `1,189,892 KB` (`47.1%`). A faster sample with the same settings reported `0:10.94` wall and `3,772,956 KB` max RSS; this entry records the more conservative warm rerun.
- Breakdown:

```text
Current Full Check Baseline (2026-05-12, parallel dependency-DAG loader refactor)
================================================================================

command: /usr/bin/time -v target/release/acorn check --jobs 20 --timing
result: 361 modules, 64,140/64,140 certificates OK, 0 searches
max RSS: 3,713,600 KB = 3.54 GiB
total measured: 11.547s
wall clock: 0:11.81
user time: 158.04s
system time: 1.55s
CPU: 1351%
project setup: 25.5ms
cache load: 25.4ms
target/module load: 7.183s
build loading phase: 0.0ms
certificate checking: 11.316s
cached cert checks: 31.815s
certificate throughput: 5668 certs/s

Overlapped timing measurements:
├── target/module load: 7.183s / 11.547s = 62.2%
└── processing/checking: 11.316s / 11.547s = 98.0%
    └── cached cert check calls: 31.815s / 11.547s = 275.5% summed worker time

Slowest rebuilt modules by total processing time:
├── function_product_algebra: 7.992s total, 2.050s cert time
├── finite_group: 6.170s total, 111.7ms cert time
├── top100.theorem_071_order_of_a_subgroup: 5.463s total, 187.7ms cert time
├── int.lattice: 3.113s total, 296.5ms cert time
└── set_lattice: 2.018s total, 823.0ms cert time

Perf top-down sample after the checker duplicate-expansion change (2026-05-11):
├── command: perf record -g --call-graph fp -o perf.data target/fastdev/profile_check
├── samples: 414,152; perf.data 109.2 MB
├── dominant path: Verifier::run -> Builder::process_module_work_batch -> Builder::verify_lowered_module
├── roughly 53% of the captured top-down path was Processor::add_imports_from_bindings
├── roughly 46% of the captured path was Checker::insert_clause_internal under imported facts
└── hot self-time was allocator/memmove/term ownership, normalization, hashing, and equality-graph cloning

Interval CPU sample for full check (2026-05-11):
├── command: target/release/acorn check --jobs 20 --timing, sampled with `pidstat -h -u -p $pid 1 1`
├── one-second `%CPU` samples: 133, 101, 1025, 351, 261, 279, 733, 886, 292, 650, 351, 657, 537, 483, 376, 667, 332, 575, 335, 481, 363, 106, 100
├── peak observed interval: 1025% = about 10.25 cores
├── median observed interval: 363% = about 3.63 cores
└── conclusion: the run does not saturate the 20 logical CPUs even in the middle; workers are frequently starved by the single-threaded load/lowering pipeline and by module-sized scheduling granularity

Comparison to older pre-LoweredModule baseline:
├── previous max rss: 9,721,212 KB = 9.27 GiB
├── current max rss: 2,477,768 KB = 2.36 GiB
└── RSS delta: -7,243,444 KB = -6.91 GiB (-74.5%)

Historical Page-Fault Top-Down Breakdown (2026-05-05, not rerun)
============================================================

99.1%  acorn main
└── 86.6%  Verifier::new_for_check / Verifier::new_inner
    └── 81.2%  Project::add_src_targets
        └── 81.1%  Project::load_module
            ├── 35.6%  Environment::add_statement
            │   ├── 16.7%  Block::new
            │   ├──  8.4%  recursive Project::load_module_by_name
            │   ├──  3.1%  BindingMap::add_unqualified_constant
            │   └──  cloning / im::HashMap insertion / AcornValue and AcornType allocation
            └──  ~3.5%  Environment::run_lowering_pass and lower_nodes_pass
                ├── lower_fact / lower_goal
                ├── SymbolTable::merge_imports
                └── KernelContext / SymbolTable / TypeStore persistent structure updates

Secondary page-fault paths during Builder::build:
├── Processor::add_imports_from_bindings / add_lowered_fact
├── Checker::insert_clause_internal
└── Processor::check_cert_with_usage cloning Checker / EqualityGraph

Retained Heap Diagnostic (2026-05-07)
============================================================

rss after full check-style load: 8.24 GiB (8.24 GiB HWM)

retained object counts:
├── 272 modules, 23,855 environments, 116,306 nodes
├── 140,161 binding snapshots with 56,433,464 summed binding entries
├── 128,923 module/node lowered facts containing 128,506 proof steps
├── 49,599 lowered goals containing 53,167 proof steps
├── 272 environment kernel contexts
├── 178,522 lowered kernel contexts
└── 0 token infos and 0 line entries

destructive clear sequence, order-sensitive but useful for retained buckets:
├── clear node/module lowered facts: -1.22 GiB
├── clear environment kernel contexts: -542.5 MiB
├── clear binding snapshots: -18.4 MiB RSS after prior clears
├── clear current bindings: -123.4 MiB
├── clear token/line maps: 0 B
├── clear node payloads: -2.23 GiB
└── clear remaining nodes / block environment tree: -3.68 GiB

largest retained local-lowered-fact modules:
├── set_lattice: 7,977 steps / 7,984 facts
├── set: 5,587 steps / 5,587 facts
├── relation_transport: 4,029 steps / 4,031 facts
├── order: 3,772 steps / 3,795 facts
└── order_iso: 3,396 steps / 3,396 facts

largest-module incremental load estimate:
├── target: `set_lattice`, the largest module by retained local lowered facts and binding snapshots
├── `set_lattice` dependency closure without `set_lattice`: 39 loaded envs, `1,858,652 KB` max RSS (`1.77 GiB`)
├── `set_lattice` target closure: 40 loaded envs, `2,922,128 KB` max RSS (`2.79 GiB`)
└── incremental max-RSS delta for `set_lattice` itself: `1,063,476 KB` (`1.01 GiB`)

Heaptrack representative module load (2026-05-07):
├── target: `order`, loaded with a temporary system-allocator profiling binary using check-mode load and no cache read/write
├── normal system-allocator run: `0:00.64` wall, `438,292 KB` max RSS
├── heaptrack run: `6.65s` runtime, `15,908,937` allocation calls, `374.84M` peak heap, `543.65M` peak RSS including heaptrack overhead
├── overall peak allocation stacks were dominated by binding-map/environment state:
│   ├── `62.23M` peak through `Arc::make_mut` / `im::nodes::hamt::Node::insert` under `BindingMap::add_constant_def` and `BindingMap::mark_as_theorem`
│   └── `43.01M` peak through `RawVec::finish_grow`, including environment node vectors and lowering/proof-step vectors
└── `KernelContext`-filtered peak stacks were smaller and mostly symbol-table mutation during lowering:
    ├── `12.21M` peak through `Arc::make_mut`, chiefly `SymbolTable::add_constant` from `register_value_symbols` while lowering facts
    └── `10.20M` peak through `RawVec::finish_grow`, chiefly `lower_fact` / clause normalization / proof-step construction
```
