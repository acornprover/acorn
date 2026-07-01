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

## profile_load

### 2026-06-30 module-load profile

- Date: 2026-06-30
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local strict-BR/exact-BR migration diff
- Command:
  - `RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_load --profile=fastdev`
  - `target/fastdev/profile_load`
  - `perf record -g --call-graph fp -o perf.data target/fastdev/profile_load`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF, 20 logical CPUs, 31 GiB RAM
- Timing: `profile_load` loaded `real.double_sum` and dependencies without build/check/search. The timing run reported `8.722s` total measured, `8.686s` target/dependency load, `36.8ms` project setup, `36.1ms` cache load, `596` modules loaded, and `117` targets. The perf run reported `8.345s` total measured and `8.306s` target/dependency load.
- Perf sample: `8.662s` sampled duration, `25,932` samples, `0` lost. Intel hybrid CPU split events; the dominant `cpu_core` section had `25K` samples.
- Summary: isolated module loading does not show checker boolean-reduction expansion. `perf report` had no `Checker::`, `insert_boolean_reductions_with_reason`, or `find_boolean_reductions` symbols above `0.01%`. The load phase is dominated by recursive dependency loading, parse/elaborate/lower work, symbol/type import merging, and statement/block elaboration. The expensive boolean-reduction closure seen before exact-BR is in the builder verification phase (`Processor::with_imports_for_checking` while checking modules), not in pure module loading.
- Breakdown:

```text
profile_load: real.double_sum
=============================

├── 96.0%  Project::add_target_by_name
│   └── 96.0%  Project::load_build_descriptors
│       └── 95.4%  Project::load_module
│           ├── recursive dependency load_module calls
│           └── module_loader::elaborate_and_lower_module
│               ├── Environment::run_lowering_pass
│               │   ├── Environment::lower_nodes_pass
│               │   │   └── lowering facts/goals/propositions to clauses
│               │   ├── SymbolTable::merge_imports
│               │   └── TypeStore::merge
│               └── Environment::add_statement
│                   └── Block::new_with_local_obligations / add_conditional
└── no visible Checker boolean-reduction expansion

Hot self-time:
├── 6.9%  memmove
├── 4.8%  mi_free
├── 4.5%  AcornType::clone
├── 4.1%  _mi_page_malloc
├── 3.0%  clear_page_erms
└── 3.0%  mi_heap_malloc_aligned_at
```

## profile_check

### 2026-07-01 strict-br single-thread full-check profile

- Date: 2026-07-01
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local strict-br rollout diff
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Scope: full acornlib `check --jobs 1 --timing`, before/after timing plus `perf` samples. The preserved pre-strict baseline used `/tmp/acorn-check-baseline-target/release/acorn --lib /tmp/acorn-check-baseline/acornlib`; strict-BR used `/tmp/acorn-strict-br-migrate --lib /home/lacker/acornlib`. Both runs checked `93,462/93,462` cached certificates with `0` searches across `605` modules.
- Commands:
  - Timing: `/tmp/acorn-check-baseline-target/release/acorn --lib /tmp/acorn-check-baseline/acornlib check --jobs 1 --timing`
  - Timing: `/tmp/acorn-strict-br-migrate --lib /home/lacker/acornlib check --jobs 1 --timing`
  - Perf: `perf record -F 99 -g --call-graph dwarf,8192 -o /tmp/acorn-old-jobs1.perf.data /tmp/acorn-check-baseline-target/release/acorn --lib /tmp/acorn-check-baseline/acornlib check --jobs 1 --timing`
  - Perf: `perf record -F 99 -g --call-graph dwarf,8192 -o /tmp/acorn-new-jobs1.perf.data /tmp/acorn-strict-br-migrate --lib /home/lacker/acornlib check --jobs 1 --timing`
- Timing:
  - Old baseline: `201.471s` measured in the perf run (`201.565s` in the plain timing run), `69.452s` target/module load, `131.808s` certificate checking, `30.811s` cached cert checks, `100.998s` other verification, `709 certs/s`.
  - Strict-BR: `140.039s` measured in the perf run (`138.356s` in the plain timing run), `69.762s` target/module load, `70.030s` certificate checking, `43.495s` cached cert checks, `26.535s` other verification, `1,335 certs/s`.
  - Net: strict-BR is `61.432s` faster in the perf run (`30.5%` by measured time). Target/module load is effectively unchanged (`+0.310s`). Certificate-checking wall time drops by `61.778s`. Cached cert replay gets `12.684s` slower, but other verification drops by `74.463s`.
- Summary: Single-thread timing is much easier to interpret than the parallel wall-clock run. The speedup is entirely in the checking phase, not module loading. Before strict-BR, most check time was not the measured per-certificate replay; it was around-cert verification work, especially imported/local fact insertion with eager boolean-reduction closure. After strict-BR, that around-cert bucket is much smaller, while explicit trace replay is slower because the certs are larger and each trace step has more parsing/replay work.
- Breakdown:

```text
Single-thread full check
========================

Old baseline
├── total measured: 201.471s
├── target/module load: 69.452s
├── certificate checking: 131.808s
│   ├── cached cert checks: 30.811s
│   └── other verification: 100.998s
└── throughput: 709 certs/s

Strict-BR
├── total measured: 140.039s
├── target/module load: 69.762s
├── certificate checking: 70.030s
│   ├── cached cert checks: 43.495s
│   └── other verification: 26.535s
└── throughput: 1335 certs/s

Delta
├── target/module load: +0.310s
├── cached cert checks: +12.684s
├── other verification: -74.463s
└── total measured: -61.432s

Perf interpretation, qualitative because the preserved release binaries use DWARF unwinding:
├── old profile: Processor::with_imports_for_checking / add_exported_fact /
│   Checker::insert_clause_internal / insert_boolean_reductions_with_reason is the dominant
│   visible branch; Clause::find_boolean_reductions_with_locations_with_options appears at
│   about 12% inclusive.
├── new profile: eager boolean-reduction discovery is no longer a visible top branch; the
│   remaining major work is ordinary load/lowering, imported/local fact insertion, allocation,
│   and explicit trace replay.
└── explicit trace replay is slower after strict-BR, visible in the timer rather than as a
    single dominant symbol: it includes claim parsing, generic/specialized normalization,
    shallow trace insertion, and exact one-step BR checks.
```

### 2026-07-01 strict-br full-check timing recheck

- Date: 2026-07-01
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local strict-br rollout diff
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Scope: full acornlib `check --timing`, timing only, no perf sample. The preserved pre-strict baseline used `/tmp/acorn-check-baseline-target/release/acorn --lib /tmp/acorn-check-baseline/acornlib`; the migrated strict run used `/tmp/acorn-strict-br-migrate --lib /home/lacker/acornlib`. Both runs checked `93,462/93,462` cached certificates with `0` searches across `605` modules. The old cert corpus was `21,091,127` bytes; the migrated strict cert corpus is `43,424,816` bytes (`2.06x`).
- Timing:
  - Default worker count (`20` threads), three alternating old/new pairs:
    - Old baseline measured totals: `32.228s`, `32.542s`, `32.670s`; average `32.480s`.
    - Migrated strict measured totals: `29.187s`, `29.265s`, `28.966s`; average `29.139s`.
    - Old average breakdown: `30.272s` target/module load, `31.964s` certificate checking, `33.526s` summed cached cert checks, `2,924 certs/s`.
    - Migrated strict average breakdown: `28.224s` target/module load, `28.591s` certificate checking, `45.348s` summed cached cert checks, `3,269 certs/s`.
  - Four workers (`--jobs 4`), one pair: old baseline `42.992s` measured, `36.511s` target/module load, `42.371s` certificate checking, `28.960s` summed cached cert checks, `2,206 certs/s`. Migrated strict `43.332s` measured, `42.477s` target/module load, `42.784s` certificate checking, `41.906s` summed cached cert checks, `2,184 certs/s`.
- Summary: Full-check timing has large single-run variance; one old-baseline default-worker run measured `24.290s`, but the immediately following three alternating old/new pairs put old consistently around `32.5s` and migrated strict around `29.1s`. On the repeated default-worker comparison, strict-BR is about `3.341s` faster (`10.3%` by measured time), and wall-time certificate checking is about `3.373s` faster. However, summed cached cert replay is slower by about `35.3%` (`33.526s` to `45.348s`) because the explicit trace format is larger and more parse/replay-heavy. The apparent win comes from reducing around-cert/import/local checker work enough to offset the slower per-cert replay. With `--jobs 4`, one timing pair was essentially flat, so this should be treated as throughput-sensitive and noisy rather than a clean universal speedup.
- Breakdown:

```text
Full check, default workers
===========================

Old baseline
├── total measured avg: 32.480s
├── target/module load avg: 30.272s
├── certificate checking avg: 31.964s
├── cached cert checks, summed worker time avg: 33.526s
└── throughput avg: 2924 certs/s

Migrated strict-BR
├── total measured avg: 29.139s
├── target/module load avg: 28.224s
├── certificate checking avg: 28.591s
├── cached cert checks, summed worker time avg: 45.348s
└── throughput avg: 3269 certs/s

Full check, --jobs 4
====================

Old baseline
├── total measured: 42.992s
├── target/module load: 36.511s
├── certificate checking: 42.371s
├── cached cert checks, summed worker time: 28.960s
└── throughput: 2206 certs/s

Migrated strict-BR
├── total measured: 43.332s
├── target/module load: 42.477s
├── certificate checking: 42.784s
├── cached cert checks, summed worker time: 41.906s
└── throughput: 2184 certs/s
```

### 2026-06-30 exact-BR sample before/after profile

- Date: 2026-06-30
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local strict-BR/exact-BR migration diff
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF, 20 logical CPUs, 31 GiB RAM
- Scope: 10-target sample, not a full-library run. Baseline used `/tmp/acorn-default-fp --lib /home/lacker/acornlib`; exact-BR used `/tmp/acorn-strict-fp --lib /tmp/acornlib-exact-br-full`. The temp exact-BR library has 57 changed cert files from the sample migration.
- Targets: `affine_map`, `continuous_preimage`, `group_action_bijection`, `multiset`, `ring_ideal_hom_image`, `crypto.rsa`, `nat.base_b_extra`, `order_set.function_order_on`, `finite_group.base`, `top100.theorem_071_order_of_a_subgroup`.
- Timing commands: frame-pointer `fastdev` binaries, one `check --timing` per target.
- Perf commands:
  - `perf record -g --call-graph fp -o /tmp/acorn-before-exactbr-sample.perf.data bash -lc '<10-target baseline loop>'`
  - `perf record -g --call-graph fp -o /tmp/acorn-after-exactbr-sample.perf.data bash -lc '<10-target exact-BR loop>'`
- Timing:
  - Baseline sample: `8,081` certs, `28.186s` total measured, `21.746s` target/module load, `6.831s` certificate checking, `2.693s` summed cached cert checks, `4.710s` other verification.
  - Exact-BR sample: `8,081` certs, `24.109s` total measured, `21.391s` target/module load, `2.996s` certificate checking, `3.980s` summed cached cert checks, `0.521s` other verification.
  - Net: total measured improved `1.17x` (`14.5%` less wall time); certificate-checking wall time improved `2.28x`; other verification dropped `9.0x`; summed cached trace replay got `1.48x` slower.
- Perf sample:
  - Baseline: `30.207s` sampled duration, `128,193` samples, `0` lost.
  - Exact-BR: `26.034s` sampled duration, `95,990` samples, `0` lost.
  - Intel hybrid CPU split reports into `cpu_core` and `cpu_atom`; `cpu_core` had most samples (`122K` before, `93K` after).
- Summary: exact-BR removes the old eager boolean-reduction closure from the hot checker path. In the sample, `insert_boolean_reductions_with_reason` falls from a major branch (`~25%` of dominant `cpu_core` samples, `~68%` in the worker-heavy `cpu_atom` section) to about `0.04%`. The wall-time win is capped because this sample repeatedly loads/elaborates dependencies for ten separate target commands, so target/module load remains about `21s` both before and after. The new checker cost is explicit trace replay, especially parsing claim strings and accepting/inserting resulting clauses.
- Breakdown:

```text
Timing Breakdown
================

Before exact-BR, 10-target sample
├── total measured: 28.186s
├── target/module load: 21.746s
├── certificate checking: 6.831s
│   ├── cached cert checks, summed worker time: 2.693s
│   └── other verification: 4.710s
└── perf hot checker path:
    └── Processor::with_imports_for_checking
        └── Checker::insert_clause_internal
            └── insert_boolean_reductions_with_reason
                └── Clause::find_boolean_reductions_with_locations_with_options

After exact-BR, 10-target sample
├── total measured: 24.109s
├── target/module load: 21.391s
├── certificate checking: 2.996s
│   ├── cached cert checks, summed worker time: 3.980s
│   └── other verification: 0.521s
└── perf hot checker path:
    └── Processor::check_cert_with_usage
        └── ProofTrace::check_with_usage
            └── TraceChecker::check_step
                ├── parse_required_claim_with_generic
                │   └── Certificate::parse_code_line
                └── accept_clause_with_aliases
```

### 2026-06-30 strict-br migrated cert timing sanity check

- Date: 2026-06-30
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local strict-br rollout diff
- Command:
  - Strict-br: `cargo run --profile release --features strict-br -- --lib /home/lacker/acornlib check --timing`
  - Current migrated certs on default checker: `/usr/bin/time -f "elapsed=%e user=%U system=%S cpu=%P maxrss=%M" target/release/acorn --lib /home/lacker/acornlib check --timing`
  - Baseline: `/usr/bin/time -f "elapsed=%e user=%U system=%S cpu=%P maxrss=%M" /tmp/acorn-check-baseline-target/release/acorn --lib /tmp/acorn-check-baseline/acornlib check --timing`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Timing:
  - Strict-br with fully migrated certs: `29.113s` measured; `93,462/93,462` cached certs OK; `0` searches; throughput `3,272 certs/s`.
  - Current migrated certs on default checker: `31.132s`, `31.159s` measured; `31.58s`, `31.60s` wall; `93,462/93,462` cached certs OK; `0` searches; throughput about `3,052 certs/s`.
  - Old tracked code/certs baseline: `32.132s`, `32.096s` measured; `32.58s`, `32.53s` wall; `93,462/93,462` cached certs OK; `0` searches; throughput about `2,958 certs/s`.
- Summary: The fully migrated strict-br certs pass check and improve full `acorn check` by about `3.0s` versus the old tracked code/certs baseline, roughly `9.3%` by Acorn's measured time. An earlier failed strict-br run was caused by an incomplete rollout copy that only updated top-level `src/certs/*.jsonl` and left nested package certs such as `src/pair/certs/base.jsonl` in the old format. Once all `*/certs/*.jsonl` files were copied from the migrated temp tree, strict-br check succeeded.
- Breakdown:

```text
Timing-only comparison, not a perf sample:

Strict-br with fully migrated certs
├── total measured: 29.113s
├── target/module load: 28.200s
├── certificate checking: 28.564s
├── cached cert checks, summed worker time: 46.888s
└── throughput: 3272 certs/s

Current migrated certs on default checker
├── total measured: 31.132s, 31.159s
├── target/module load: 28.942s, 28.980s
├── certificate checking: 30.603s, 30.634s
├── cached cert checks, summed worker time: 34.193s, 33.610s
└── throughput: 3054 certs/s, 3051 certs/s

Old tracked code/certs baseline
├── total measured: 32.132s, 32.096s
├── target/module load: 29.958s, 29.935s
├── certificate checking: 31.604s, 31.585s
├── cached cert checks, summed worker time: 33.778s, 34.246s
└── throughput: 2957 certs/s, 2959 certs/s
```

Post-strict-br perf sample:

```text
Perf command:
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin acorn --profile=fastdev --features strict-br
perf record -g --call-graph fp -o /tmp/acorn-strict-br-check-perf.data \
    /home/lacker/acorn/target/fastdev/acorn --lib /home/lacker/acornlib check --timing

Result:
├── 93,462/93,462 certificates OK, 0 searches
├── total measured: 29.962s
├── target/module load: 29.009s
├── certificate checking: 29.413s
├── cached cert checks: 51.013s summed worker time
├── perf data: 482,590 samples, 0 lost
└── report note: Intel hybrid CPU produced cpu_core and cpu_atom sections;
    this summary uses the dominant cpu_core section, with 441K samples.

Top-down shape:
├── 77.9%  worker threads
│   ├── 50.6%  Builder::build_module_on_worker
│   │   └── 50.5%  Builder::verify_lowered_module
│   │       ├── 41.0%  Builder::verify_lowered_items
│   │       │   ├── 35.6%  Processor::check_cert_with_usage
│   │       │   │   └── 32.8%  ProofTrace::check_with_usage
│   │       │   │       └── 32.0%  TraceChecker::check_step
│   │       │   │           ├── 15.1%  TraceChecker::parse_required_claim_with_generic
│   │       │   │           │   └── 12.8%  Certificate::parse_code_line
│   │       │   │           ├──  9.5%  TraceChecker::accept_clause_with_aliases
│   │       │   │           │   └──  5.1%  Checker::insert_clause_for_trace
│   │       │   │           └──  1.1%  Clause::find_boolean_reductions_with_locations_with_options
│   │       │   └──  8.9%  Processor::with_imports_for_checking
│   │       │       └──  8.7%  Processor::add_exported_fact
│   │       │           └──  8.4%  Checker::insert_clause_internal
│   │       └── other local lowered item work
│   └── 25.9%  module_loader::elaborate_and_lower_module
└── remaining time: main-thread project/target walking, scheduling, filesystem metadata, and runtime overhead

Hot self-time:
├── 5.3%  _mi_page_malloc
├── 5.2%  __memmove_avx_unaligned_erms
├── 5.0%  mi_free
├── 3.1%  TermRef::split_application_multi
├── 2.6%  mi_heap_malloc_aligned_at
├── 2.3%  TermRef::decompose
├── 2.0%  SipHasher::write
├── 1.9%  filesystem/AppArmor stat path
├── 1.9%  AcornType::clone
└── 1.6%  split_symbol_application

Interpretation:
Strict-br removes the old import-time eager boolean-reduction closure from the hot path:
`insert_boolean_reductions_with_reason` is no longer a large visible branch, and explicit
boolean-reduction discovery/checking is around 1% of sampled CPU in this run. The dominant
post-strict-br checker cost is instead explicit trace replay, especially repeatedly parsing
claim strings from JSON and accepting/inserting the resulting clauses. This explains the tradeoff:
wall time improves because import/setup closure is gone, but summed certificate worker time rises
because the larger explicit trace format creates much more parse/replay work.
```

### 2026-06-17 certificate trace Full Check Profile

- Date: 2026-06-17
- Git hash: `a9bd149b` plus local `certificate_trace` feature diff
- Command: `cargo run --manifest-path /home/lacker/acorn/Cargo.toml --profile release --features certificate_trace -- check --timing` in `/tmp/acornlib-certificate_trace-test`, then `RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_check --profile=fastdev --features certificate_trace` and `perf record -g --call-graph fp -o /tmp/certificate_trace-check-perf.data /home/lacker/acorn/target/fastdev/profile_check`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: release certificate trace check completed successfully in `32.670s` measured time. It checked `93,462/93,462` cached certificates, performed `0` searches, printed `605` modules, and rebuilt `584` modules. The measured phases were `30.208s` target/module load, `32.160s` certificate checking, and `35.145s` summed cached certificate checks, for `2,906 certs/s`.
- Summary: certificate trace improves full-check wall time from the current non-certificate trace baseline of about `47.97s` to `32.67s`, but the profile explains why this is not a complete boolean-reduction win. certificate trace proof-step replay itself is no longer the dominant path. The remaining hot work is mostly pre-cert and around-cert checker setup: importing facts, inserting local lowered facts/goals, and still eagerly deriving boolean-reduction closure for those clauses. The observed low CPU utilization near the tail is consistent with the timing table: slow modules such as `int.lattice` spend most of their wall time outside summed cert replay (`9.204s` total vs. `210.7ms` cert time), so the long pole is module/import/setup work rather than all workers staying busy on independent cert checks.
- Breakdown:

```text
certificate trace Full Check Timing (2026-06-17)
==================================

release command: cargo run --manifest-path /home/lacker/acorn/Cargo.toml --profile release --features certificate_trace -- check --timing
result: 605 modules printed, 584 rebuilt, 93,462/93,462 certificates OK, 0 searches
total measured: 32.670s
target/module load: 30.208s
certificate checking: 32.160s
cached cert checks: 35.145s summed worker time
certificate throughput: 2,906 certs/s

Slowest rebuilt modules by total processing time:
| module                              | total  | cert time |
|-------------------------------------|--------|-----------|
| int.lattice                         | 9.204s | 210.7ms   |
| function_product_algebra            | 6.200s | 1.664s    |
| top100.theorem_071_order_of_a_subgroup | 3.961s | 168.5ms |
| finite_group.base                   | 2.292s | 125.7ms   |
| set_lattice                         | 1.871s | 811.3ms   |

Fastdev perf command: perf record -g --call-graph fp -o /tmp/certificate_trace-check-perf.data /home/lacker/acorn/target/fastdev/profile_check
perf sample: 887,109 cpu_core samples over 221.799s, 236.7 MB perf.data, 0 lost samples

Top-down perf shape:
Verifier::run                                         99.9%
  Builder::process_module_work_batch                  67.7%
    Builder::verify_lowered_module                    67.2%
      Processor::with_imports_for_checking            34.1%
        add_imported_module / add_exported_fact       33.9%
          Checker::insert_clause_internal             33.7%
            insert_boolean_reductions_with_reason     26.2%
      Builder::verify_lowered_items                   32.1%
        local fact, goal, and certificate setup
        certificate trace cert replay proper is much smaller
  Project::load_target_by_descriptor                  16-20%
  BuildCache::load                                     6-7%

Hot self-time:
TermRef::split_application_multi                       7.22%
_mi_page_malloc                                        6.92%
mi_free                                                5.61%
TermRef::to_owned                                      4.88%
__memmove_avx_unaligned_erms                           4.22%
TermRef::decompose                                     3.25%
DefaultHasher::write                                   3.09%
term_normalization::split_symbol_application           2.99%

Interpretation:
certificate trace removed a major source of eager boolean-reduction work from certificate proof-step replay,
but it did not remove eager boolean-reduction closure from checker setup. Imported exported facts,
local lowered facts, and goal insertion still flow through `Checker::insert_clause_internal` and
`insert_boolean_reductions_with_reason`. The next performance target is therefore not the certificate trace
step checker itself; it is changing how the checker represents imported/local/goal facts so check
mode does not eagerly generate broad boolean-reduction closure for facts the proof never uses.
```

### 2026-06-17 Current Full Check Profile

- Date: 2026-06-17
- Git hash: `6ee1e22cdafc97c16f6d1be98e74106ebfcaf5fa`
- Command: `RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_check --profile=fastdev`, then `perf record -g --call-graph fp -o perf.data target/fastdev/profile_check`. For user-facing timing, also ran `/usr/bin/time -f "elapsed=%e user=%U system=%S cpu=%P maxrss=%M" target/release/acorn check --timing`.
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: release `acorn check --timing` completed successfully in `47.97s` wall with `561.50s` user time, `29.03s` system time, `1230%` CPU, and `5,085,744 KB` max RSS (`4.85 GiB`). It checked `93,462/93,462` cached certificates, performed `0` searches, printed `605` modules, and rebuilt `584` modules. The measured timing was `47.454s`: `40.956s` target/module load, `46.947s` certificate checking, and `368.910s` summed cached cert checks. The `fastdev` perf run checked the same `93,462` certificates; the perf capture sampled `461.848s`, wrote a `517 MB` `perf.data`, collected about `1.85M` samples, and reported `0` lost samples.
- Summary: The check corpus is essentially the same size as the June 15 baseline, and release throughput remains about `1,991 certs/s`. Wall time is still dominated by two overlapped phases: target/module loading is `86.3%` of wall time, and certificate checking is `98.9%` of wall time. The perf shape is again checker-heavy, with the hot path inside `Checker::insert_clause_internal -> insert_boolean_reductions_with_reason`. The main cost under that path is not a specific theorem lookup; it is repeatedly enumerating boolean reductions, normalizing the candidate traces, splitting applications, type-checking/simplifying boolean terms, and allocating intermediate terms/clauses.
- Breakdown:

```text
Current Full Check Timing (2026-06-17)
======================================

release command: /usr/bin/time -f "elapsed=%e user=%U system=%S cpu=%P maxrss=%M" target/release/acorn check --timing
result: 605 modules printed, 584 rebuilt, 93,462/93,462 certificates OK, 0 searches
max RSS: 5,085,744 KB = 4.85 GiB
wall clock: 47.97s
user time: 561.50s
system time: 29.03s
CPU: 1230%
project setup: 32.0ms
cache load: 29.5ms
target/module load: 40.956s
build loading phase: 0.0ms
certificate checking: 46.947s
cached cert checks: 368.910s summed worker time
certificate throughput: 1991 certs/s

Slowest rebuilt modules by total processing time:
├── set_lattice: 27.516s total, 26.403s cert time
├── set: 18.372s total, 17.565s cert time
├── topological_space: 17.830s total, 17.034s cert time
├── submodule: 13.297s total, 12.341s cert time
├── int.lattice: 11.932s total, 344.1ms cert time
├── function_product_units: 11.905s total, 10.250s cert time
├── function_product_algebra: 11.338s total, 3.186s cert time
├── subring: 9.358s total, 8.871s cert time
├── simple_graph: 8.539s total, 7.855s cert time
├── ideal: 8.161s total, 7.679s cert time
├── top100.theorem_071_order_of_a_subgroup: 7.901s total, 3.590s cert time
└── measurable_space: 7.890s total, 7.479s cert time

Fastdev perf command: perf record -g --call-graph fp -o perf.data target/fastdev/profile_check
perf sample: 1.85M samples over 461.848s, 517 MB perf.data, 0 lost samples

Top-down perf shape:
├── 92.8%  Builder::process_module_work_batch
│   └── 92.8%  Builder::verify_lowered_module
│       └── 68.4%  Builder::verify_lowered_items
│           └── 41.0%  Builder::verify_goal
│               └── 41.0%  Processor::check_cert_with_usage
│                   └── 41.0%  Certificate::check_with_usage
│                       └── 41.0%  Checker::check_cert_steps
│                           └── 41.0%  Checker::insert_clause
│                               └── 41.0%  Checker::insert_clause_internal
│                                   └── 41.0%  Checker::insert_boolean_reductions_with_reason
│                                       ├── 23.6%  Clause::find_boolean_reductions_with_locations_with_options
│                                       │   ├── 7.9%  Clause::normalize_boolean_reduction
│                                       │   │   └── 6.9%  Clause::normalize_with_var_ids_prefilled
│                                       │   ├── 5.8%  Clause::with_replaced_literal_and_context
│                                       │   ├── 4.2%  TermRef::get_type_with_context
│                                       │   └── 2.7%  Clause::simplify_ite_term
│                                       └── 13.8%  Checker::normalize_checker_trace
│                                           └── 11.8%  Clause::normalize_with_var_ids_prefilled
│                                               └── 10.8%  normalize_signed_clause_term
└── hot self-time: TermRef::split_application_multi, normalize_clause_term_with_polarity,
    split_symbol_application, allocator/free traffic, memmove, term construction, and KBO sorting.

Deeper read of the verification subtree:
├── The visible 41.0% branch is not the total boolean-reduction cost; it is only the largest
│   recursive `verify_lowered_items -> verify_goal` branch.
├── The same 68.4% `verify_lowered_items` subtree also contains a separate 26.6% direct
│   `verify_goal` branch, including 19.2% more sampled time in
│   `insert_boolean_reductions_with_reason`.
└── Conservatively, at least about 60% of total sampled time, and roughly 88% of the visible
    verification subtree, is spent under boolean-reduction insertion/closure.

Interpretation:
├── Boolean reductions are still the right target. The checker spends a large visible share of
│   sampled time deriving the full boolean-reduction closure for inserted clauses.
├── The evidence is strong enough that check-mode boolean reductions should be handled differently:
│   the checker should not eagerly derive every possible boolean reduction when the certificate only
│   needs specific reductions.
├── A compact certificate hint that names the exact boolean reduction used by a proof step should
│   let check mode avoid enumerating and normalizing many unused candidate reductions.
└── The committed structured-proof scaffolding does not appear as an active check-mode path in
    this profile, but it is not the format direction we want if the goal is a small JSONL delta.

Targeted boolean-reduction kind probe:
├── Date: 2026-06-17
├── Method: temporary checker counters over five slow/representative check targets:
│   set_lattice, topological_space, set, function_product_units, and function_product_algebra.
│   Counters tracked candidate counts, per-kind checker-normalization time, insertions, and
│   post-normalization dedup skips.
├── Aggregate over those targets: 1,471,939 candidate reductions, 21.505s measured
│   checker-normalization time, 40,811 inserted reductions, and 1,430,670 dedup skips.
├── Per-kind normalization-time share:
│   boolean equality split 29.0%, function inequality to exists 26.8%,
│   positive conjunction split 15.3%, negative conjunction split 11.2%,
│   negated forall to exists 9.6%, positive forall open 4.9%, all other kinds 3.2%.
├── Per-kind candidate-count share:
│   boolean equality split 30.6%, positive conjunction split 30.2%,
│   negative conjunction split 14.0%, negated forall to exists 7.7%,
│   function inequality to exists 6.7%, positive forall open 5.5%, all other kinds 5.3%.
└── Interpretation: the broad problem is eager closure plus late dedup. The worst cluster is
    boolean equality/conjunction splitting by volume, while function inequality to exists is much
    more expensive per candidate and dominates product-algebra-style modules.

Early exact-dedup follow-up:
├── Change: before checker-normalizing a boolean-reduction trace, skip it if the trace clause is
│   already in `past_boolean_reductions`. This keeps the existing post-normalization dedup guard,
│   but avoids the expensive second-stage normalization for candidates that are already exact
│   known duplicates.
├── Targeted timings:
│   set_lattice cached cert time improved from 19.547s to 12.286s, with wall time from 22.69s
│   to 15.24s. set cached cert time improved from 11.851s to 7.575s, with wall time from
│   13.86s to 9.47s.
└── Full check timing: `target/release/acorn check --timing` completed in 42.36s wall, with
    238.795s summed cached cert checks. Compared with the 2026-06-17 baseline of 47.97s wall
    and 368.910s summed cached cert checks, this is about 11.7% faster wall-clock and 35.3%
    less summed certificate-checking time.

Post-dedup perf follow-up:
├── Date: 2026-06-17
├── Git hash: `e93559cf0c982e966f0b19c69fcd9c5840056ddb`
├── Command: `RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_check
│   --profile=fastdev`, then `perf record -g --call-graph fp -o perf.data
│   target/fastdev/profile_check`.
├── Result: 93,462/93,462 cached certificates OK, 0 searches. The perf capture covered
│   369.716s and wrote 407 MB with 1,478,838 samples and 0 lost samples.
├── Main `cpu_core/cycles/P` aggregate inclusive samples:
│   `Checker::insert_boolean_reductions_with_reason` 64.80%,
│   `Clause::find_boolean_reductions_with_locations_with_options` 47.32%,
│   `Clause::normalize_boolean_reduction` 22.59%, and
│   `Checker::normalize_checker_trace` 10.10%.
└── Interpretation: early exact dedup reduced absolute check time substantially, but the remaining
    workload is still dominated by boolean-reduction closure. The next performance gains probably
    need to avoid enumerating/checking broad closure candidates in the first place, not just dedup
    them earlier.

Processor-phase import replay census:
├── Date: 2026-06-17
├── Method: temporary `Processor` timers on `target/release/profile_check`, measuring summed worker
│   time for imported module export replay, local lowered fact insertion, and cached certificate
│   checking. This is a checker/proof-processing split after modules are lowered; it does not
│   include source parsing/lowering or build graph/module loading time.
├── Result: 93,462 cached certificates checked successfully with 0 searches.
├── Import behavior: imported facts are replayed into a fresh processor/checker for each checked
│   module that imports them. `Processor::add_imports_from_bindings` walks direct and transitive
│   dependencies, `add_check_export_fact` inserts each exported assumption, and checker insertion
│   runs normal boolean-reduction closure for those imported clauses. Imported modules are deduped
│   inside one processor, but not across independent module processors.
├── Exclusive processor-side measured time:
│   import replay 86.584s (30.36%), 24,301 imported-module replays, 2,318,469 exported facts;
│   cached cert checking 178.603s (62.63%), 93,462 cert checks;
│   local lowered fact insertion 19.966s (7.00%), 220,469 calls, 220,095 facts.
├── Local/cert work together was 198.570s (69.64%) of the same measured processor-side total.
├── `cert_goal_setup` was also measured as a subphase inside cert checking: 5.219s, 93,462 calls,
│   99,911 goal clauses. It is not added to the exclusive total above because it is already part of
│   cached cert checking.
└── Interpretation: import replay is a major but not majority component of checker-side work:
    about 30% of measured processor time. Since replaying imports triggers boolean-reduction closure
    on imported facts, avoiding or caching imported boolean-reduction closure is still a meaningful
    target, but the larger combined bucket remains per-goal/per-cert local checking.

Remaining possible improvement areas:
├── Reduce boolean-reduction closure cost. Recursive insert_clause_internal ->
│   insert_boolean_reductions_with_reason dominates the visible certificate-checking profile.
│   Explicit boolean-reduction hints are a good first migration because they target the dominant
│   cost without replacing the whole certificate format.
├── Avoid broader import replay cost. Check-mode module exports already store normalized
│   CheckExportFact clauses, but each module still constructs a fresh checker and replays the
│   transitive import facts. Earlier exact import-set and direct-dependency cache attempts did not
│   produce a clear wall-time win.
└── Improve scheduling granularity for large modules. The release run averages 12.2 CPUs, while
    modules like set_lattice, topological_space, set, and submodule dominate the tail. Per-module
    work stealing cannot fully use 20 logical CPUs when a few large modules sit on the critical path.
```

### 2026-05-14 SatisfyStep Checker Validation

- Date: 2026-05-14
- Git hash: `c8f0ec23` plus local `SatisfyStep` checker-payload validation changes
- Command: `RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_check --profile=fastdev`, then `/usr/bin/time -f elapsed=%e perf record -g --call-graph fp -o /tmp/acorn-satisfy-after.data target/fastdev/profile_check`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Timing: patched `profile_check` completed successfully in `286.52s` under `perf`, checking `66,544/66,544` cached certificates with `0` searches. The matched pre-change baseline from a detached `HEAD` worktree completed in `283.50s` under the same command shape and the same acornlib checkout. This is a `+3.02s` wall-time delta, about `+1.1%`.
- Summary: Revalidating `SatisfyStep` checker payloads before trusting embedded witness clauses does not show up as a material check-mode hotspot. In the patched perf sample, `SatisfyStep::validate_checker_payload` appears under the certificate-checking path at roughly `0.18%` inclusive in the sampled call graph, with direct self-time rounded to `0.00%`. The main profile shape is still dominated by clause insertion, boolean reductions, and term normalization.
- Breakdown:

```text
Before/after wall time under perf:
├── baseline HEAD: 283.50s, 66,544/66,544 certificates OK, 0 searches
├── patched tree: 286.52s, 66,544/66,544 certificates OK, 0 searches
└── delta: +3.02s = +1.1%

Patched profile_check top-down shape:
├── 99.95%  Verifier::run
│   └── 99.90%  Verifier::load_and_build_streaming
│       └── 91.83%  Builder::process_module_work_batch
│           └── 91.54%  Builder::verify_lowered_module
│               ├── 76.75%  Builder::verify_lowered_items
│               │   └── 67.23%  Builder::verify_goal
│               │       └── 67.18%  Processor::check_cert_with_usage
│               │           └── 65.72%  Certificate::check_with_usage
│               │               └── 62.72%  Checker::check_cert_steps
│               │                   ├── 68.14%  Checker::insert_clause
│               │                   └── ~0.18%  SatisfyStep::validate_checker_payload
│               └── 18.03%  Processor::add_imports_from_bindings
├── 84.20%  Checker::insert_clause_internal
├── 78.93%  Checker::insert_boolean_reductions_with_reason
├── 47.40%  Clause::normalize_with_var_ids_prefilled
├── 42.34%  Clause::find_boolean_reductions_with_kinds_with_options
└── 38.70%  normalize_clause_term_with_polarity

Hot direct self-time remains term splitting, term ownership, allocation/free,
memmove, normalization, and hashing. The new SatisfyStep validation path is
below the visible self-time threshold.
```

### 2026-05-12 Parallel Dependency-DAG Loader Baseline

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
