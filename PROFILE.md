# Profile Baselines

Keep this file updated with the most recent profiling result for each profiling target. Each
section is the current baseline for that script, so replace stale data when a newer run is
collected. Rollout-era migration notes should stay in git history rather than accumulating here.

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
- Timing: full acornlib cached verify replay completed successfully in `0:32.06` wall with `548.19s` user time, `13.50s` system time, `1751%` CPU, and `4,950,528 KB` max RSS (`4.72 GiB`). A matching CLI timing sample, `/usr/bin/time -v target/release/acorn verify --ignore-hash --read-only --jobs 20 --timing`, reported `30.457s` measured time: `9.462s` target/module load, `30.213s` verification/search, and `61.701s` summed cached cert checks.
- Summary: parallel verify processing with per-worker build-cache deltas cut cached replay wall time by roughly `83%` versus the old sequential baseline (`3:10.77` wall). The tradeoff is peak RSS rising from about `1.83 GiB` to about `4.72 GiB`.
- Breakdown:

```text
profile_verify
==============

profile command: /usr/bin/time -v target/release/profile_verify
profile result: 356 modules rebuilt, 64,140/64,140 certificates OK, 0 searches
profile wall clock: 0:32.06
profile max RSS: 4.72 GiB

timing command: /usr/bin/time -v target/release/acorn verify --ignore-hash --read-only --jobs 20 --timing
total measured: 30.457s
target/module load: 9.462s
verification/search: 30.213s
cached cert checks: 61.701s summed worker time
```

## profile_load

### 2026-06-30 module-load profile

- Date: 2026-06-30
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local certificate-trace rollout diff
- Command:
  - `RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=profile_load --profile=fastdev`
  - `target/fastdev/profile_load`
  - `perf record -g --call-graph fp -o perf.data target/fastdev/profile_load`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF, 20 logical CPUs, 31 GiB RAM
- Timing: `profile_load` loaded `real.double_sum` and dependencies without build/check/search. The timing run reported `8.722s` total measured, `8.686s` target/dependency load, `36.8ms` project setup, `36.1ms` cache load, `596` modules loaded, and `117` targets.
- Summary: isolated module loading does not show checker boolean-reduction expansion. `perf report` had no `Checker::`, `insert_boolean_reductions_with_reason`, or `find_boolean_reductions` symbols above `0.01%`. The load phase is dominated by recursive dependency loading, parse/elaborate/lower work, symbol/type import merging, and statement/block elaboration.
- Breakdown:

```text
profile_load: real.double_sum
=============================

target/dependency load: 8.686s of 8.722s total

Dominant branch:
Project::add_target_by_name
└── Project::load_build_descriptors
    └── Project::load_module
        ├── recursive dependency load_module calls
        └── module_loader::elaborate_and_lower_module

Hot self-time:
memmove, mi_free, AcornType::clone, _mi_page_malloc, clear_page_erms
```

## profile_check

### 2026-07-01 certificate-trace single-thread full-check profile

- Date: 2026-07-01
- Git hash: `5e035ace2a39fcf1a65304404d6edb54f05a70bb` plus local certificate-trace rollout diff
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Scope: full acornlib `check --jobs 1 --timing`, before/after timing plus `perf` samples. Both runs checked `93,462/93,462` cached certificates with `0` searches across `605` modules.
- Timing:
  - Pre-trace baseline: `201.471s` measured in the perf run (`201.565s` in the plain timing run), `69.452s` target/module load, `131.808s` certificate checking, `30.811s` cached cert checks, `100.998s` other verification, `709 certs/s`.
  - Certificate trace: `140.039s` measured in the perf run (`138.356s` in the plain timing run), `69.762s` target/module load, `70.030s` certificate checking, `43.495s` cached cert checks, `26.535s` other verification, `1,335 certs/s`.
  - Net: certificate trace is `61.432s` faster in the perf run (`30.5%` by measured time). Target/module load is effectively unchanged (`+0.310s`). Certificate-checking wall time drops by `61.778s`. Cached cert replay gets `12.684s` slower, but other verification drops by `74.463s`.
- Summary: single-thread timing is much easier to interpret than the parallel wall-clock run. The speedup is entirely in the checking phase, not module loading. Before the current certificate-trace format, most check time was around-cert verification work, especially imported/local fact insertion with eager boolean-reduction closure. After the trace rollout, that around-cert bucket is much smaller, while explicit trace replay is slower because the certs are larger and each trace step has more parsing/replay work.
- Breakdown:

```text
Single-thread full check
========================

Pre-trace baseline
├── total measured: 201.471s
├── target/module load: 69.452s
├── certificate checking: 131.808s
│   ├── cached cert checks: 30.811s
│   └── other verification: 100.998s
└── throughput: 709 certs/s

Certificate trace
├── total measured: 140.039s
├── target/module load: 69.762s
├── certificate checking: 70.030s
│   ├── cached cert checks: 43.495s
│   └── other verification: 26.535s
└── throughput: 1,335 certs/s

Perf interpretation:
├── pre-trace profile: imported/local fact insertion with eager boolean-reduction closure
│   is the dominant visible checker branch.
├── current profile: eager boolean-reduction discovery is no longer a visible top branch.
└── explicit trace replay is slower after the certificate-trace rollout because it includes
    claim parsing, generic/specialized normalization, trace insertion, and exact one-step
    boolean-reduction checks.
```
