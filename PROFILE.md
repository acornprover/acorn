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
