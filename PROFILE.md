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

## profile_check

- Date: 2026-05-11
- Git hash: `a1e4091c` plus local checkpoint-lifetime cleanup
- Command: `/usr/bin/time -v target/release/acorn check --jobs 20 --timing`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: full acornlib check completed successfully with `23.445s` measured time: `20.461s` target/module load, `23.389s` certificate checking, `19.101s` inside cached certificate checks, and `4.288s` other verification. The run verified `319` modules, checked `56,405` cached certificates, performed `0` searches, elaborated `7` pending goals in `5` modules, and peaked at `2,477,768 KB` max RSS (`2.36 GiB`). `/usr/bin/time` reported `0:23.63` wall, `100.76s` user, `1.18s` system, and `431%` CPU.
- Summary: Check still requests all available worker threads by default. The useful fix was not adding duplicate work to raise CPU usage; it was removing repeated checker work and keeping the existing workers busier. The checker now skips repeated concrete clauses and re-expands repeated variable clauses only when new concrete facts have arrived. Check-mode exports are pre-normalized, active module processors retain newly visible imports, check scheduling includes local lowered step counts, and ordinary check mode no longer keeps eval-only processor checkpoints alive across `Rc::make_mut`. Compared with the previous local `--jobs 20` baseline (`0:48.94`, `2,527,464 KB` max RSS, `307%` CPU), wall time is down about `25.31s` (`51.7%`), peak RSS is down `49,696 KB` (`2.0%`), and CPU utilization is up to `431%`.
- Breakdown:

```text
Current Full Check Baseline (2026-05-11, checkpoint-lifetime cleanup)
=====================================================================

command: /usr/bin/time -v target/release/acorn check --jobs 20 --timing
result: 319 modules, 56,405/56,405 certificates OK, 0 searches
max RSS: 2,477,768 KB = 2.36 GiB
total measured: 23.445s
wall clock: 0:23.63
user time: 100.76s
system time: 1.18s
CPU: 431%
project setup: 19.5ms
cache load: 19.5ms
target/module load: 20.461s
build loading phase: 0.0ms
certificate checking: 23.389s
cached cert checks: 19.101s
other verification: 4.288s
certificate throughput: 2412 certs/s

Overlapped timing measurements:
├── target/module load: 20.461s / 23.445s = 87.3%
└── processing/checking: 23.389s / 23.445s = 99.8%
    ├── cached cert check calls: 19.101s / 23.445s = 81.5%
    └── other verification work: 4.288s / 23.445s = 18.3%

Slowest rebuilt modules by total processing time:
├── function_product_algebra: 5.566s total, 1.335s cert time
├── finite_group: 3.776s total, 69.7ms cert time
├── top100.theorem_071_order_of_a_subgroup: 3.034s total, 111.9ms cert time
├── int.lattice: 1.922s total, 201.2ms cert time
└── function_product_units: 1.360s total, 203.4ms cert time

Perf top-down sample after the checker duplicate-expansion change (2026-05-11):
├── command: perf record -g --call-graph fp -o perf.data target/fastdev/profile_check
├── samples: 414,152; perf.data 109.2 MB
├── dominant path: Verifier::run -> Builder::process_module_work_batch -> Builder::verify_lowered_module
├── roughly 53% of the captured top-down path was Processor::add_imports_from_bindings
├── roughly 46% of the captured path was Checker::insert_clause_internal under imported facts
└── hot self-time was allocator/memmove/term ownership, normalization, hashing, and equality-graph cloning

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
