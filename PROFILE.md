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

- Date: 2026-05-09
- Git hash: `275285ad` plus local `LoweredModule` cleanup changes
- Command: `cargo run --profile release -- check --timing`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: after the upstream merge and local `LoweredModule` cleanup changes, full acornlib check completed successfully with `61.787s` measured time: `17.854s` project setup, including `17.841s` target/module load, plus `43.932s` certificate checking. The run verified `302` modules, checked `54,155` cached certificates, performed `0` searches, and elaborated `7` pending goals in `5` modules. This timing-only run did not collect max RSS; the prior max-RSS baseline was `7,769,036 KB` (`7.41 GiB`).
- Summary: The `LoweredModule` cut made check-mode module loading retain `BindingMap + LoweredModule` and drop the full `Environment` tree. Compared with the pre-refactor baseline (`0:59.97` wall, `9,721,212 KB` / `9.27 GiB` max RSS), peak RSS is down by `1,952,176 KB` (`1.86 GiB`, about `20.1%`) while wall time is roughly flat/slightly slower (`+0.37s`, about `0.6%`). Removing the duplicated lowered slots from `Environment`/`Node` did not produce a clear additional RSS win versus the initial `LoweredModule` result (`7,533,992 KB` / `7.19 GiB`) or the check-mode no-retained-lowering refinement (`7,688,584 KB` / `7.33 GiB`); current variation is plausibly allocator/run noise and retained `LoweredModule`/binding state.
- Breakdown:

```text
Current Full Check Baseline (2026-05-09, after duplicated Environment/Node lowering cleanup)
============================================================

command: cargo run --profile release -- check --timing
result: 302 modules, 54,155/54,155 certificates OK, 0 searches
total measured: 61.787s
project setup: 17.854s
cache load: 13.3ms
target/module load: 17.841s
build loading phase: 0.1ms
certificate checking: 43.932s
cached cert checks: 28.571s
other verification: 15.361s
certificate throughput: 1233 certs/s

Phase split by measured time:
├── target/module load: 17.841s / 61.787s = 28.9%
├── build loading scan: 0.1ms / 61.787s = ~0.0%
└── processing/checking: 43.932s / 61.787s = 71.1%
    ├── cached cert check calls: 28.571s / 61.787s = 46.2%
    └── other verification work: 15.361s / 61.787s = 24.9%

Current retained load memory diagnostic (2026-05-09, `target/release/profile_memory`):
├── check-style load time: 18.890s
├── RSS after full check-style load: 6.97 GiB
├── retained environments: 0
├── retained environment nodes: 0
├── retained binding maps: 302 current maps / 81,152 entries; 0 snapshots
├── retained lowered module facts: 126,100 facts / 125,790 proof steps
├── retained lowered goals: 54,162 goals / 58,153 proof steps
├── retained lowered kernel contexts: 180,262 contexts
└── destructive clear of `LoweredModule`: -3.56 GiB

Comparison to pre-refactor baseline:
├── previous elapsed: 0:59.97 wall
├── previous max rss: 9,721,212 KB = 9.27 GiB
├── RSS delta: -1,952,176 KB = -1.86 GiB (-20.1%)
└── wall delta: +0.37s (+0.6%)

Comparison to initial LoweredModule result:
├── previous elapsed: 1:01.41 wall
├── previous max rss: 7,533,992 KB = 7.19 GiB
├── RSS delta: +235,044 KB = +229.5 MiB (+3.1%)
└── wall delta: -1.07s (-1.7%)

Comparison to no-retained-Environment-lowering refinement:
├── previous elapsed: 1:00.96 wall
├── previous max rss: 7,688,584 KB = 7.33 GiB
├── RSS delta: +80,452 KB = +78.6 MiB (+1.0%)
└── wall delta: -0.62s (-1.0%)

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
