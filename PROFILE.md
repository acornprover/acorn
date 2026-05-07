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

- Date: 2026-05-07 for retained heap diagnostic; full check timing/page-fault profile still from 2026-05-05
- Git hash: `14ea47e5` plus local uncommitted changes for the retained heap diagnostic; full timing/page-fault profile was `4e6f69fc` plus local uncommitted changes
- Command: retained heap diagnostic with `cargo run --profile release --bin profile_memory`; older full timing/page-fault profile used `RUSTFLAGS='-C force-frame-pointers=yes' cargo build --bin acorn --profile=fastdev`, `/usr/bin/time -v target/release/acorn check --jobs 1`, `MIMALLOC_SHOW_STATS=1 target/release/acorn check --jobs 1`, and `perf record -g --call-graph fp -e page-faults -o perf.data target/fastdev/acorn check --jobs 1`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: retained heap diagnostic reached `8.25 GiB` RSS / HWM after `15.199s` of target/dependency load and `17.079s` total measured time. The older single-worker release check completed successfully in `49.20s` wall, `48.47s` user, `0.72s` sys; maximum RSS was `7,455,696 KB` (`7.1 GiB`); mimalloc reported `8.0 GiB` reserved, `7.9 GiB` committed, and `7.1 GiB` process RSS; page-fault profile captured `3,233` samples / about `123,270` events.
- Summary: The retained heap diagnostic now runs with `UsageMode::Check` and check-only IDE metadata discard, so token and line metadata are gone from the retained heap (`0` token infos, `0` line entries, and clearing token/line maps releases `0 B`). RSS is still high, and higher than the older diagnostic, because the current library has grown to `272` modules, `23,855` environments, `116,306` nodes, `140,161` binding snapshots, and `178,522` lowered `KernelContext` snapshots. The earlier page-fault profile still indicates high RSS is primarily established during verifier setup and target/module loading, before certificate checking.
- Breakdown:

```text
Page-Fault Top-Down Breakdown (2026-05-05, not rerun)
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

rss after full check-style load: 8.25 GiB (8.25 GiB HWM)

retained object counts:
├── 272 modules, 23,855 environments, 116,306 nodes
├── 140,161 binding snapshots with 56,433,464 summed binding entries
├── 128,923 module/node lowered facts containing 128,506 proof steps
├── 49,599 lowered goals containing 53,167 proof steps
├── 272 environment kernel contexts
├── 178,522 lowered kernel contexts
└── 0 token infos and 0 line entries

destructive clear sequence, order-sensitive but useful for retained buckets:
├── clear node/module lowered facts: -1.21 GiB
├── clear environment kernel contexts: -541.2 MiB
├── clear binding snapshots: -18.7 MiB RSS after prior clears
├── clear current bindings: -173.3 MiB
├── clear token/line maps: 0 B
├── clear node payloads: -2.20 GiB
└── clear remaining nodes / block environment tree: -3.67 GiB

largest retained local-lowered-fact modules:
├── set_lattice: 7,977 steps / 7,984 facts
├── set: 5,587 steps / 5,587 facts
├── relation_transport: 4,029 steps / 4,031 facts
├── order: 3,772 steps / 3,795 facts
└── order_iso: 3,396 steps / 3,396 facts
```
