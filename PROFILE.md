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

- Date: 2026-05-05
- Git hash: `4e6f69fc` plus local uncommitted changes
- Command: `RUSTFLAGS='-C force-frame-pointers=yes' cargo build --bin acorn --profile=fastdev`; memory run with `/usr/bin/time -v target/release/acorn check --jobs 1`; allocator stats with `MIMALLOC_SHOW_STATS=1 target/release/acorn check --jobs 1`; page-fault profile with `perf record -g --call-graph fp -e page-faults -o perf.data target/fastdev/acorn check --jobs 1`; retained heap diagnostic with `cargo run --profile release --bin profile_memory`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF (20 logical CPUs); 31.2 GiB RAM
- Timing: single-worker release check completed successfully in `49.20s` wall, `48.47s` user, `0.72s` sys; maximum RSS was `7,455,696 KB` (`7.1 GiB`); mimalloc reported `8.0 GiB` reserved, `7.9 GiB` committed, and `7.1 GiB` process RSS; page-fault profile captured `3,233` samples / about `123,270` events. After removing retained lowered imports and import kernel contexts, `profile_memory` full check-style load reached `6.14 GiB` HWM after `8.40s` of target/dependency load, down from the prior `7.10 GiB` diagnostic HWM.
- Summary: The high RSS is primarily established during verifier setup and target/module loading, before the certificate-checking phase. A sampled run reached about `7.47 GiB` RSS by the time `verifying 173 modules...` printed, then only grew to about `7.51 GiB` during checking. The page-fault profile agrees: `86.6%` of sampled page faults are under `Verifier::new_for_check`, and `81.2%` under `Project::add_src_targets` / `Project::load_module`. The retained heap diagnostic shows the source text is not the issue: loading still retains `18,447` environments, `86,633` nodes, `105,080` binding snapshots, and `132,986` lowered `KernelContext` snapshots. Certificate replay contributes some additional allocation, but it is not the main source of peak RSS.
- Breakdown:

```text
Page-Fault Top-Down Breakdown
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

Retained Heap Diagnostic
============================================================

rss after full check-style load: 6.14 GiB (6.14 GiB HWM)

retained object counts:
├── 173 modules, 18,447 environments, 86,633 nodes
├── 105,080 binding snapshots with 38,972,184 summed binding entries
├── 96,253 module/node lowered facts containing 95,850 proof steps
├── 36,733 lowered goals containing 39,567 proof steps
├── 173 environment kernel contexts
└── 132,986 lowered kernel contexts

destructive clear sequence, order-sensitive but useful for retained buckets:
├── clear node/module lowered facts: -921 MiB
├── clear environment kernel contexts: -304 MiB
├── clear binding snapshots: -14 MiB RSS after prior clears
├── clear token/line maps: -285 MiB
├── clear node payloads: -1.64 GiB
└── clear remaining nodes / block environment tree: -2.76 GiB

largest retained local-lowered-fact modules:
├── set: 5,587 steps / 5,587 facts
├── relation_transport: 4,029 steps / 4,031 facts
├── order: 3,772 steps / 3,795 facts
└── order_iso: 3,396 steps / 3,396 facts
```
