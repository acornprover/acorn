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

- Date: 2026-04-15
- Git hash: `89e6fc2a0aa774a1de32eacaebfab46a9e570a44`
- Command: `RUSTFLAGS='-C force-frame-pointers=yes' cargo build --bin=profile_check --profile=fastdev`; warm cache with `target/fastdev/profile_check`; timed run with `/usr/bin/time -p target/fastdev/profile_check`; sampled run with `perf record -g --call-graph fp -o perf.data target/fastdev/profile_check`
- Machine: `freedom`; Ubuntu 22.04 kernel `6.8.0-107-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Timing: warm timed run completed successfully in `real 7.77`, `user 7.58`, `sys 0.18`; sampled run captured `31,655` samples and wrote `8.153 MB` of `perf.data`
- Summary: `profile_check` is now dominated by actual certificate checking and term normalization inside `Builder::verify_module`. The earlier `Rc::make_mut`/snapshot-cloning hotspot was largely eliminated by avoiding unnecessary `make_mut` at `verify_node` entry and by removing prover state from check-only processors. `Rc::make_mut` is now down to about `0.74%` inclusive, so the main costs are `Checker::insert_clause`, `TermRef::split_application_multi`, and certificate parsing.
- Breakdown:

```text
Top-Down Breakdown
============================================================

100.0%  Verifier::run
└── 100.0%  Builder::build
    └── 100.0%  Builder::verify_module
        ├── 35.9%  Certificate::check_with_usage
        │   ├── 17.3%  Checker::check_cert_steps
        │   │   └── 11.9%  Checker::insert_clause
        │   └── 12.8%  Certificate::parse_cert_steps_internal
        │       └── 9.5%  ClaimCodec::try_deserialize_claim_expression
        ├── 24.7%  TermRef::split_application_multi
        ├── 0.8%  Rc::drop_slow
        └── 0.7%  Rc::make_mut

Top self-time:
- 8.7% `TermRef::split_application_multi`
- 6.1% `mi_free`
- 5.9% `TermRef::to_owned`
- 5.7% `_mi_page_malloc`
- 5.0% `__memmove_avx_unaligned_erms`
```
