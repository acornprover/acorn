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
- Git hash: `9d4371f556f727910fc63fe2426e0e48c69361b2`
- Command: `RUSTFLAGS='-C force-frame-pointers=yes' cargo build --bin=profile_check --profile=fastdev`; warm cache with `target/fastdev/profile_check`; timed run with `/usr/bin/time -p target/fastdev/profile_check`; sampled run with `perf record -g --call-graph fp -o perf.data target/fastdev/profile_check`
- Machine: `freedom`; Ubuntu 22.04 kernel `6.8.0-107-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Timing: warm timed run completed successfully in `real 18.72`, `user 18.49`, `sys 0.22`; sampled run captured `73,383` samples and wrote `16.018 MB` of `perf.data`
- Summary: `profile_check` is dominated by verifier work inside `Builder::verify_module`. The largest aggregate cost is copy-on-write proof structure cloning via `Rc::make_mut`, followed by certificate checking inside `verify_goal`, with `Checker::insert_clause` and `TermRef::split_application_multi` showing up as significant repeated costs. Self-time is allocator-heavy (`mimalloc` alloc/free plus `memmove`), which matches the cloning-heavy profile.
- Breakdown:

```text
Top-Down Breakdown
============================================================

98.7%  __libc_start_call_main
└── 88.6%  Verifier::run
    └── 87.8%  Builder::build
        └── 87.8%  Builder::verify_module
            ├── 49.6%  Rc::make_mut
            │   └── 38.8%  proof/clause cloning work
            │       ├── 14.2%  _mi_page_malloc
            │       ├── 8.5%   __memmove_avx_unaligned_erms
            │       ├── 6.3%   mi_free
            │       └── 4-4%   ProofStep::clone / Vec::clone
            ├── 28.4%  Builder::verify_goal
            │   ├── 20.9%  Processor::check_cert_with_usage
            │   │   └── 17.5%  Certificate::check_with_usage
            │   │       ├── 8.1%  Checker::check_cert_steps
            │   │       │   └── 5.5%  Checker::insert_clause
            │   │       └── 6.5%  Certificate::parse_cert_steps_internal
            │   │           └── 4.8%  ClaimCodec::try_deserialize_claim_expression
            │   └── 7.4%  Rc::drop_slow
            ├── 21.4%  Checker::insert_clause
            │   └── 11.2%  TermRef::split_application_multi
            └── 10.4%  Rc::drop_slow
```
