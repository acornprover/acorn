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

- Date: 2026-04-29
- Git hash: `c34ae04b211fa44d11fc084e1387314a6494417f`
- Command: `RUSTFLAGS='-C force-frame-pointers=yes' cargo build --bin=profile_check --profile=fastdev`; timed run with `/usr/bin/time -p target/fastdev/profile_check`; sampled run with `perf record -g --call-graph fp -o perf.data target/fastdev/profile_check`
- Machine: `freedom`; Ubuntu 22.04 kernel `6.8.0-110-generic`; Intel Core i7-12700KF (20 logical CPUs); 31 GiB RAM
- Timing: warm timed run completed successfully in `real 14.22`, `user 13.92`, `sys 0.29`; sampled run captured `58,120` core samples and wrote `14.813 MB` of `perf.data`; check processed `16,343` cached certificates with no searches
- Summary: `profile_check` is still dominated by the same term-normalization, allocation, and certificate-checking costs as the 2026-04-15 baseline. Wall time increased from `7.77s` to `14.22s` (`1.83x`), while sampled core cycles increased from `31,655` to `58,120` samples (`1.84x`). Because the top self-time functions are nearly unchanged, this looks more like acornlib/certificate corpus growth than a distinct new checker hotspot. The new CLI timing breakdown also shows about `3.26s` in project/target module loading and about `10.89s` in certificate checking for `cargo run --profile release -- check`.
- Breakdown:

```text
Top-Down Breakdown
============================================================

100.0%  profile_check
├── ~23%  Verifier::new / Project::add_src_targets
│   └── module loading and elaboration
│       └── 13.5%  Environment::run_lowering_pass
└── 78.6%  Verifier::run
    └── 77.2%  Builder::build
        └── 77.2%  Builder::verify_module
            ├── 57.9%  Builder::verify_node (recursive)
            │   ├── certificate replay via Processor::check_cert_with_usage
            │   │   ├── Checker::check_cert_steps / Checker::insert_clause
            │   │   └── Certificate::parse_cert_steps_internal / ClaimCodec
            │   └── imported/local fact insertion via Processor::add_lowered_fact
            └── term normalization and allocation hot paths

Top self-time:
- 9.5% `TermRef::split_application_multi`
- 6.4% `mi_free`
- 6.3% `TermRef::to_owned`
- 6.1% `_mi_page_malloc`
- 4.8% `__memmove_avx_unaligned_erms`
- 4.4% `mi_heap_malloc_aligned_at`
- 4.1% `TermRef::decompose`
- 4.0% `term_normalization::split_symbol_application`
```
