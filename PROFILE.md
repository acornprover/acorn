# Profile Baselines

Keep this file focused on current performance baselines. Historical rollout notes and old-format
migration comparisons belong in git history, not in the active profiling record.

## How To Read Check Performance

Track `check` in two modes:

- `--jobs 1`: best for total work and code-level profiling. Phase times are easy to interpret and
  mostly additive.
- `--jobs 20` or default jobs: best for user-visible wall time. This captures scheduling,
  dependency ordering, memory pressure, and the long-pole effect.

In parallel `check`, printed phase counters are not a simple sum of wall time. A 20-thread run can
report target/module load and certificate checking counters that are each close to total wall time,
because module loading and module work are overlapped in the streaming build path. Use the total
measured time and slowest-module table for wall-time interpretation.

## profile_check

### 2026-07-01 Current Full-Library Check Baseline

- Git hash: `1d8efa5e21022464861d617f7126f54407546cb0`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF; 20 logical CPUs; 31 GiB RAM
- Scope: full acornlib cached certificate check, `605` modules, `93,462/93,462` cached
  certificates OK, `0` searches.

Commands:

```bash
cargo build --profile release
/usr/bin/time -v target/release/acorn check --jobs 1 --timing
/usr/bin/time -v target/release/acorn check --jobs 20 --timing
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --bin=acorn --profile=fastdev
perf record -g --call-graph fp -o perf.data target/fastdev/acorn check --jobs 1 --timing
```

Single-thread timing:

```text
target/module load: 67.337s
certificate checking: 67.745s
  cached cert checks: 42.472s
  other verification: 25.273s
total measured: 135.325s
certificate throughput: 1,380 certs/s
wall clock: 2:15.69
max RSS: 3.49 GiB
```

20-thread timing:

```text
target/module load counter: 28.143s
certificate checking counter: 28.521s
  cached cert checks: 46.613s summed worker time
total measured: 29.053s
certificate throughput: 3,277 certs/s
wall clock: 0:29.52
CPU: 482%
max RSS: 4.36 GiB
```

Slowest modules in the 20-thread wall-time run:

```text
int.lattice                         4.722s total, 3.429s cert time
function_product_algebra            3.067s total, 2.549s cert time
real.real_field                     1.789s total, 1.447s cert time
set                                 1.638s total, 1.368s cert time
set_lattice                         1.607s total, 1.268s cert time
top100.theorem_071_order_of_a_subgroup
                                    1.356s total, 0.713s cert time
submodule                           1.122s total, 0.909s cert time
real.cauchy                         1.026s total, 0.782s cert time
```

Single-thread perf summary:

```text
Verifier::run
├── ~50% Builder::process_module_work_batch / verify lowered modules
│   ├── certificate trace replay
│   │   ├── Certificate::parse_code_line / claim deserialization
│   │   ├── TraceChecker::accept_clause_with_aliases
│   │   │   └── TermBridge::quote_clause / quote_term
│   │   ├── Checker::insert_clause_for_trace
│   │   └── Checker::check_clause_direct_for_trace
│   ├── checker cloning before cert replay
│   └── imported/local fact insertion into the checker
└── ~30% Project::load_target_by_descriptor / load_module
    └── module_loader::elaborate_and_lower_module
```

Hot self-time is broad rather than a single smoking gun:

```text
allocator work: _mi_page_malloc, mi_free, mi_heap_collect_ex, alloc/realloc
copying: memmove, Vec clone, String clone
term operations: TermRef::split_application_multi, decompose, Term::apply
hashing/maps: DefaultHasher::write, im::HashMap operations
syntax/loading: Token::scan_with_start_line, Expression::parse
normalization: normalize_clause_term_with_polarity, split_symbol_application
```

Current interpretation:

- Single-thread `check` is roughly half module load/lower and half certificate checking.
- Multi-thread wall time is much lower, but only uses about `4.8` cores on average. The parallel
  run is limited by streaming load, dependencies, memory/cache pressure, and slow modules rather
  than by perfect distribution over 20 workers.
- Certificate replay is no longer dominated by eager boolean-reduction expansion. Current replay
  cost is mostly parsing Acorn-readable trace claims, normalizing/lowering them, inserting them into
  the trace checker, and quoting clauses for diagnostics/line records.
- Further `check` wins probably need to reduce repeated load/elaboration work, reduce trace replay
  parsing/normalization/quoting, or improve parallel scheduling around the slowest modules.

## profile_load

### 2026-07-01 Current Target Load Baseline

- Git hash: `1d8efa5e21022464861d617f7126f54407546cb0`
- Machine: `freedom`; Linux `6.8.0-111-generic`; Intel Core i7-12700KF; 20 logical CPUs; 31 GiB RAM
- Target: `real.double_sum`

Commands:

```bash
cargo build --profile release --bin profile_load
/usr/bin/time -v target/release/profile_load
```

Timing:

```text
project setup: 60.4ms
  cache load: 59.4ms
target/dependency load: 8.768s
total measured: 8.828s
modules loaded: 596
targets: 117
wall clock: 0:09.16
max RSS: 3.49 GiB
```

Interpretation:

- Target/dependency load is still substantial on its own.
- For full `check`, load/lower work is now important enough to profile alongside certificate
  replay rather than treating it as setup noise.

## profile_verify

No current baseline collected in this pass. Refresh this section only when measuring edit-loop or
no-change `verify` performance.

## profile_reprove

No current baseline collected in this pass. Refresh this section only when measuring prover/search
performance.
