# Acorn Scorer Training

This uv project trains proof-step scoring models from `acorn eval --trace-out` JSONL.ZST exports.
Trace feature names are written once in a sidecar `*.meta.json` file; training reads the numeric
`feature_vector` values from the compressed JSONL rows. Raw traces are standardized on
`.jsonl.zst`.

The current training signal is one row per activated proof step:

- input: selected columns from the trace row's `feature_vector`, using names from the sidecar
  `*.meta.json`
- label: `used_in_final_proof`

Rows from failed searches are kept with their real `outcome` and `used_in_final_proof=false`.

By default the trainer uses all trace catalog features. Repeat `--feature NAME` to train on an
explicit subset.

The CLI trains a small PyTorch model and exports an ONNX model plus `*.features.json` sidecar:

- input name: `input`
- input shape: `[batch_size, selected_feature_count]`
- output name: `output`
- output shape: `[batch_size, 1]`
- output value: probability that the activated step is used in the final proof
- feature contract: exact input feature names and order

Minimal example:

```bash
cd python
uv run acorn-train-scorer ../tmp/acorn-eval-latest/shards \
  --out ../tmp/models/scorer.onnx
```

For quick inspection without training from raw traces:

```bash
cd python
uv run acorn-train-scorer ../traces/latest.jsonl.zst --inspect-only
```

## Normal Training Workflow

Use exactly one eval-suite output directory as one training generation. Do not mix traces from
different eval-suite runs unless you are doing that deliberately; one run is simpler to reason about
and already contains comparable traces for each policy.

The normal training path is:

1. Run the eval suite with tracing.
2. Convert that run's raw `.jsonl.zst` traces into binary shards.
3. Train from the shard directory, not from raw JSON.

Direct trace training is mainly for smoke tests and early experiments.

For the current suite layout, `handcrafted` is intentionally not part of the standard training
corpus. Build shards from the latest non-handcrafted traces like this:

```bash
cd python
uv run acorn-build-scorer-shards \
  ../tmp/acorn-eval-latest/traces/depth-first-[0-9][0-9][0-9][0-9][0-9][0-9].jsonl.zst \
  ../tmp/acorn-eval-latest/traces/onnx-[0-9][0-9][0-9][0-9][0-9][0-9].jsonl.zst \
  ../tmp/acorn-eval-latest/traces/onnx-no-shallow-[0-9][0-9][0-9][0-9][0-9][0-9].jsonl.zst \
  ../tmp/acorn-eval-latest/traces/trained-5m-[0-9][0-9][0-9][0-9][0-9][0-9].jsonl.zst \
  ../tmp/acorn-eval-latest/traces/trained-5m-no-shallow-[0-9][0-9][0-9][0-9][0-9][0-9].jsonl.zst \
  --out ../tmp/shards/model-YYYYMMDD-latest-allpos-neg20m \
  --max-negatives 20000000 \
  --shard-rows 1000000 \
  --workers 0 \
  --overwrite
```

Then train a size sweep from those shards:

```bash
uv run acorn-train-scorer ../tmp/shards/model-YYYYMMDD-latest-allpos-neg20m \
  --out '../tmp/models/model-YYYYMMDD-h{hidden_size}-l3.onnx' \
  --hidden-size-sweep 128,256,512 \
  --hidden-layers 3 \
  --epochs 5 \
  --batch-size 65536 \
  --device cuda \
  --seed 42
```

With a sweep, the trainer loads and splits the shard dataset once, then trains each requested
architecture on the same train/validation split. The `--out` path can use `{hidden_size}` and
`{hidden_layers}` placeholders.

For CPU-only fallback, use `--device cpu --threads 20` or another appropriate thread count.

## CUDA Notes

The project uses a CUDA-enabled PyTorch wheel. A quick sanity check is:

```bash
cd python
uv run python -c "import torch; print(torch.__version__); print(torch.cuda.is_available()); print(torch.cuda.get_device_name(0) if torch.cuda.is_available() else 'no cuda')"
```

On the current workstation this should report `torch 2.4.1+cu121`, `True`, and
`NVIDIA GeForce RTX 3080 Ti`.

In Codex/tool-driven runs, prefer `uv run ...` for GPU training. Direct `.venv/bin/python ...`
commands can run inside a sandbox that hides `/dev/nvidia*`; in that case PyTorch is built with
CUDA but reports `torch.cuda.is_available() == False` and may warn that it cannot initialize NVML.

## Training Shards

The intended training cache format is a directory of fixed-row-count binary shards plus a manifest.
Raw `.jsonl.zst` traces should remain the inspectable archive format; repeated training should read
the shards instead of reparsing JSON.

Initial shard layout:

- `manifest.json`: schema version, feature names, policy names, source trace paths, shard row
  counts, and split/sampling settings
- `shard-000000.pt`, `shard-000001.pt`, ...: PyTorch-saved dictionaries with tensor fields

Each shard should store:

- `features`: `float32` tensor with shape `[rows, features]`
- `labels`: `bool` or `uint8` tensor for `used_in_final_proof`
- `group_ids`: integer tensor for `(module, goal)` split groups
- `goal_buckets`: `int16` tensor for the stable eval/training partition, or `-1` for unstamped rows
- `policy_ids`: small integer tensor for policy source
- optional cheap analysis fields such as `activation_index`

Shard boundaries should be based on row count, not module or policy. The converter should preserve
group ids for train/validation splitting, but training wants to shuffle across modules and policies.
For new traces that include `goal_bucket`, training uses buckets `90-99` as validation and `0-89`
as trainable rows. Legacy traces or shards without usable buckets fall back to a randomized
`(module, goal)` grouped split.
For a full corpus conversion, use positive-preserving negative sampling before writing shards. This
keeps all known-good proof steps while bounding the much larger negative class.

The converter supports either uniform reservoir sampling or positive-preserving negative sampling.
The positive-preserving mode keeps every `used_in_final_proof=true` row and reservoir-samples only
negative rows, which is the normal choice for serious scorer training:

```bash
uv run acorn-build-scorer-shards TRACE... \
  --max-negatives 20000000 \
  --shard-rows 1000000 \
  --workers 0 \
  --out ../tmp/shards
```

`--workers 0` uses one worker per trace file up to the local CPU count. Parallel negative sampling is
file-stratified by trace size, then merged into a normal shard manifest.

The latest non-handcrafted eval-suite run on 2026-06-11 produced this shard build with
`--max-negatives 20000000`: 127,437,913 scanned trace rows, 1,011,106 positive rows, 20,000,000
negative rows, 21,011,106 written shard rows, and about 5.1 GiB on disk.

Uniform reservoir sampling is still useful for small smoke-test datasets:

```bash
uv run acorn-build-scorer-shards TRACE... \
  --sample-records 5000000 \
  --shard-rows 1000000 \
  --out ../tmp/shards
```

Without `--sample-records`, it writes all rows in input order. Use `--max-records` for smoke tests.

Train from the resulting shard directory:

```bash
uv run acorn-train-scorer ../tmp/shards \
  --out ../tmp/models/scorer.onnx
```

`acorn-train-scorer` still accepts raw trace files for smoke tests, but serious runs should train
from shard directories.
