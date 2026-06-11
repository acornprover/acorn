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

By default the trainer uses all trace catalog features. Use `--features legacy` to train on the
old nine-feature ONNX contract, or repeat `--feature NAME` to train on an explicit subset.

The CLI trains a small PyTorch model and exports an ONNX model plus `*.features.json` sidecar:

- input name: `input`
- input shape: `[batch_size, selected_feature_count]`
- output name: `output`
- output shape: `[batch_size, 1]`
- output value: probability that the activated step is used in the final proof
- feature contract: exact input feature names and order

Example:

```bash
cd python
uv run acorn-train-scorer ../tmp/acorn-eval-latest/shards \
  --out ../tmp/models/scorer.onnx
```

For quick inspection without training from raw traces:

```bash
cd python
uv run acorn-train-scorer ../traces/legacy.jsonl.zst --inspect-only
```

For large eval-suite trace corpora, use reservoir sampling to keep memory bounded while still
sampling across all input traces:

The normal training path should convert raw `.jsonl.zst` traces into binary shards first, then train
from those shards. Direct trace training is mainly for smoke tests and early experiments.

```bash
cd python
uv run acorn-build-scorer-shards ../tmp/acorn-eval-latest/traces/*.jsonl.zst \
  --sample-records 1000000 \
  --shard-rows 250000 \
  --out ../tmp/acorn-eval-latest/shards
```

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
- `group_ids`: integer tensor for `(module, goal, skip, policy)` split groups
- `policy_ids`: small integer tensor for policy source
- optional cheap analysis fields such as `activation_index`

Shard boundaries should be based on row count, not module or policy. The converter should preserve
group ids for train/validation splitting, but training wants to shuffle across modules and policies.
For a full corpus conversion, use a bounded shuffle buffer or policy-balanced sampling before writing
shards so early training batches are not dominated by trace-file order.

The first converter supports reservoir sampling:

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
