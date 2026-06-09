# Acorn Scorer Training

This uv project trains proof-step scoring models from `acorn eval --trace-out` JSONL exports.
Trace feature names are written once in a sidecar `*.meta.json` file; training reads the numeric
`feature_vector` values from the JSONL rows. Both plain `.jsonl` and gzip-compressed `.jsonl.gz`
traces are supported.

The current training signal is one row per activated proof step:

- input: selected columns from the trace row's `feature_vector`, using names from the sidecar
  `*.meta.json`
- label: `used_in_final_proof`

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
uv run acorn-train-scorer ../traces/onnx.jsonl.gz --out ../files/models/scorer.onnx
```

For quick inspection without training:

```bash
cd python
uv run acorn-train-scorer ../traces/onnx.jsonl.gz --inspect-only
```
