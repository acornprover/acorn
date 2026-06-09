# Acorn Scorer Training

This uv project trains proof-step scoring models from `acorn eval --trace-out` JSONL exports.
Trace feature names are written once in a sidecar `*.meta.json` file; training reads the numeric
`feature_vector` values from the JSONL rows. Both plain `.jsonl` and gzip-compressed `.jsonl.gz`
traces are supported.

The current training signal is one row per activated proof step:

- input: the trace row's `feature_vector`, matching `src/prover/features.rs`
- label: `used_in_final_proof`

The CLI trains a small PyTorch model and exports an ONNX model with the Rust scorer contract:

- input name: `input`
- input shape: `[batch_size, 9]`
- output name: `output`
- output shape: `[batch_size, 1]`
- output value: probability that the activated step is used in the final proof

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
