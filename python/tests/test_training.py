from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import torch
import zstandard

from acorn_training.data import (
    LEGACY_FEATURE_NAMES,
    TRACE_SCHEMA,
    DatasetSplit,
    load_shard_dataset,
    load_trace_dataset,
    split_by_search,
    trace_metadata_path,
)
from acorn_training.model import ProbabilityScorer, ScorerNet
from acorn_training.shards import SHARD_SCHEMA, ShardBuildConfig, build_shards
from acorn_training.train import (
    FEATURE_CONTRACT_SCHEMA,
    TrainConfig,
    export_onnx,
    feature_contract_path,
    train_model,
)

TEST_FEATURE_NAMES = LEGACY_FEATURE_NAMES + ["literal_count", "rule_is_resolution"]


def _record(goal: str, index: int, label: bool, goal_bucket: int | None = None) -> dict:
    record = {
        "schema": TRACE_SCHEMA,
        "module": "foo",
        "goal": goal,
        "goal_first_line": 1,
        "goal_last_line": 3,
        "skip": 0,
        "policy": "onnx",
        "outcome": "success",
        "activation_index": index,
        "passive_id": index,
        "active_id": index,
        "used_in_final_proof": label,
        "queue_score": 0.0,
        "queue_contradiction": False,
        "queue_shallow_status": "unspent",
        "queue_is_shallow": True,
        "rule": "Assumption",
        "truthiness": "factual",
        "feature_vector": [
            0.0,
            float(index + 1),
            0.0,
            0.0,
            1.0,
            1.0,
            0.0,
            float(index + 2),
            float(index),
            1.0,
            0.0,
        ],
    }
    if goal_bucket is not None:
        record["goal_bucket"] = goal_bucket
    return record


class TrainingDataTest(unittest.TestCase):
    def _write_trace(self, path: Path, rows: list[dict]) -> None:
        trace_metadata_path(path).write_text(
            json.dumps(
                {
                    "schema": TRACE_SCHEMA,
                    "feature_vector": TEST_FEATURE_NAMES,
                }
            )
        )
        with zstandard.open(path, "wt") as f:
            f.write("\n".join(json.dumps(row) for row in rows) + "\n")

    def test_loads_trace_and_splits_by_search(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trace.jsonl.zst"
            rows = [
                _record("a", 0, True),
                _record("a", 1, False),
                _record("b", 0, True),
                _record("b", 1, False),
            ]
            self._write_trace(path, rows)

            dataset = load_trace_dataset([path])
            self.assertEqual(dataset.num_examples, 4)
            self.assertEqual(dataset.num_positive, 2)
            self.assertEqual(dataset.feature_names, TEST_FEATURE_NAMES)

            split = split_by_search(dataset, validation_fraction=0.5, seed=1)
            self.assertEqual(split.train_features.shape[1], len(TEST_FEATURE_NAMES))
            self.assertEqual(split.val_features.shape[1], len(TEST_FEATURE_NAMES))
            self.assertEqual(
                split.train_labels.numel() + split.val_labels.numel(),
                4,
            )

            legacy_dataset = load_trace_dataset([path], feature_names=LEGACY_FEATURE_NAMES)
            self.assertEqual(legacy_dataset.features.shape[1], len(LEGACY_FEATURE_NAMES))
            self.assertEqual(legacy_dataset.feature_names, LEGACY_FEATURE_NAMES)

    def test_reservoir_sample_scans_all_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            first = Path(tmp) / "first.jsonl.zst"
            second = Path(tmp) / "second.jsonl.zst"
            self._write_trace(first, [_record("a", i, i == 0) for i in range(10)])
            self._write_trace(second, [_record("b", i, i == 0) for i in range(10)])

            dataset = load_trace_dataset(
                [first, second],
                sample_records=6,
                seed=3,
            )

            self.assertEqual(dataset.num_examples, 6)
            self.assertEqual(dataset.metadata["scanned_records"], 20)
            self.assertEqual(dataset.metadata["loaded_records"], 6)
            self.assertIn("foo\tb", dataset.groups)

    def test_search_groups_ignore_policy_and_skip(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trace.jsonl.zst"
            rows = [
                _record("same", 0, True),
                {**_record("same", 1, False), "policy": "depth-first"},
                {**_record("same", 2, False), "skip": 1},
                _record("other", 0, True),
            ]
            self._write_trace(path, rows)

            dataset = load_trace_dataset([path])
            self.assertEqual(dataset.groups[0], dataset.groups[1])
            self.assertEqual(dataset.groups[0], dataset.groups[2])
            self.assertNotEqual(dataset.groups[0], dataset.groups[3])

            split = split_by_search(dataset, validation_fraction=0.5, seed=1)
            self.assertEqual(
                sorted([split.train_labels.numel(), split.val_labels.numel()]),
                [1, 3],
            )

    def test_goal_buckets_define_validation_split_when_present(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trace.jsonl.zst"
            rows = [
                _record("train", 0, True, goal_bucket=12),
                _record("train", 1, False, goal_bucket=12),
                _record("val", 0, True, goal_bucket=90),
                _record("val", 1, False, goal_bucket=90),
            ]
            self._write_trace(path, rows)

            dataset = load_trace_dataset([path])
            self.assertEqual(dataset.metadata["rows_with_goal_bucket"], 4)
            self.assertEqual(dataset.goal_buckets.tolist(), [12, 12, 90, 90])

            split = split_by_search(dataset, validation_fraction=0.1, seed=1)
            self.assertEqual(split.train_labels.numel(), 2)
            self.assertEqual(split.val_labels.numel(), 2)
            self.assertEqual(split.train_labels.tolist(), [1.0, 0.0])
            self.assertEqual(split.val_labels.tolist(), [1.0, 0.0])

    def test_rejects_non_zstd_trace_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trace.jsonl"
            with self.assertRaisesRegex(ValueError, "must end in .jsonl.zst"):
                load_trace_dataset([path])

    def test_builds_training_shards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            trace = Path(tmp) / "trace.jsonl.zst"
            out_dir = Path(tmp) / "shards"
            self._write_trace(
                trace,
                [
                    _record("a", 0, True),
                    _record("a", 1, False),
                    _record("b", 0, True),
                    _record("b", 1, False),
                    _record("c", 0, False),
                ],
            )

            summary = build_shards(
                ShardBuildConfig(
                    trace_paths=[trace],
                    out_dir=out_dir,
                    shard_rows=2,
                ),
                progress=None,
            )

            self.assertEqual(summary.scanned_records, 5)
            self.assertEqual(summary.written_records, 5)
            self.assertEqual(summary.shard_count, 3)
            manifest = json.loads((out_dir / "manifest.json").read_text())
            self.assertEqual(manifest["schema"], SHARD_SCHEMA)
            self.assertEqual(manifest["feature_names"], TEST_FEATURE_NAMES)
            self.assertEqual(manifest["group_names"], ["foo\ta", "foo\tb", "foo\tc"])
            self.assertEqual(manifest["written_records"], 5)
            self.assertEqual(len(manifest["shards"]), 3)

            shard = torch.load(out_dir / "shard-000000.pt", weights_only=False)
            self.assertEqual(shard["schema"], SHARD_SCHEMA)
            self.assertEqual(tuple(shard["features"].shape), (2, len(TEST_FEATURE_NAMES)))
            self.assertEqual(tuple(shard["labels"].shape), (2,))
            self.assertEqual(tuple(shard["group_ids"].shape), (2,))

            dataset = load_shard_dataset([out_dir])
            self.assertEqual(dataset.num_examples, 5)
            self.assertEqual(dataset.num_positive, 2)
            self.assertEqual(dataset.feature_names, TEST_FEATURE_NAMES)
            self.assertEqual(dataset.metadata["loaded_records"], 5)
            self.assertEqual(dataset.metadata["policy:onnx"], 5)
            self.assertIsNone(dataset.goal_buckets)

            limited = load_shard_dataset([out_dir], max_records=3)
            self.assertEqual(limited.num_examples, 3)
            self.assertEqual(limited.metadata["loaded_records"], 3)

    def test_shards_preserve_goal_buckets(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            trace = Path(tmp) / "trace.jsonl.zst"
            out_dir = Path(tmp) / "shards"
            self._write_trace(
                trace,
                [
                    _record("a", 0, True, goal_bucket=0),
                    _record("b", 0, False, goal_bucket=90),
                    _record("c", 0, False, goal_bucket=99),
                ],
            )

            build_shards(
                ShardBuildConfig(
                    trace_paths=[trace],
                    out_dir=out_dir,
                    shard_rows=2,
                ),
                progress=None,
            )

            dataset = load_shard_dataset([out_dir])
            self.assertEqual(dataset.goal_buckets.tolist(), [0, 90, 99])
            split = split_by_search(dataset, validation_fraction=0.1, seed=1)
            self.assertEqual(split.train_labels.numel(), 1)
            self.assertEqual(split.val_labels.numel(), 2)

    def test_builds_sampled_training_shards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            first = Path(tmp) / "first.jsonl.zst"
            second = Path(tmp) / "second.jsonl.zst"
            out_dir = Path(tmp) / "sampled"
            self._write_trace(first, [_record("a", i, i == 0) for i in range(8)])
            self._write_trace(second, [_record("b", i, i == 0) for i in range(8)])

            summary = build_shards(
                ShardBuildConfig(
                    trace_paths=[first, second],
                    out_dir=out_dir,
                    shard_rows=3,
                    sample_records=5,
                    seed=7,
                ),
                progress=None,
            )

            self.assertEqual(summary.scanned_records, 16)
            self.assertEqual(summary.written_records, 5)
            self.assertEqual(summary.shard_count, 2)
            manifest = json.loads((out_dir / "manifest.json").read_text())
            self.assertTrue(manifest["sampled"])
            self.assertEqual(manifest["source_trace_rows"], [8, 8])
            self.assertEqual(sum(shard["rows"] for shard in manifest["shards"]), 5)

    def test_builds_positive_preserving_sampled_training_shards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            trace = Path(tmp) / "trace.jsonl.zst"
            out_dir = Path(tmp) / "sampled"
            rows = [
                _record("a", 0, True),
                _record("a", 1, False),
                _record("b", 0, False),
                _record("c", 0, True),
                _record("d", 0, False),
                _record("e", 0, True),
                _record("f", 0, False),
            ]
            self._write_trace(trace, rows)

            summary = build_shards(
                ShardBuildConfig(
                    trace_paths=[trace],
                    out_dir=out_dir,
                    shard_rows=3,
                    max_negative_records=2,
                    seed=7,
                ),
                progress=None,
            )

            self.assertEqual(summary.scanned_records, 7)
            self.assertEqual(summary.written_records, 5)
            self.assertEqual(summary.positive_records, 3)
            manifest = json.loads((out_dir / "manifest.json").read_text())
            self.assertTrue(manifest["sampled"])
            self.assertEqual(manifest["sampling_mode"], "all_positives_max_negatives")
            self.assertEqual(manifest["max_negative_records"], 2)
            self.assertEqual(manifest["positive_records"], 3)
            self.assertEqual(manifest["negative_records"], 2)

            dataset = load_shard_dataset([out_dir])
            self.assertEqual(dataset.num_examples, 5)
            self.assertEqual(dataset.num_positive, 3)
            self.assertEqual(dataset.num_negative, 2)

    def test_builds_positive_preserving_sampled_training_shards_in_parallel(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            first = Path(tmp) / "first.jsonl.zst"
            second = Path(tmp) / "second.jsonl.zst"
            out_dir = Path(tmp) / "sampled"
            self._write_trace(first, [_record("a", i, i == 0) for i in range(6)])
            self._write_trace(second, [_record("b", i, i == 0) for i in range(6)])

            summary = build_shards(
                ShardBuildConfig(
                    trace_paths=[first, second],
                    out_dir=out_dir,
                    shard_rows=3,
                    max_negative_records=4,
                    workers=2,
                    seed=7,
                ),
                progress=None,
            )

            self.assertEqual(summary.scanned_records, 12)
            self.assertEqual(summary.written_records, 6)
            self.assertEqual(summary.positive_records, 2)
            manifest = json.loads((out_dir / "manifest.json").read_text())
            self.assertEqual(
                manifest["sampling_mode"],
                "all_positives_file_stratified_max_negatives",
            )
            self.assertEqual(manifest["workers"], 2)

            dataset = load_shard_dataset([out_dir])
            self.assertEqual(dataset.num_examples, 6)
            self.assertEqual(dataset.num_positive, 2)
            self.assertEqual(dataset.num_negative, 4)
            self.assertEqual(dataset.metadata["policy:onnx"], 6)

    def test_trains_from_loaded_shards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            trace = Path(tmp) / "trace.jsonl.zst"
            out_dir = Path(tmp) / "shards"
            rows = [
                _record("a", 0, True),
                _record("a", 1, False),
                _record("b", 0, True),
                _record("b", 1, False),
                _record("c", 0, True),
                _record("c", 1, False),
            ]
            self._write_trace(trace, rows)
            build_shards(
                ShardBuildConfig(
                    trace_paths=[trace],
                    out_dir=out_dir,
                    shard_rows=3,
                ),
                progress=None,
            )

            dataset = load_shard_dataset([out_dir])
            split = split_by_search(dataset, validation_fraction=0.33, seed=2)
            config = TrainConfig(
                epochs=1,
                batch_size=2,
                learning_rate=1e-3,
                weight_decay=0.0,
                hidden_size=4,
                hidden_layers=1,
                seed=1,
                device="cpu",
            )
            model, metrics = train_model(split, config)
            self.assertEqual(len(metrics), 1)
            self.assertTrue(metrics[0].is_best)

            output_path = Path(tmp) / "scorer.onnx"
            export_onnx(model, output_path, dataset.feature_names)
            self.assertTrue(output_path.exists())

    def test_model_exports_probability_shape(self) -> None:
        features = torch.randn(8, len(TEST_FEATURE_NAMES))
        model = ScorerNet.from_training_features(
            features,
            hidden_size=4,
            hidden_layers=1,
        )
        probabilities = ProbabilityScorer(model)(features)
        self.assertEqual(tuple(probabilities.shape), (8, 1))
        self.assertTrue(torch.all(probabilities >= 0.0))
        self.assertTrue(torch.all(probabilities <= 1.0))

    def test_trains_and_exports_onnx(self) -> None:
        split = DatasetSplit(
            train_features=torch.tensor(
                [
                    [0.0, 1.0, 0.0, 0.0, 1.0, 1.0, 0.0, 2.0, 0.0, 1.0, 0.0],
                    [0.0, 2.0, 0.0, 0.0, 1.0, 1.0, 0.0, 3.0, 1.0, 1.0, 0.0],
                    [0.0, 3.0, 0.0, 0.0, 1.0, 1.0, 0.0, 4.0, 2.0, 1.0, 0.0],
                    [0.0, 4.0, 0.0, 0.0, 1.0, 1.0, 0.0, 5.0, 3.0, 1.0, 0.0],
                ],
                dtype=torch.float32,
            ),
            train_labels=torch.tensor([1.0, 0.0, 1.0, 0.0]),
            val_features=torch.tensor(
                [
                    [0.0, 5.0, 0.0, 0.0, 1.0, 1.0, 0.0, 6.0, 4.0, 1.0, 0.0],
                    [0.0, 6.0, 0.0, 0.0, 1.0, 1.0, 0.0, 7.0, 5.0, 1.0, 0.0],
                ],
                dtype=torch.float32,
            ),
            val_labels=torch.tensor([1.0, 0.0]),
            feature_names=TEST_FEATURE_NAMES,
        )
        config = TrainConfig(
            epochs=1,
            batch_size=2,
            learning_rate=1e-3,
            weight_decay=0.0,
            hidden_size=4,
            hidden_layers=1,
            seed=1,
            device="cpu",
        )
        model, metrics = train_model(split, config)
        self.assertEqual(len(metrics), 1)
        self.assertTrue(metrics[0].is_best)

        with tempfile.TemporaryDirectory() as tmp:
            output_path = Path(tmp) / "scorer.onnx"
            export_onnx(model, output_path, TEST_FEATURE_NAMES)
            self.assertTrue(output_path.exists())
            contract = json.loads(feature_contract_path(output_path).read_text())
            self.assertEqual(contract["schema"], FEATURE_CONTRACT_SCHEMA)
            self.assertEqual(contract["input_features"], TEST_FEATURE_NAMES)


if __name__ == "__main__":
    unittest.main()
