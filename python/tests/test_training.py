from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import torch

from acorn_training.data import (
    TRACE_SCHEMA,
    DatasetSplit,
    load_trace_dataset,
    split_by_search,
)
from acorn_training.model import ProbabilityScorer, ScorerNet
from acorn_training.train import TrainConfig, export_onnx, train_model


def _record(goal: str, index: int, label: bool) -> dict:
    return {
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
        ],
        "features": {},
    }


class TrainingDataTest(unittest.TestCase):
    def test_loads_trace_and_splits_by_search(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trace.jsonl"
            rows = [
                _record("a", 0, True),
                _record("a", 1, False),
                _record("b", 0, True),
                _record("b", 1, False),
            ]
            path.write_text("\n".join(json.dumps(row) for row in rows) + "\n")

            dataset = load_trace_dataset([path])
            self.assertEqual(dataset.num_examples, 4)
            self.assertEqual(dataset.num_positive, 2)

            split = split_by_search(dataset, validation_fraction=0.5, seed=1)
            self.assertEqual(split.train_features.shape[1], 9)
            self.assertEqual(split.val_features.shape[1], 9)
            self.assertEqual(
                split.train_labels.numel() + split.val_labels.numel(),
                4,
            )

    def test_model_exports_probability_shape(self) -> None:
        features = torch.randn(8, 9)
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
                    [0.0, 1.0, 0.0, 0.0, 1.0, 1.0, 0.0, 2.0, 0.0],
                    [0.0, 2.0, 0.0, 0.0, 1.0, 1.0, 0.0, 3.0, 1.0],
                    [0.0, 3.0, 0.0, 0.0, 1.0, 1.0, 0.0, 4.0, 2.0],
                    [0.0, 4.0, 0.0, 0.0, 1.0, 1.0, 0.0, 5.0, 3.0],
                ],
                dtype=torch.float32,
            ),
            train_labels=torch.tensor([1.0, 0.0, 1.0, 0.0]),
            val_features=torch.tensor(
                [
                    [0.0, 5.0, 0.0, 0.0, 1.0, 1.0, 0.0, 6.0, 4.0],
                    [0.0, 6.0, 0.0, 0.0, 1.0, 1.0, 0.0, 7.0, 5.0],
                ],
                dtype=torch.float32,
            ),
            val_labels=torch.tensor([1.0, 0.0]),
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

        with tempfile.TemporaryDirectory() as tmp:
            output_path = Path(tmp) / "scorer.onnx"
            export_onnx(model, output_path)
            self.assertTrue(output_path.exists())


if __name__ == "__main__":
    unittest.main()
