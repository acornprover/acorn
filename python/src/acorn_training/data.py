from __future__ import annotations

import gzip
import json
import random
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import torch
from torch.utils.data import DataLoader, TensorDataset

TRACE_SCHEMA = "acorn-activated-step-trace-v2"
NUM_FEATURES = 9


@dataclass(frozen=True)
class TraceDataset:
    features: torch.Tensor
    labels: torch.Tensor
    groups: list[str]
    metadata: Counter[str]

    @property
    def num_examples(self) -> int:
        return int(self.labels.numel())

    @property
    def num_positive(self) -> int:
        return int(self.labels.sum().item())

    @property
    def num_negative(self) -> int:
        return self.num_examples - self.num_positive

    @property
    def positive_rate(self) -> float:
        if self.num_examples == 0:
            return 0.0
        return self.num_positive / self.num_examples


@dataclass(frozen=True)
class DatasetSplit:
    train_features: torch.Tensor
    train_labels: torch.Tensor
    val_features: torch.Tensor
    val_labels: torch.Tensor


def _search_group(record: dict) -> str:
    return "\t".join(
        [
            str(record.get("module", "")),
            str(record.get("goal", "")),
            str(record.get("skip", "")),
            str(record.get("policy", "")),
        ]
    )


def _iter_records(path: Path) -> Iterable[dict]:
    opener = gzip.open if path.suffix == ".gz" else Path.open
    with opener(path, "rt") as f:
        for line_number, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as e:
                raise ValueError(f"{path}:{line_number}: invalid JSON: {e}") from e
            if record.get("schema") != TRACE_SCHEMA:
                raise ValueError(
                    f"{path}:{line_number}: expected schema {TRACE_SCHEMA!r}, "
                    f"got {record.get('schema')!r}"
                )
            yield record


def load_trace_dataset(
    paths: list[Path],
    *,
    max_records: int | None = None,
) -> TraceDataset:
    feature_rows: list[list[float]] = []
    labels: list[float] = []
    groups: list[str] = []
    metadata: Counter[str] = Counter()

    for path in paths:
        for record in _iter_records(path):
            vector = record.get("feature_vector")
            if not isinstance(vector, list) or len(vector) != NUM_FEATURES:
                raise ValueError(
                    f"{path}: expected feature_vector with {NUM_FEATURES} values"
                )
            label = record.get("used_in_final_proof")
            if not isinstance(label, bool):
                raise ValueError(f"{path}: expected boolean used_in_final_proof")

            feature_rows.append([float(value) for value in vector])
            labels.append(float(label))
            groups.append(_search_group(record))
            metadata[f"policy:{record.get('policy', '')}"] += 1
            metadata[f"outcome:{record.get('outcome', '')}"] += 1

            if max_records is not None and len(labels) >= max_records:
                break
        if max_records is not None and len(labels) >= max_records:
            break

    if not labels:
        raise ValueError("no trace records loaded")

    return TraceDataset(
        features=torch.tensor(feature_rows, dtype=torch.float32),
        labels=torch.tensor(labels, dtype=torch.float32),
        groups=groups,
        metadata=metadata,
    )


def split_by_search(
    dataset: TraceDataset,
    *,
    validation_fraction: float,
    seed: int,
) -> DatasetSplit:
    if not 0.0 < validation_fraction < 1.0:
        raise ValueError("validation_fraction must be between 0 and 1")

    unique_groups = sorted(set(dataset.groups))
    rng = random.Random(seed)
    rng.shuffle(unique_groups)
    val_group_count = max(1, int(round(len(unique_groups) * validation_fraction)))
    if val_group_count >= len(unique_groups):
        val_group_count = max(1, len(unique_groups) - 1)
    val_groups = set(unique_groups[:val_group_count])

    val_indices = [
        i for i, group in enumerate(dataset.groups) if group in val_groups
    ]
    train_indices = [
        i for i, group in enumerate(dataset.groups) if group not in val_groups
    ]
    if not train_indices or not val_indices:
        raise ValueError("split produced an empty train or validation set")

    train_tensor = torch.tensor(train_indices, dtype=torch.long)
    val_tensor = torch.tensor(val_indices, dtype=torch.long)
    return DatasetSplit(
        train_features=dataset.features.index_select(0, train_tensor),
        train_labels=dataset.labels.index_select(0, train_tensor),
        val_features=dataset.features.index_select(0, val_tensor),
        val_labels=dataset.labels.index_select(0, val_tensor),
    )


def make_loader(
    features: torch.Tensor,
    labels: torch.Tensor,
    *,
    batch_size: int,
    shuffle: bool,
    seed: int,
) -> DataLoader:
    generator = torch.Generator()
    generator.manual_seed(seed)
    dataset = TensorDataset(features, labels)
    return DataLoader(
        dataset,
        batch_size=batch_size,
        shuffle=shuffle,
        generator=generator if shuffle else None,
    )
