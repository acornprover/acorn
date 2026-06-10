from __future__ import annotations

import gzip
import json
import random
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import torch
import zstandard
from torch.utils.data import DataLoader, TensorDataset

TRACE_SCHEMA = "acorn-activated-step-trace-v2"
LEGACY_FEATURE_NAMES = [
    "is_contradiction",
    "atom_count",
    "is_counterfactual",
    "is_hypothetical",
    "is_factual",
    "is_assumption",
    "is_negated_goal",
    "proof_size",
    "depth",
]


@dataclass(frozen=True)
class TraceDataset:
    features: torch.Tensor
    labels: torch.Tensor
    feature_names: list[str]
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
    feature_names: list[str]


@dataclass(frozen=True)
class _LoadedRow:
    features: list[float]
    label: float
    group: str
    policy: str
    outcome: str


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
    if path.suffix == ".zst":
        opener = zstandard.open
    elif path.suffix == ".gz":
        opener = gzip.open
    else:
        opener = Path.open
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


def trace_metadata_path(trace_path: Path) -> Path:
    name = trace_path.name
    if name.endswith(".jsonl.zst"):
        return trace_path.with_name(f"{name[:-len('.jsonl.zst')]}.meta.json")
    if name.endswith(".jsonl.gz"):
        return trace_path.with_name(f"{name[:-len('.jsonl.gz')]}.meta.json")
    if name.endswith(".jsonl"):
        return trace_path.with_name(f"{name[:-len('.jsonl')]}.meta.json")
    return trace_path.with_suffix(".meta.json")


def _load_feature_names(path: Path) -> list[str]:
    metadata_path = trace_metadata_path(path)
    if metadata_path.exists():
        with metadata_path.open("r") as f:
            metadata = json.load(f)
        if metadata.get("schema") != TRACE_SCHEMA:
            raise ValueError(
                f"{metadata_path}: expected schema {TRACE_SCHEMA!r}, "
                f"got {metadata.get('schema')!r}"
            )
        feature_names = metadata.get("feature_vector")
        if not isinstance(feature_names, list) or not all(
            isinstance(name, str) for name in feature_names
        ):
            raise ValueError(f"{metadata_path}: expected string feature_vector names")
        return feature_names

    return LEGACY_FEATURE_NAMES.copy()


def _selected_indices(
    path: Path,
    trace_feature_names: list[str],
    selected_feature_names: list[str] | None,
) -> tuple[list[str], list[int]]:
    feature_names = selected_feature_names or trace_feature_names
    positions = {name: i for i, name in enumerate(trace_feature_names)}
    missing = [name for name in feature_names if name not in positions]
    if missing:
        raise ValueError(f"{path}: trace metadata is missing features: {', '.join(missing)}")
    return list(feature_names), [positions[name] for name in feature_names]


def load_trace_dataset(
    paths: list[Path],
    *,
    feature_names: list[str] | None = None,
    max_records: int | None = None,
    sample_records: int | None = None,
    seed: int = 42,
) -> TraceDataset:
    if max_records is not None and max_records <= 0:
        raise ValueError("max_records must be positive")
    if sample_records is not None and sample_records <= 0:
        raise ValueError("sample_records must be positive")

    rows: list[_LoadedRow] = []
    rng = random.Random(seed)
    scanned_records = 0
    output_feature_names: list[str] | None = None

    for path in paths:
        trace_feature_names = _load_feature_names(path)
        selected_names, indices = _selected_indices(path, trace_feature_names, feature_names)
        if output_feature_names is None:
            output_feature_names = selected_names
        elif output_feature_names != selected_names:
            raise ValueError("all trace files must use the same selected feature names")

        for record in _iter_records(path):
            vector = record.get("feature_vector")
            if not isinstance(vector, list) or len(vector) != len(trace_feature_names):
                raise ValueError(
                    f"{path}: expected feature_vector with {len(trace_feature_names)} values"
                )
            label = record.get("used_in_final_proof")
            if not isinstance(label, bool):
                raise ValueError(f"{path}: expected boolean used_in_final_proof")

            row = _LoadedRow(
                features=[float(vector[i]) for i in indices],
                label=float(label),
                group=_search_group(record),
                policy=str(record.get("policy", "")),
                outcome=str(record.get("outcome", "")),
            )
            scanned_records += 1

            if sample_records is None:
                rows.append(row)
            elif len(rows) < sample_records:
                rows.append(row)
            else:
                replacement_index = rng.randrange(scanned_records)
                if replacement_index < sample_records:
                    rows[replacement_index] = row

            if max_records is not None and scanned_records >= max_records:
                break
        if max_records is not None and scanned_records >= max_records:
            break

    if not rows:
        raise ValueError("no trace records loaded")

    metadata: Counter[str] = Counter()
    for row in rows:
        metadata[f"policy:{row.policy}"] += 1
        metadata[f"outcome:{row.outcome}"] += 1
    metadata["loaded_records"] = len(rows)
    metadata["scanned_records"] = scanned_records

    return TraceDataset(
        features=torch.tensor([row.features for row in rows], dtype=torch.float32),
        labels=torch.tensor([row.label for row in rows], dtype=torch.float32),
        feature_names=output_feature_names or [],
        groups=[row.group for row in rows],
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
        feature_names=dataset.feature_names,
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
