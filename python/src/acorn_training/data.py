from __future__ import annotations

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
SHARD_SCHEMA = "acorn-training-shards-v1"
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
    groups: list[str | int] | torch.Tensor
    metadata: Counter[str]
    goal_buckets: torch.Tensor | None = None

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
    goal_bucket: int | None
    policy: str
    outcome: str


def _search_group(record: dict) -> str:
    # Keep every policy/skip variant of the same goal in the same split.
    # Otherwise validation can measure memorization across near-duplicate runs.
    return "\t".join(
        [
            str(record.get("module", "")),
            str(record.get("goal", "")),
        ]
    )


def _goal_bucket(record: dict) -> int | None:
    bucket = record.get("goal_bucket")
    if isinstance(bucket, int) and 0 <= bucket < 100:
        return bucket
    return None


def _iter_records(path: Path) -> Iterable[dict]:
    if not path.name.endswith(".jsonl.zst"):
        raise ValueError(f"{path}: trace files must end in .jsonl.zst")
    with zstandard.open(path, "rt") as f:
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
    raise ValueError(f"{trace_path}: trace files must end in .jsonl.zst")


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
                goal_bucket=_goal_bucket(record),
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
    rows_with_goal_bucket = sum(row.goal_bucket is not None for row in rows)
    metadata["rows_with_goal_bucket"] = rows_with_goal_bucket
    metadata["loaded_records"] = len(rows)
    metadata["scanned_records"] = scanned_records
    goal_buckets = None
    if rows_with_goal_bucket == len(rows):
        goal_buckets = torch.tensor([row.goal_bucket for row in rows], dtype=torch.long)

    return TraceDataset(
        features=torch.tensor([row.features for row in rows], dtype=torch.float32),
        labels=torch.tensor([row.label for row in rows], dtype=torch.float32),
        feature_names=output_feature_names or [],
        groups=[row.group for row in rows],
        metadata=metadata,
        goal_buckets=goal_buckets,
    )


def load_shard_dataset(
    shard_dirs: list[Path],
    *,
    max_records: int | None = None,
) -> TraceDataset:
    if max_records is not None and max_records <= 0:
        raise ValueError("max_records must be positive")

    feature_names: list[str] | None = None
    features: list[torch.Tensor] = []
    labels: list[torch.Tensor] = []
    group_ids: list[torch.Tensor] = []
    goal_bucket_tensors: list[torch.Tensor] = []
    metadata: Counter[str] = Counter()
    loaded_records = 0
    total_source_records = 0
    group_offset = 0
    missing_goal_buckets = False
    policy_names: list[str] = []
    outcome_names: list[str] = []

    for shard_dir in shard_dirs:
        manifest_path = shard_dir / "manifest.json"
        with manifest_path.open("r") as f:
            manifest = json.load(f)
        if manifest.get("schema") != SHARD_SCHEMA:
            raise ValueError(
                f"{manifest_path}: expected schema {SHARD_SCHEMA!r}, "
                f"got {manifest.get('schema')!r}"
            )
        manifest_features = manifest.get("feature_names")
        if not isinstance(manifest_features, list) or not all(
            isinstance(name, str) for name in manifest_features
        ):
            raise ValueError(f"{manifest_path}: expected string feature_names")
        if feature_names is None:
            feature_names = list(manifest_features)
        elif feature_names != manifest_features:
            raise ValueError("all shard directories must use the same feature names")

        manifest_groups = manifest.get("group_names", [])
        if not isinstance(manifest_groups, list):
            raise ValueError(f"{manifest_path}: expected group_names list")
        policy_names = [str(name) for name in manifest.get("policy_names", [])]
        outcome_names = [str(name) for name in manifest.get("outcome_names", [])]

        for shard in manifest.get("shards", []):
            if not isinstance(shard, dict) or not isinstance(shard.get("path"), str):
                raise ValueError(f"{manifest_path}: invalid shard entry")
            data = torch.load(shard_dir / shard["path"], weights_only=False)
            if data.get("schema") != SHARD_SCHEMA:
                raise ValueError(f"{shard_dir / shard['path']}: invalid shard schema")
            shard_features = data["features"].to(dtype=torch.float32)
            shard_labels = data["labels"].to(dtype=torch.float32)
            shard_groups = data["group_ids"].to(dtype=torch.long) + group_offset
            shard_goal_buckets = data.get("goal_buckets")
            if shard_goal_buckets is not None:
                shard_goal_buckets = shard_goal_buckets.to(dtype=torch.long)
            else:
                missing_goal_buckets = True
            row_count = int(shard_labels.numel())
            if int(shard_features.shape[0]) != row_count:
                raise ValueError(f"{shard_dir / shard['path']}: inconsistent row count")

            if max_records is not None:
                remaining = max_records - loaded_records
                if remaining <= 0:
                    break
                if row_count > remaining:
                    shard_features = shard_features[:remaining]
                    shard_labels = shard_labels[:remaining]
                    shard_groups = shard_groups[:remaining]
                    if shard_goal_buckets is not None:
                        shard_goal_buckets = shard_goal_buckets[:remaining]
                    row_count = remaining

            features.append(shard_features)
            labels.append(shard_labels)
            group_ids.append(shard_groups)
            if shard_goal_buckets is not None:
                goal_bucket_tensors.append(shard_goal_buckets)
            loaded_records += row_count
            if "policy_ids" in data:
                policy_tensor = data["policy_ids"][:row_count]
                for policy_id, count in zip(*torch.unique(policy_tensor, return_counts=True)):
                    index = int(policy_id.item())
                    name = policy_names[index] if index < len(policy_names) else str(index)
                    metadata[f"policy:{name}"] += int(count.item())
            if "outcome_ids" in data:
                outcome_tensor = data["outcome_ids"][:row_count]
                for outcome_id, count in zip(*torch.unique(outcome_tensor, return_counts=True)):
                    index = int(outcome_id.item())
                    name = outcome_names[index] if index < len(outcome_names) else str(index)
                    metadata[f"outcome:{name}"] += int(count.item())
        total_source_records += int(manifest.get("scanned_records", 0))
        group_offset += len(manifest_groups)
        if max_records is not None and loaded_records >= max_records:
            break

    if not labels:
        raise ValueError("no shard records loaded")

    metadata["loaded_records"] = loaded_records
    metadata["source_records"] = total_source_records
    goal_buckets = None
    if not missing_goal_buckets and goal_bucket_tensors:
        candidate_goal_buckets = torch.cat(goal_bucket_tensors, dim=0)
        if bool(torch.all((0 <= candidate_goal_buckets) & (candidate_goal_buckets < 100))):
            goal_buckets = candidate_goal_buckets
            metadata["rows_with_goal_bucket"] = loaded_records
    return TraceDataset(
        features=torch.cat(features, dim=0),
        labels=torch.cat(labels, dim=0),
        feature_names=feature_names or [],
        groups=torch.cat(group_ids, dim=0),
        metadata=metadata,
        goal_buckets=goal_buckets,
    )


def split_by_search(
    dataset: TraceDataset,
    *,
    validation_fraction: float,
    seed: int,
) -> DatasetSplit:
    if not 0.0 < validation_fraction < 1.0:
        raise ValueError("validation_fraction must be between 0 and 1")

    rng = random.Random(seed)
    if dataset.goal_buckets is not None:
        goal_buckets = dataset.goal_buckets.to(dtype=torch.long)
        first_validation_bucket = int(round((1.0 - validation_fraction) * 100.0))
        first_validation_bucket = max(1, min(99, first_validation_bucket))
        val_mask = goal_buckets >= first_validation_bucket
        val_tensor = val_mask.nonzero(as_tuple=False).flatten()
        train_tensor = (~val_mask).nonzero(as_tuple=False).flatten()
    elif isinstance(dataset.groups, torch.Tensor):
        group_ids = dataset.groups.to(dtype=torch.long)
        unique_groups = torch.unique(group_ids).tolist()
        rng.shuffle(unique_groups)
        val_group_count = max(1, int(round(len(unique_groups) * validation_fraction)))
        if val_group_count >= len(unique_groups):
            val_group_count = max(1, len(unique_groups) - 1)
        val_groups = torch.tensor(unique_groups[:val_group_count], dtype=torch.long)
        lookup = torch.zeros(int(group_ids.max().item()) + 1, dtype=torch.bool)
        lookup[val_groups] = True
        val_mask = lookup.index_select(0, group_ids)
        val_tensor = val_mask.nonzero(as_tuple=False).flatten()
        train_tensor = (~val_mask).nonzero(as_tuple=False).flatten()
    else:
        unique_groups = sorted(set(dataset.groups))
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
        train_tensor = torch.tensor(train_indices, dtype=torch.long)
        val_tensor = torch.tensor(val_indices, dtype=torch.long)

    if train_tensor.numel() == 0 or val_tensor.numel() == 0:
        raise ValueError("split produced an empty train or validation set")
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
