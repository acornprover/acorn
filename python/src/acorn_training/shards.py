from __future__ import annotations

import json
import random
import shutil
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import torch

from .data import (
    TRACE_SCHEMA,
    _iter_records,
    _load_feature_names,
    _search_group,
    _selected_indices,
)

SHARD_SCHEMA = "acorn-training-shards-v1"


@dataclass(frozen=True)
class ShardBuildConfig:
    trace_paths: list[Path]
    out_dir: Path
    feature_names: list[str] | None = None
    shard_rows: int = 1_000_000
    sample_records: int | None = None
    max_records: int | None = None
    seed: int = 42
    overwrite: bool = False
    progress_interval: int = 1_000_000


@dataclass(frozen=True)
class ShardBuildSummary:
    out_dir: Path
    scanned_records: int
    written_records: int
    positive_records: int
    shard_count: int


@dataclass(frozen=True)
class _TraceSelection:
    path: Path
    trace_feature_names: list[str]
    feature_names: list[str]
    indices: list[int]
    source_trace_id: int


@dataclass(frozen=True)
class _Row:
    features: list[float]
    label: int
    group_id: int
    policy_id: int
    outcome_id: int
    activation_index: int
    source_trace_id: int


class _IdMap:
    def __init__(self) -> None:
        self.names: list[str] = []
        self.positions: dict[str, int] = {}

    def id_for(self, value: str) -> int:
        if value in self.positions:
            return self.positions[value]
        next_id = len(self.names)
        self.names.append(value)
        self.positions[value] = next_id
        return next_id


class _ShardWriter:
    def __init__(
        self,
        out_dir: Path,
        feature_names: list[str],
        *,
        shard_rows: int,
    ) -> None:
        self.out_dir = out_dir
        self.feature_names = feature_names
        self.shard_rows = shard_rows
        self.shards: list[dict] = []
        self.feature_rows: list[list[float]] = []
        self.labels: list[int] = []
        self.group_ids: list[int] = []
        self.policy_ids: list[int] = []
        self.outcome_ids: list[int] = []
        self.activation_indices: list[int] = []
        self.source_trace_ids: list[int] = []

    def push(self, row: _Row) -> None:
        self.feature_rows.append(row.features)
        self.labels.append(row.label)
        self.group_ids.append(row.group_id)
        self.policy_ids.append(row.policy_id)
        self.outcome_ids.append(row.outcome_id)
        self.activation_indices.append(row.activation_index)
        self.source_trace_ids.append(row.source_trace_id)
        if len(self.labels) >= self.shard_rows:
            self.flush()

    def flush(self) -> None:
        if not self.labels:
            return
        shard_index = len(self.shards)
        shard_name = f"shard-{shard_index:06d}.pt"
        shard_path = self.out_dir / shard_name
        row_count = len(self.labels)
        torch.save(
            {
                "schema": SHARD_SCHEMA,
                "features": torch.tensor(self.feature_rows, dtype=torch.float32),
                "labels": torch.tensor(self.labels, dtype=torch.uint8),
                "group_ids": torch.tensor(self.group_ids, dtype=torch.int64),
                "policy_ids": torch.tensor(self.policy_ids, dtype=torch.int16),
                "outcome_ids": torch.tensor(self.outcome_ids, dtype=torch.int16),
                "activation_index": torch.tensor(self.activation_indices, dtype=torch.int32),
                "source_trace_ids": torch.tensor(self.source_trace_ids, dtype=torch.int16),
            },
            shard_path,
        )
        self.shards.append({"path": shard_name, "rows": row_count})
        self.feature_rows = []
        self.labels = []
        self.group_ids = []
        self.policy_ids = []
        self.outcome_ids = []
        self.activation_indices = []
        self.source_trace_ids = []


class _Reservoir:
    def __init__(self, capacity: int, feature_count: int, seed: int) -> None:
        self.capacity = capacity
        self.feature_count = feature_count
        self.rng = random.Random(seed)
        self.features = torch.empty((capacity, feature_count), dtype=torch.float32)
        self.labels = torch.empty(capacity, dtype=torch.uint8)
        self.group_ids = torch.empty(capacity, dtype=torch.int64)
        self.policy_ids = torch.empty(capacity, dtype=torch.int16)
        self.outcome_ids = torch.empty(capacity, dtype=torch.int16)
        self.activation_indices = torch.empty(capacity, dtype=torch.int32)
        self.source_trace_ids = torch.empty(capacity, dtype=torch.int16)
        self.loaded = 0
        self.scanned = 0

    def consider(self, row: _Row) -> None:
        self.scanned += 1
        if self.loaded < self.capacity:
            slot = self.loaded
            self.loaded += 1
        else:
            slot = self.rng.randrange(self.scanned)
            if slot >= self.capacity:
                return
        self.features[slot] = torch.tensor(row.features, dtype=torch.float32)
        self.labels[slot] = row.label
        self.group_ids[slot] = row.group_id
        self.policy_ids[slot] = row.policy_id
        self.outcome_ids[slot] = row.outcome_id
        self.activation_indices[slot] = row.activation_index
        self.source_trace_ids[slot] = row.source_trace_id

    def write_shards(self, out_dir: Path, *, shard_rows: int, seed: int) -> list[dict]:
        shards: list[dict] = []
        generator = torch.Generator()
        generator.manual_seed(seed)
        order = torch.randperm(self.loaded, generator=generator)
        for shard_index, start in enumerate(range(0, self.loaded, shard_rows)):
            indices = order[start : start + shard_rows]
            shard_name = f"shard-{shard_index:06d}.pt"
            shard_path = out_dir / shard_name
            torch.save(
                {
                    "schema": SHARD_SCHEMA,
                    "features": self.features.index_select(0, indices),
                    "labels": self.labels.index_select(0, indices),
                    "group_ids": self.group_ids.index_select(0, indices),
                    "policy_ids": self.policy_ids.index_select(0, indices),
                    "outcome_ids": self.outcome_ids.index_select(0, indices),
                    "activation_index": self.activation_indices.index_select(0, indices),
                    "source_trace_ids": self.source_trace_ids.index_select(0, indices),
                },
                shard_path,
            )
            shards.append({"path": shard_name, "rows": int(indices.numel())})
        return shards


def _prepare_out_dir(path: Path, *, overwrite: bool) -> None:
    if path.exists():
        if not overwrite:
            if any(path.iterdir()):
                raise ValueError(f"output directory already exists and is not empty: {path}")
        else:
            shutil.rmtree(path)
    path.mkdir(parents=True, exist_ok=True)


def _trace_selections(
    paths: list[Path],
    selected_feature_names: list[str] | None,
) -> tuple[list[_TraceSelection], list[str]]:
    selections: list[_TraceSelection] = []
    output_feature_names: list[str] | None = None
    for source_trace_id, path in enumerate(paths):
        trace_feature_names = _load_feature_names(path)
        feature_names, indices = _selected_indices(path, trace_feature_names, selected_feature_names)
        if output_feature_names is None:
            output_feature_names = feature_names
        elif output_feature_names != feature_names:
            raise ValueError("all trace files must use the same selected feature names")
        selections.append(
            _TraceSelection(
                path=path,
                trace_feature_names=trace_feature_names,
                feature_names=feature_names,
                indices=indices,
                source_trace_id=source_trace_id,
            )
        )
    if output_feature_names is None:
        raise ValueError("no trace paths provided")
    return selections, output_feature_names


def _row_from_record(
    record: dict,
    selection: _TraceSelection,
    *,
    groups: _IdMap,
    policies: _IdMap,
    outcomes: _IdMap,
) -> _Row:
    vector = record.get("feature_vector")
    if not isinstance(vector, list) or len(vector) != len(selection.trace_feature_names):
        raise ValueError(
            f"{selection.path}: expected feature_vector with "
            f"{len(selection.trace_feature_names)} values"
        )
    label = record.get("used_in_final_proof")
    if not isinstance(label, bool):
        raise ValueError(f"{selection.path}: expected boolean used_in_final_proof")
    activation_index = record.get("activation_index", -1)
    if not isinstance(activation_index, int):
        activation_index = -1
    policy = str(record.get("policy", ""))
    outcome = str(record.get("outcome", ""))
    return _Row(
        features=[float(vector[i]) for i in selection.indices],
        label=int(label),
        group_id=groups.id_for(_search_group(record)),
        policy_id=policies.id_for(policy),
        outcome_id=outcomes.id_for(outcome),
        activation_index=activation_index,
        source_trace_id=selection.source_trace_id,
    )


def _write_manifest(
    out_dir: Path,
    *,
    config: ShardBuildConfig,
    feature_names: list[str],
    source_traces: list[Path],
    source_trace_rows: list[int],
    groups: _IdMap,
    policies: _IdMap,
    outcomes: _IdMap,
    shards: list[dict],
    scanned_records: int,
    written_records: int,
    positive_records: int,
    sampled: bool,
    source_counter: Counter[str],
) -> None:
    manifest = {
        "schema": SHARD_SCHEMA,
        "source_schema": TRACE_SCHEMA,
        "feature_names": feature_names,
        "source_traces": [str(path) for path in source_traces],
        "source_trace_rows": source_trace_rows,
        "policy_names": policies.names,
        "outcome_names": outcomes.names,
        "group_names": groups.names,
        "shards": shards,
        "shard_rows": config.shard_rows,
        "scanned_records": scanned_records,
        "written_records": written_records,
        "positive_records": positive_records,
        "sample_records": config.sample_records,
        "max_records": config.max_records,
        "seed": config.seed,
        "sampled": sampled,
        "source_counts": dict(source_counter),
    }
    with (out_dir / "manifest.json").open("w") as f:
        json.dump(manifest, f, indent=2)
        f.write("\n")


def _validate_config(config: ShardBuildConfig) -> None:
    if config.shard_rows <= 0:
        raise ValueError("shard_rows must be positive")
    if config.sample_records is not None and config.sample_records <= 0:
        raise ValueError("sample_records must be positive")
    if config.max_records is not None and config.max_records <= 0:
        raise ValueError("max_records must be positive")
    if config.progress_interval <= 0:
        raise ValueError("progress_interval must be positive")


def build_shards(
    config: ShardBuildConfig,
    *,
    progress: Callable[[str], None] | None = print,
) -> ShardBuildSummary:
    _validate_config(config)
    _prepare_out_dir(config.out_dir, overwrite=config.overwrite)
    selections, feature_names = _trace_selections(config.trace_paths, config.feature_names)
    groups = _IdMap()
    policies = _IdMap()
    outcomes = _IdMap()
    source_counter: Counter[str] = Counter()
    source_trace_rows = [0 for _ in selections]
    scanned_records = 0
    positive_records = 0
    last_progress = 0
    started = time.monotonic()

    writer: _ShardWriter | None = None
    reservoir: _Reservoir | None = None
    if config.sample_records is None:
        writer = _ShardWriter(config.out_dir, feature_names, shard_rows=config.shard_rows)
    else:
        reservoir = _Reservoir(config.sample_records, len(feature_names), config.seed)

    def maybe_progress(force: bool = False) -> None:
        nonlocal last_progress
        if progress is None:
            return
        if force or scanned_records - last_progress >= config.progress_interval:
            elapsed = max(0.001, time.monotonic() - started)
            rate = scanned_records / elapsed
            if reservoir is None:
                loaded = scanned_records
            else:
                loaded = reservoir.loaded
            progress(
                f"scanned={scanned_records} loaded={loaded} "
                f"rate={rate:.0f} rows/s shards={len(writer.shards) if writer else 0}"
            )
            last_progress = scanned_records

    for selection in selections:
        if progress is not None:
            progress(f"reading {selection.path}")
        for record in _iter_records(selection.path):
            row = _row_from_record(
                record,
                selection,
                groups=groups,
                policies=policies,
                outcomes=outcomes,
            )
            scanned_records += 1
            source_trace_rows[selection.source_trace_id] += 1
            source_counter[f"policy:{policies.names[row.policy_id]}"] += 1
            source_counter[f"outcome:{outcomes.names[row.outcome_id]}"] += 1
            positive_records += row.label

            if writer is not None:
                writer.push(row)
            else:
                assert reservoir is not None
                reservoir.consider(row)

            maybe_progress()
            if config.max_records is not None and scanned_records >= config.max_records:
                break
        if config.max_records is not None and scanned_records >= config.max_records:
            break

    if scanned_records == 0:
        raise ValueError("no trace records loaded")

    if writer is not None:
        writer.flush()
        shards = writer.shards
        written_records = scanned_records
    else:
        assert reservoir is not None
        if progress is not None:
            progress("writing sampled shards")
        positive_records = int(reservoir.labels[: reservoir.loaded].sum().item())
        shards = reservoir.write_shards(config.out_dir, shard_rows=config.shard_rows, seed=config.seed)
        written_records = reservoir.loaded

    _write_manifest(
        config.out_dir,
        config=config,
        feature_names=feature_names,
        source_traces=config.trace_paths,
        source_trace_rows=source_trace_rows,
        groups=groups,
        policies=policies,
        outcomes=outcomes,
        shards=shards,
        scanned_records=scanned_records,
        written_records=written_records,
        positive_records=positive_records,
        sampled=config.sample_records is not None,
        source_counter=source_counter,
    )
    maybe_progress(force=True)
    return ShardBuildSummary(
        out_dir=config.out_dir,
        scanned_records=scanned_records,
        written_records=written_records,
        positive_records=positive_records,
        shard_count=len(shards),
    )
