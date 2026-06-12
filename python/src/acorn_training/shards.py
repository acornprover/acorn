from __future__ import annotations

import json
import random
import shutil
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import torch

from .data import (
    TRACE_SCHEMA,
    _iter_records,
    _goal_bucket,
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
    max_negative_records: int | None = None
    max_records: int | None = None
    seed: int = 42
    overwrite: bool = False
    progress_interval: int = 1_000_000
    workers: int = 1


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
class _WorkerResult:
    source_trace_id: int
    scanned_records: int
    written_records: int
    positive_records: int
    source_trace_rows: int
    source_counter: Counter[str]
    group_names: list[str]
    policy_names: list[str]
    outcome_names: list[str]
    shards: list[dict]
    out_dir: Path


@dataclass(frozen=True)
class _Row:
    features: list[float]
    label: int
    group_id: int
    goal_bucket: int
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
        self.goal_buckets: list[int] = []
        self.policy_ids: list[int] = []
        self.outcome_ids: list[int] = []
        self.activation_indices: list[int] = []
        self.source_trace_ids: list[int] = []

    def push(self, row: _Row) -> None:
        self.feature_rows.append(row.features)
        self.labels.append(row.label)
        self.group_ids.append(row.group_id)
        self.goal_buckets.append(row.goal_bucket)
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
                "goal_buckets": torch.tensor(self.goal_buckets, dtype=torch.int16),
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
        self.goal_buckets = []
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
        self.goal_buckets = torch.empty(capacity, dtype=torch.int16)
        self.policy_ids = torch.empty(capacity, dtype=torch.int16)
        self.outcome_ids = torch.empty(capacity, dtype=torch.int16)
        self.activation_indices = torch.empty(capacity, dtype=torch.int32)
        self.source_trace_ids = torch.empty(capacity, dtype=torch.int16)
        self.loaded = 0
        self.scanned = 0

    def choose_slot(self) -> int | None:
        self.scanned += 1
        if self.loaded < self.capacity:
            slot = self.loaded
            self.loaded += 1
        else:
            slot = self.rng.randrange(self.scanned)
            if slot >= self.capacity:
                return None
        return slot

    def store(self, slot: int, row: _Row) -> None:
        self.features[slot] = torch.tensor(row.features, dtype=torch.float32)
        self.labels[slot] = row.label
        self.group_ids[slot] = row.group_id
        self.goal_buckets[slot] = row.goal_bucket
        self.policy_ids[slot] = row.policy_id
        self.outcome_ids[slot] = row.outcome_id
        self.activation_indices[slot] = row.activation_index
        self.source_trace_ids[slot] = row.source_trace_id

    def consider(self, row: _Row) -> None:
        slot = self.choose_slot()
        if slot is not None:
            self.store(slot, row)

    def write_shards(
        self,
        out_dir: Path,
        *,
        shard_rows: int,
        seed: int,
        start_index: int = 0,
    ) -> list[dict]:
        shards: list[dict] = []
        generator = torch.Generator()
        generator.manual_seed(seed)
        order = torch.randperm(self.loaded, generator=generator)
        for offset, start in enumerate(range(0, self.loaded, shard_rows)):
            shard_index = start_index + offset
            indices = order[start : start + shard_rows]
            shard_name = f"shard-{shard_index:06d}.pt"
            shard_path = out_dir / shard_name
            torch.save(
                {
                    "schema": SHARD_SCHEMA,
                    "features": self.features.index_select(0, indices),
                    "labels": self.labels.index_select(0, indices),
                    "group_ids": self.group_ids.index_select(0, indices),
                    "goal_buckets": self.goal_buckets.index_select(0, indices),
                    "policy_ids": self.policy_ids.index_select(0, indices),
                    "outcome_ids": self.outcome_ids.index_select(0, indices),
                    "activation_index": self.activation_indices.index_select(0, indices),
                    "source_trace_ids": self.source_trace_ids.index_select(0, indices),
                },
                shard_path,
            )
            shards.append({"path": shard_name, "rows": int(indices.numel())})
        return shards


class _PositiveNegativeSampler:
    def __init__(
        self,
        out_dir: Path,
        feature_names: list[str],
        *,
        max_negative_records: int,
        shard_rows: int,
        seed: int,
    ) -> None:
        self.positive_writer = _ShardWriter(out_dir, feature_names, shard_rows=shard_rows)
        self.negative_reservoir = _Reservoir(max_negative_records, len(feature_names), seed)
        self.positive_records = 0

    @property
    def loaded(self) -> int:
        return self.positive_records + self.negative_reservoir.loaded

    @property
    def shard_count(self) -> int:
        return len(self.positive_writer.shards)

    def consider(self, row: _Row) -> None:
        if row.label:
            self.push_positive(row)
        else:
            slot = self.choose_negative_slot()
            if slot is not None:
                self.store_negative(slot, row)

    def push_positive(self, row: _Row) -> None:
        self.positive_writer.push(row)
        self.positive_records += 1

    def choose_negative_slot(self) -> int | None:
        return self.negative_reservoir.choose_slot()

    def store_negative(self, slot: int, row: _Row) -> None:
        self.negative_reservoir.store(slot, row)

    def write_shards(self, out_dir: Path, *, shard_rows: int, seed: int) -> list[dict]:
        self.positive_writer.flush()
        negative_shards = self.negative_reservoir.write_shards(
            out_dir,
            shard_rows=shard_rows,
            seed=seed,
            start_index=len(self.positive_writer.shards),
        )
        return self.positive_writer.shards + negative_shards


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
    goal_bucket = _goal_bucket(record)
    return _Row(
        features=[float(vector[i]) for i in selection.indices],
        label=int(label),
        group_id=groups.id_for(_search_group(record)),
        goal_bucket=goal_bucket if goal_bucket is not None else -1,
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
        "negative_records": written_records - positive_records,
        "sample_records": config.sample_records,
        "max_negative_records": config.max_negative_records,
        "max_records": config.max_records,
        "seed": config.seed,
        "workers": config.workers,
        "sampled": sampled,
        "sampling_mode": (
            "all_positives_file_stratified_max_negatives"
            if config.max_negative_records is not None
            and config.workers > 1
            and len(source_traces) > 1
            else "all_positives_max_negatives"
            if config.max_negative_records is not None
            else "uniform_reservoir"
            if config.sample_records is not None
            else "none"
        ),
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
    if config.max_negative_records is not None and config.max_negative_records <= 0:
        raise ValueError("max_negative_records must be positive")
    if config.sample_records is not None and config.max_negative_records is not None:
        raise ValueError("sample_records and max_negative_records are mutually exclusive")
    if config.max_records is not None and config.max_records <= 0:
        raise ValueError("max_records must be positive")
    if config.progress_interval <= 0:
        raise ValueError("progress_interval must be positive")
    if config.workers <= 0:
        raise ValueError("workers must be positive")


def _default_progress(message: str) -> None:
    print(message, flush=True)


def _allocate_counts(total: int, weights: list[int]) -> list[int]:
    weight_total = sum(weights)
    if weight_total <= 0:
        return [0 for _ in weights]
    raw = [total * weight / weight_total for weight in weights]
    counts = [int(value) for value in raw]
    remaining = total - sum(counts)
    order = sorted(
        range(len(weights)),
        key=lambda i: raw[i] - counts[i],
        reverse=True,
    )
    for index in order[:remaining]:
        counts[index] += 1
    return counts


def _run_positive_negative_worker(
    selection: _TraceSelection,
    feature_names: list[str],
    out_dir: Path,
    *,
    negative_quota: int,
    shard_rows: int,
    seed: int,
) -> _WorkerResult:
    groups = _IdMap()
    policies = _IdMap()
    outcomes = _IdMap()
    source_counter: Counter[str] = Counter()
    sampler = _PositiveNegativeSampler(
        out_dir,
        feature_names,
        max_negative_records=negative_quota,
        shard_rows=shard_rows,
        seed=seed,
    )
    scanned_records = 0
    positive_records = 0

    for record in _iter_records(selection.path):
        label = record.get("used_in_final_proof")
        if not isinstance(label, bool):
            raise ValueError(f"{selection.path}: expected boolean used_in_final_proof")
        policy = str(record.get("policy", ""))
        outcome = str(record.get("outcome", ""))
        scanned_records += 1
        source_counter[f"policy:{policy}"] += 1
        source_counter[f"outcome:{outcome}"] += 1

        if label:
            positive_records += 1
            row = _row_from_record(
                record,
                selection,
                groups=groups,
                policies=policies,
                outcomes=outcomes,
            )
            sampler.push_positive(row)
        else:
            slot = sampler.choose_negative_slot()
            if slot is not None:
                row = _row_from_record(
                    record,
                    selection,
                    groups=groups,
                    policies=policies,
                    outcomes=outcomes,
                )
                sampler.store_negative(slot, row)

    shards = sampler.write_shards(out_dir, shard_rows=shard_rows, seed=seed)
    return _WorkerResult(
        source_trace_id=selection.source_trace_id,
        scanned_records=scanned_records,
        written_records=sampler.loaded,
        positive_records=positive_records,
        source_trace_rows=scanned_records,
        source_counter=source_counter,
        group_names=groups.names,
        policy_names=policies.names,
        outcome_names=outcomes.names,
        shards=shards,
        out_dir=out_dir,
    )


def _remap_ids(ids: torch.Tensor, names: list[str], target: _IdMap, dtype: torch.dtype) -> torch.Tensor:
    if not names:
        return ids.to(dtype=dtype)
    remap = torch.tensor([target.id_for(name) for name in names], dtype=dtype)
    return remap.index_select(0, ids.to(dtype=torch.long))


def _merge_worker_shards(
    config: ShardBuildConfig,
    feature_names: list[str],
    results: list[_WorkerResult],
    groups: _IdMap,
    policies: _IdMap,
    outcomes: _IdMap,
) -> list[dict]:
    shards: list[dict] = []
    for result in results:
        for shard in result.shards:
            data = torch.load(result.out_dir / shard["path"], weights_only=False)
            if data.get("schema") != SHARD_SCHEMA:
                raise ValueError(f"{result.out_dir / shard['path']}: invalid shard schema")
            data["group_ids"] = _remap_ids(
                data["group_ids"],
                result.group_names,
                groups,
                torch.int64,
            )
            data["policy_ids"] = _remap_ids(
                data["policy_ids"],
                result.policy_names,
                policies,
                torch.int16,
            )
            data["outcome_ids"] = _remap_ids(
                data["outcome_ids"],
                result.outcome_names,
                outcomes,
                torch.int16,
            )
            shard_name = f"shard-{len(shards):06d}.pt"
            torch.save(data, config.out_dir / shard_name)
            shards.append({"path": shard_name, "rows": int(data["labels"].numel())})
    return shards


def _build_positive_negative_shards_parallel(
    config: ShardBuildConfig,
    selections: list[_TraceSelection],
    feature_names: list[str],
    *,
    progress: Callable[[str], None] | None,
) -> ShardBuildSummary:
    assert config.max_negative_records is not None
    if config.max_records is not None:
        raise ValueError("parallel positive-preserving sampling does not support max_records")

    weights = [selection.path.stat().st_size for selection in selections]
    negative_quotas = _allocate_counts(config.max_negative_records, weights)
    worker_count = min(config.workers, len(selections))
    worker_root = config.out_dir / ".worker-shards"
    worker_root.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    if progress is not None:
        progress(
            f"parallel shard build: workers={worker_count} "
            f"traces={len(selections)} max_negatives={config.max_negative_records}"
        )

    results: list[_WorkerResult] = []
    with ProcessPoolExecutor(max_workers=worker_count) as executor:
        futures = []
        for selection, negative_quota in zip(selections, negative_quotas):
            out_dir = worker_root / f"trace-{selection.source_trace_id:06d}"
            out_dir.mkdir(parents=True, exist_ok=True)
            futures.append(
                executor.submit(
                    _run_positive_negative_worker,
                    selection,
                    feature_names,
                    out_dir,
                    negative_quota=negative_quota,
                    shard_rows=config.shard_rows,
                    seed=config.seed + selection.source_trace_id,
                )
            )
        scanned_records = 0
        written_records = 0
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            scanned_records += result.scanned_records
            written_records += result.written_records
            if progress is not None:
                elapsed = max(0.001, time.monotonic() - started)
                rate = scanned_records / elapsed
                progress(
                    f"finished={len(results)}/{len(selections)} "
                    f"scanned={scanned_records} loaded={written_records} "
                    f"rate={rate:.0f} rows/s"
                )

    results.sort(key=lambda result: result.source_trace_id)
    groups = _IdMap()
    policies = _IdMap()
    outcomes = _IdMap()
    source_counter: Counter[str] = Counter()
    source_trace_rows = [0 for _ in selections]
    scanned_records = 0
    written_records = 0
    positive_records = 0
    for result in results:
        scanned_records += result.scanned_records
        written_records += result.written_records
        positive_records += result.positive_records
        source_trace_rows[result.source_trace_id] = result.source_trace_rows
        source_counter.update(result.source_counter)

    if scanned_records == 0:
        raise ValueError("no trace records loaded")
    if progress is not None:
        progress("merging worker shards")
    shards = _merge_worker_shards(config, feature_names, results, groups, policies, outcomes)
    shutil.rmtree(worker_root)

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
        sampled=True,
        source_counter=source_counter,
    )
    if progress is not None:
        elapsed = max(0.001, time.monotonic() - started)
        progress(
            f"done scanned={scanned_records} loaded={written_records} "
            f"rate={scanned_records / elapsed:.0f} rows/s shards={len(shards)}"
        )
    return ShardBuildSummary(
        out_dir=config.out_dir,
        scanned_records=scanned_records,
        written_records=written_records,
        positive_records=positive_records,
        shard_count=len(shards),
    )


def build_shards(
    config: ShardBuildConfig,
    *,
    progress: Callable[[str], None] | None = _default_progress,
) -> ShardBuildSummary:
    _validate_config(config)
    _prepare_out_dir(config.out_dir, overwrite=config.overwrite)
    selections, feature_names = _trace_selections(config.trace_paths, config.feature_names)
    if (
        config.max_negative_records is not None
        and config.workers > 1
        and len(selections) > 1
        and config.max_records is None
    ):
        return _build_positive_negative_shards_parallel(
            config,
            selections,
            feature_names,
            progress=progress,
        )
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
    sampler: _PositiveNegativeSampler | None = None
    if config.sample_records is None:
        if config.max_negative_records is None:
            writer = _ShardWriter(config.out_dir, feature_names, shard_rows=config.shard_rows)
        else:
            sampler = _PositiveNegativeSampler(
                config.out_dir,
                feature_names,
                max_negative_records=config.max_negative_records,
                shard_rows=config.shard_rows,
                seed=config.seed,
            )
    else:
        reservoir = _Reservoir(config.sample_records, len(feature_names), config.seed)

    def maybe_progress(force: bool = False) -> None:
        nonlocal last_progress
        if progress is None:
            return
        if force or scanned_records - last_progress >= config.progress_interval:
            elapsed = max(0.001, time.monotonic() - started)
            rate = scanned_records / elapsed
            if reservoir is None and sampler is None:
                loaded = scanned_records
            elif reservoir is not None:
                loaded = reservoir.loaded
            else:
                assert sampler is not None
                loaded = sampler.loaded
            shard_count = len(writer.shards) if writer else sampler.shard_count if sampler else 0
            progress(
                f"scanned={scanned_records} loaded={loaded} "
                f"rate={rate:.0f} rows/s shards={shard_count}"
            )
            last_progress = scanned_records

    for selection in selections:
        if progress is not None:
            progress(f"reading {selection.path}")
        for record in _iter_records(selection.path):
            label = record.get("used_in_final_proof")
            if not isinstance(label, bool):
                raise ValueError(f"{selection.path}: expected boolean used_in_final_proof")
            policy = str(record.get("policy", ""))
            outcome = str(record.get("outcome", ""))
            scanned_records += 1
            source_trace_rows[selection.source_trace_id] += 1
            source_counter[f"policy:{policy}"] += 1
            source_counter[f"outcome:{outcome}"] += 1
            positive_records += int(label)

            if writer is not None:
                row = _row_from_record(
                    record,
                    selection,
                    groups=groups,
                    policies=policies,
                    outcomes=outcomes,
                )
                writer.push(row)
            elif reservoir is not None:
                row = _row_from_record(
                    record,
                    selection,
                    groups=groups,
                    policies=policies,
                    outcomes=outcomes,
                )
                reservoir.consider(row)
            else:
                assert sampler is not None
                if label:
                    row = _row_from_record(
                        record,
                        selection,
                        groups=groups,
                        policies=policies,
                        outcomes=outcomes,
                    )
                    sampler.push_positive(row)
                else:
                    slot = sampler.choose_negative_slot()
                    if slot is not None:
                        row = _row_from_record(
                            record,
                            selection,
                            groups=groups,
                            policies=policies,
                            outcomes=outcomes,
                        )
                        sampler.store_negative(slot, row)

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
        if reservoir is not None:
            if progress is not None:
                progress("writing sampled shards")
            positive_records = int(reservoir.labels[: reservoir.loaded].sum().item())
            shards = reservoir.write_shards(
                config.out_dir,
                shard_rows=config.shard_rows,
                seed=config.seed,
            )
            written_records = reservoir.loaded
        else:
            assert sampler is not None
            if progress is not None:
                progress("writing positive-preserving sampled shards")
            positive_records = sampler.positive_records
            shards = sampler.write_shards(
                config.out_dir,
                shard_rows=config.shard_rows,
                seed=config.seed,
            )
            written_records = sampler.loaded

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
        sampled=config.sample_records is not None or config.max_negative_records is not None,
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
