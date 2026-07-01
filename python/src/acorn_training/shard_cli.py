from __future__ import annotations

import argparse
import os
from pathlib import Path

from .shards import ShardBuildConfig, build_shards


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Convert Acorn eval traces into binary scorer training shards."
    )
    parser.add_argument(
        "trace",
        nargs="+",
        type=Path,
        help="Trace JSONL.ZST file from `acorn eval --trace-out`.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output shard directory.",
    )
    parser.add_argument(
        "--shard-rows",
        type=int,
        default=1_000_000,
        help="Rows per output shard. Default: 1,000,000.",
    )
    parser.add_argument(
        "--sample-records",
        type=int,
        default=None,
        help="Reservoir-sample this many rows before writing shards.",
    )
    parser.add_argument(
        "--max-negatives",
        type=int,
        default=None,
        help="Keep all positive rows and reservoir-sample at most this many negative rows.",
    )
    parser.add_argument(
        "--max-records",
        type=int,
        default=None,
        help="Stop reading after this many trace rows, for smoke tests.",
    )
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument(
        "--workers",
        type=int,
        default=0,
        help="Parallel workers for positive-preserving sharding. Use 0 for auto. Default: 0.",
    )
    parser.add_argument(
        "--feature",
        action="append",
        default=None,
        help="Use this feature name. Can be repeated to choose an explicit subset.",
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Delete the output directory before writing.",
    )
    parser.add_argument(
        "--progress-interval",
        type=int,
        default=1_000_000,
        help="Print progress every N scanned rows. Default: 1,000,000.",
    )
    return parser


def main(argv: list[str] | None = None) -> None:
    args = _parser().parse_args(argv)
    workers = args.workers
    if workers == 0:
        workers = min(os.cpu_count() or 1, len(args.trace))

    summary = build_shards(
        ShardBuildConfig(
            trace_paths=args.trace,
            out_dir=args.out,
            feature_names=args.feature,
            shard_rows=args.shard_rows,
            sample_records=args.sample_records,
            max_negative_records=args.max_negatives,
            max_records=args.max_records,
            seed=args.seed,
            overwrite=args.overwrite,
            progress_interval=args.progress_interval,
            workers=workers,
        )
    )
    print(f"wrote {summary.written_records} rows to {summary.shard_count} shards")
    print(f"scanned {summary.scanned_records} trace rows")
    print(f"positive rows: {summary.positive_records}")
    print(f"manifest: {summary.out_dir / 'manifest.json'}")


if __name__ == "__main__":
    main()
