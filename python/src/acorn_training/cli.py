from __future__ import annotations

import argparse
from pathlib import Path

from .data import LEGACY_FEATURE_NAMES, load_shard_dataset, load_trace_dataset, split_by_search
from .train import TrainConfig, export_onnx, train_model


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Train an Acorn proof-step scorer from eval trace JSONL."
    )
    parser.add_argument(
        "input",
        nargs="+",
        type=Path,
        help="Shard directory, or trace JSONL/JSONL.ZST/JSONL.GZ file.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("../files/models/scorer.onnx"),
        help="ONNX output path.",
    )
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--batch-size", type=int, default=8192)
    parser.add_argument("--learning-rate", type=float, default=1e-3)
    parser.add_argument("--weight-decay", type=float, default=1e-3)
    parser.add_argument("--hidden-size", type=int, default=32)
    parser.add_argument("--hidden-layers", type=int, default=2)
    parser.add_argument("--validation-fraction", type=float, default=0.1)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument(
        "--features",
        choices=["all", "legacy"],
        default="all",
        help="Feature set to train on when reading raw traces. Default: all trace catalog features.",
    )
    parser.add_argument(
        "--feature",
        action="append",
        default=None,
        help="Use this feature name. Can be repeated and overrides --features.",
    )
    parser.add_argument(
        "--device",
        default="auto",
        help="Torch device: auto, cpu, cuda, cuda:0, etc.",
    )
    parser.add_argument(
        "--max-records",
        type=int,
        default=None,
        help="Stop reading after this many trace rows, for smoke tests or quick iteration.",
    )
    parser.add_argument(
        "--sample-records",
        type=int,
        default=None,
        help="Reservoir-sample this many rows across all read trace rows. Not used for shards.",
    )
    parser.add_argument(
        "--inspect-only",
        action="store_true",
        help="Load and summarize the trace without training or exporting.",
    )
    return parser


def _print_dataset_summary(dataset) -> None:
    print(f"examples: {dataset.num_examples}")
    print(f"positive: {dataset.num_positive}")
    print(f"negative: {dataset.num_negative}")
    print(f"positive_rate: {dataset.positive_rate:.6f}")
    for key, count in sorted(dataset.metadata.items()):
        print(f"{key}: {count}")
    print(f"features: {len(dataset.feature_names)}")


def main(argv: list[str] | None = None) -> None:
    args = _parser().parse_args(argv)
    shard_dirs = [path for path in args.input if path.is_dir()]
    trace_paths = [path for path in args.input if not path.is_dir()]
    if shard_dirs and trace_paths:
        raise ValueError("do not mix shard directories and raw trace files in one training run")

    if shard_dirs:
        if args.feature is not None or args.features != "all":
            raise ValueError("feature selection is fixed by shard manifests")
        if args.sample_records is not None:
            raise ValueError("use acorn-build-scorer-shards --sample-records before training")
        dataset = load_shard_dataset(
            shard_dirs,
            max_records=args.max_records,
        )
    else:
        feature_names = None
        if args.feature is not None:
            feature_names = args.feature
        elif args.features == "legacy":
            feature_names = LEGACY_FEATURE_NAMES

        dataset = load_trace_dataset(
            trace_paths,
            feature_names=feature_names,
            max_records=args.max_records,
            sample_records=args.sample_records,
            seed=args.seed,
        )
    _print_dataset_summary(dataset)
    if args.inspect_only:
        return

    split = split_by_search(
        dataset,
        validation_fraction=args.validation_fraction,
        seed=args.seed,
    )
    config = TrainConfig(
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.learning_rate,
        weight_decay=args.weight_decay,
        hidden_size=args.hidden_size,
        hidden_layers=args.hidden_layers,
        seed=args.seed,
        device=args.device,
    )
    model, metrics = train_model(split, config)
    for metric in metrics:
        print(
            f"epoch {metric.epoch}: "
            f"train_loss={metric.train_loss:.6f} "
            f"val_loss={metric.val_loss:.6f} "
            f"val_accuracy={metric.val_accuracy:.4f} "
            f"val_predicted_positive_rate={metric.val_positive_rate:.4f}"
        )
    export_onnx(model, args.out, split.feature_names)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
