from __future__ import annotations

import json
import copy
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import onnx
import torch
from torch import nn

from .data import DatasetSplit
from .model import ProbabilityScorer, ScorerNet

FEATURE_CONTRACT_SCHEMA = "acorn-scorer-feature-contract-v1"


@dataclass(frozen=True)
class TrainConfig:
    epochs: int
    batch_size: int
    learning_rate: float
    weight_decay: float
    hidden_size: int
    hidden_layers: int
    seed: int
    device: str
    threads: int | None = None


@dataclass(frozen=True)
class EpochMetrics:
    epoch: int
    train_loss: float
    val_loss: float
    val_accuracy: float
    val_positive_rate: float
    is_best: bool = False


def choose_device(raw: str) -> torch.device:
    if raw == "auto":
        return torch.device("cuda" if torch.cuda.is_available() else "cpu")
    device = torch.device(raw)
    if device.type == "cuda" and not torch.cuda.is_available():
        raise ValueError("CUDA requested but not available")
    return device


def _positive_weight(labels: torch.Tensor) -> torch.Tensor:
    positive = labels.sum()
    negative = labels.numel() - positive
    if positive <= 0:
        raise ValueError("training split has no positive examples")
    if negative <= 0:
        raise ValueError("training split has no negative examples")
    return negative / positive


def _run_epoch(
    model: ScorerNet,
    features: torch.Tensor,
    labels: torch.Tensor,
    criterion: nn.Module,
    *,
    batch_size: int,
    shuffle: bool,
    seed: int,
    optimizer: torch.optim.Optimizer | None = None,
) -> tuple[float, float, float]:
    training = optimizer is not None
    model.train(training)

    total_loss = 0.0
    total_examples = 0
    correct = 0
    predicted_positive = 0

    with torch.set_grad_enabled(training):
        if shuffle:
            generator = torch.Generator(device=features.device)
            generator.manual_seed(seed)
            order = torch.randperm(
                labels.numel(),
                generator=generator,
                device=features.device,
            )
        else:
            order = None

        for start in range(0, labels.numel(), batch_size):
            end = min(start + batch_size, labels.numel())
            if order is None:
                batch_features = features[start:end]
                batch_labels = labels[start:end]
            else:
                indices = order[start:end]
                batch_features = features.index_select(0, indices)
                batch_labels = labels.index_select(0, indices)

            batch_labels = batch_labels.unsqueeze(1)
            logits = model(batch_features)
            loss = criterion(logits, batch_labels)

            if optimizer is not None:
                optimizer.zero_grad(set_to_none=True)
                loss.backward()
                optimizer.step()

            actual_batch_size = int(batch_labels.shape[0])
            total_loss += float(loss.item()) * actual_batch_size
            total_examples += actual_batch_size
            predictions = torch.sigmoid(logits) >= 0.5
            expected = batch_labels >= 0.5
            correct += int((predictions == expected).sum().item())
            predicted_positive += int(predictions.sum().item())

    return (
        total_loss / total_examples,
        correct / total_examples,
        predicted_positive / total_examples,
    )


def train_model(
    split: DatasetSplit,
    config: TrainConfig,
    progress: Callable[[EpochMetrics], None] | None = None,
) -> tuple[ScorerNet, list[EpochMetrics]]:
    torch.manual_seed(config.seed)
    if config.threads is not None:
        if config.threads <= 0:
            raise ValueError("threads must be positive")
        torch.set_num_threads(config.threads)
    device = choose_device(config.device)

    model = ScorerNet.from_training_features(
        split.train_features,
        hidden_size=config.hidden_size,
        hidden_layers=config.hidden_layers,
    ).to(device)
    train_features = split.train_features.to(device)
    train_labels = split.train_labels.to(device)
    val_features = split.val_features.to(device)
    val_labels = split.val_labels.to(device)
    criterion = nn.BCEWithLogitsLoss(
        pos_weight=_positive_weight(train_labels).to(device)
    )
    optimizer = torch.optim.AdamW(
        model.parameters(),
        lr=config.learning_rate,
        weight_decay=config.weight_decay,
    )

    metrics: list[EpochMetrics] = []
    best_val_loss = float("inf")
    best_state = copy.deepcopy(model.state_dict())
    for epoch in range(1, config.epochs + 1):
        train_loss, _, _ = _run_epoch(
            model,
            train_features,
            train_labels,
            criterion,
            batch_size=config.batch_size,
            shuffle=True,
            seed=config.seed + epoch,
            optimizer=optimizer,
        )
        val_loss, val_accuracy, val_positive_rate = _run_epoch(
            model,
            val_features,
            val_labels,
            criterion,
            batch_size=config.batch_size,
            shuffle=False,
            seed=config.seed,
        )
        is_best = val_loss < best_val_loss
        if is_best:
            best_val_loss = val_loss
            best_state = copy.deepcopy(model.state_dict())
        metric = EpochMetrics(
            epoch=epoch,
            train_loss=train_loss,
            val_loss=val_loss,
            val_accuracy=val_accuracy,
            val_positive_rate=val_positive_rate,
            is_best=is_best,
        )
        metrics.append(metric)
        if progress is not None:
            progress(metric)

    model.load_state_dict(best_state)
    return model, metrics


def feature_contract_path(model_path: Path) -> Path:
    if model_path.name.endswith(".onnx"):
        return model_path.with_name(f"{model_path.name[:-len('.onnx')]}.features.json")
    return model_path.with_suffix(".features.json")


def export_onnx(model: ScorerNet, output_path: Path, feature_names: list[str]) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    export_model = ProbabilityScorer(model).cpu().eval()
    if not feature_names:
        raise ValueError("feature_names must not be empty")
    if len(feature_names) != int(model.feature_mean.numel()):
        raise ValueError("feature_names length does not match model input width")
    dummy_input = torch.zeros(1, len(feature_names), dtype=torch.float32)
    torch.onnx.export(
        export_model,
        dummy_input,
        output_path,
        input_names=["input"],
        output_names=["output"],
        dynamic_axes={
            "input": {0: "batch_size"},
            "output": {0: "batch_size"},
        },
    )
    onnx_model = onnx.load(output_path)
    onnx.checker.check_model(onnx_model)
    contract_path = feature_contract_path(output_path)
    with contract_path.open("w") as f:
        json.dump(
            {
                "schema": FEATURE_CONTRACT_SCHEMA,
                "input_features": feature_names,
            },
            f,
            indent=2,
        )
        f.write("\n")
