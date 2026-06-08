from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import onnx
import torch
from torch import nn

from .data import NUM_FEATURES, DatasetSplit, make_loader
from .model import ProbabilityScorer, ScorerNet


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


@dataclass(frozen=True)
class EpochMetrics:
    epoch: int
    train_loss: float
    val_loss: float
    val_accuracy: float
    val_positive_rate: float


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
    loader,
    criterion: nn.Module,
    *,
    device: torch.device,
    optimizer: torch.optim.Optimizer | None = None,
) -> tuple[float, float, float]:
    training = optimizer is not None
    model.train(training)

    total_loss = 0.0
    total_examples = 0
    correct = 0
    predicted_positive = 0

    with torch.set_grad_enabled(training):
        for features, labels in loader:
            features = features.to(device)
            labels = labels.to(device).unsqueeze(1)
            logits = model(features)
            loss = criterion(logits, labels)

            if optimizer is not None:
                optimizer.zero_grad(set_to_none=True)
                loss.backward()
                optimizer.step()

            batch_size = int(labels.shape[0])
            total_loss += float(loss.item()) * batch_size
            total_examples += batch_size
            predictions = torch.sigmoid(logits) >= 0.5
            expected = labels >= 0.5
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
) -> tuple[ScorerNet, list[EpochMetrics]]:
    torch.manual_seed(config.seed)
    device = choose_device(config.device)

    model = ScorerNet.from_training_features(
        split.train_features,
        hidden_size=config.hidden_size,
        hidden_layers=config.hidden_layers,
    ).to(device)
    criterion = nn.BCEWithLogitsLoss(
        pos_weight=_positive_weight(split.train_labels).to(device)
    )
    optimizer = torch.optim.AdamW(
        model.parameters(),
        lr=config.learning_rate,
        weight_decay=config.weight_decay,
    )

    train_loader = make_loader(
        split.train_features,
        split.train_labels,
        batch_size=config.batch_size,
        shuffle=True,
        seed=config.seed,
    )
    val_loader = make_loader(
        split.val_features,
        split.val_labels,
        batch_size=config.batch_size,
        shuffle=False,
        seed=config.seed,
    )

    metrics: list[EpochMetrics] = []
    for epoch in range(1, config.epochs + 1):
        train_loss, _, _ = _run_epoch(
            model,
            train_loader,
            criterion,
            device=device,
            optimizer=optimizer,
        )
        val_loss, val_accuracy, val_positive_rate = _run_epoch(
            model,
            val_loader,
            criterion,
            device=device,
        )
        metrics.append(
            EpochMetrics(
                epoch=epoch,
                train_loss=train_loss,
                val_loss=val_loss,
                val_accuracy=val_accuracy,
                val_positive_rate=val_positive_rate,
            )
        )

    return model, metrics


def export_onnx(model: ScorerNet, output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    export_model = ProbabilityScorer(model).cpu().eval()
    dummy_input = torch.zeros(1, NUM_FEATURES, dtype=torch.float32)
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
