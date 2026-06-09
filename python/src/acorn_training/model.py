from __future__ import annotations

import torch
from torch import nn


class ScorerNet(nn.Module):
    def __init__(
        self,
        *,
        feature_mean: torch.Tensor,
        feature_scale: torch.Tensor,
        hidden_size: int,
        hidden_layers: int,
    ) -> None:
        super().__init__()
        if feature_mean.ndim != 1:
            raise ValueError("feature_mean must be one-dimensional")
        if feature_scale.shape != feature_mean.shape:
            raise ValueError("feature_scale must have the same shape as feature_mean")

        self.register_buffer("feature_mean", feature_mean.float())
        self.register_buffer("feature_scale", feature_scale.float().clamp_min(1e-6))

        layers: list[nn.Module] = []
        in_features = int(feature_mean.numel())
        for _ in range(hidden_layers):
            layers.append(nn.Linear(in_features, hidden_size))
            layers.append(nn.ReLU())
            in_features = hidden_size
        layers.append(nn.Linear(in_features, 1))
        self.network = nn.Sequential(*layers)

    @classmethod
    def from_training_features(
        cls,
        features: torch.Tensor,
        *,
        hidden_size: int,
        hidden_layers: int,
    ) -> "ScorerNet":
        feature_mean = features.mean(dim=0)
        feature_scale = features.std(dim=0, unbiased=False)
        return cls(
            feature_mean=feature_mean,
            feature_scale=feature_scale,
            hidden_size=hidden_size,
            hidden_layers=hidden_layers,
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = (x - self.feature_mean) / self.feature_scale
        return self.network(x)


class ProbabilityScorer(nn.Module):
    def __init__(self, scorer: ScorerNet) -> None:
        super().__init__()
        self.scorer = scorer

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return torch.sigmoid(self.scorer(x))
