"""Reproducible Fashion-MNIST data protocol."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import numpy as np
import torch
from sklearn.model_selection import train_test_split
from torch.utils.data import DataLoader, Subset
from torchvision import datasets, transforms


@dataclass(frozen=True)
class DataConfig:
    root: Path
    batch_size: int = 256
    validation_size: int = 5_000
    workers: int = 2
    seed: int = 17
    train_limit: int | None = None
    test_limit: int | None = None


def _limit(
    indices: np.ndarray, labels: np.ndarray, limit: int | None, seed: int
) -> np.ndarray:
    if limit is None or limit >= len(indices):
        return indices
    selected, _ = train_test_split(
        indices,
        train_size=limit,
        random_state=seed,
        shuffle=True,
        stratify=labels[indices],
    )
    return np.sort(selected)


def make_loaders(config: DataConfig) -> tuple[DataLoader, DataLoader, DataLoader]:
    transform = transforms.Compose(
        [transforms.ToTensor(), transforms.Normalize((0.2860,), (0.3530,))]
    )
    train_set = datasets.FashionMNIST(config.root, train=True, download=True, transform=transform)
    test_set = datasets.FashionMNIST(config.root, train=False, download=True, transform=transform)
    if not 0 < config.validation_size < len(train_set):
        raise ValueError("validation_size must lie strictly inside the training set")

    labels = np.asarray(train_set.targets)
    all_train = np.arange(len(train_set))
    train_indices, val_indices = train_test_split(
        all_train,
        test_size=config.validation_size,
        random_state=config.seed,
        shuffle=True,
        stratify=labels,
    )
    train_indices = _limit(np.sort(train_indices), labels, config.train_limit, config.seed + 1)
    test_labels = np.asarray(test_set.targets)
    test_indices = _limit(
        np.arange(len(test_set)), test_labels, config.test_limit, config.seed + 2
    )
    generator = torch.Generator().manual_seed(config.seed)

    common = {
        "batch_size": config.batch_size,
        "num_workers": config.workers,
        "pin_memory": torch.cuda.is_available(),
    }
    train = DataLoader(Subset(train_set, train_indices.tolist()), shuffle=True, generator=generator, **common)
    validation = DataLoader(Subset(train_set, val_indices.tolist()), shuffle=False, **common)
    test = DataLoader(Subset(test_set, test_indices.tolist()), shuffle=False, **common)
    return train, validation, test


def flatten_loader(loader: DataLoader) -> tuple[np.ndarray, np.ndarray]:
    """Materialize normalized pixels for conventional CPU baselines."""
    xs, ys = [], []
    for images, labels in loader:
        xs.append(images.flatten(1).numpy())
        ys.append(labels.numpy())
    return np.concatenate(xs), np.concatenate(ys)
