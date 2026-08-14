"""Training and evaluation loops with comparable benchmark accounting."""

from __future__ import annotations

import random
import time
from dataclasses import dataclass

import numpy as np
import torch
from torch import Tensor, nn
from torch.utils.data import DataLoader

from .models import TabularWickClassifier, WickClassifier


@dataclass(frozen=True)
class TrainConfig:
    epochs: int = 15
    learning_rate: float = 3e-4
    weight_decay: float = 1e-4
    bridge_action_weight: float = 0.0
    patience: int = 4
    seed: int = 17
    device: str = "auto"


def seed_everything(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def resolve_device(name: str) -> torch.device:
    if name == "auto":
        return torch.device("cuda" if torch.cuda.is_available() else "cpu")
    return torch.device(name)


def _sync(device: torch.device) -> None:
    if device.type == "cuda":
        torch.cuda.synchronize(device)


@torch.inference_mode()
def evaluate(model: nn.Module, loader: DataLoader, device: torch.device) -> dict[str, float]:
    model.eval()
    total_loss = total_correct = total = 0.0
    started = time.perf_counter()
    for images, labels in loader:
        images, labels = images.to(device, non_blocking=True), labels.to(device, non_blocking=True)
        logits = model(images)
        total_loss += float(nn.functional.cross_entropy(logits, labels, reduction="sum"))
        total_correct += float((logits.argmax(1) == labels).sum())
        total += labels.numel()
    _sync(device)
    elapsed = time.perf_counter() - started
    return {
        "accuracy": total_correct / total,
        "nll": total_loss / total,
        "examples": int(total),
        "seconds": elapsed,
        "examples_per_second": total / max(elapsed, 1e-12),
    }


def train_neural(
    model: nn.Module,
    train_loader: DataLoader,
    validation_loader: DataLoader,
    config: TrainConfig,
) -> tuple[nn.Module, dict[str, object]]:
    seed_everything(config.seed)
    device = resolve_device(config.device)
    if device.type == "cuda":
        torch.cuda.reset_peak_memory_stats(device)
    model.to(device)
    optimizer = torch.optim.AdamW(
        model.parameters(), lr=config.learning_rate, weight_decay=config.weight_decay
    )
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=config.epochs)
    best_state: dict[str, Tensor] | None = None
    best_nll = float("inf")
    stale = 0
    history: list[dict[str, float]] = []
    started = time.perf_counter()

    for epoch in range(config.epochs):
        model.train()
        total_loss = total = 0.0
        for images, labels in train_loader:
            images, labels = images.to(device, non_blocking=True), labels.to(device, non_blocking=True)
            optimizer.zero_grad(set_to_none=True)
            logits = model(images)
            loss = nn.functional.cross_entropy(logits, labels)
            if isinstance(model, (WickClassifier, TabularWickClassifier)) and config.bridge_action_weight:
                loss = loss + config.bridge_action_weight * model.wick.bridge_action()
            loss.backward()
            optimizer.step()
            total_loss += float(loss.detach()) * labels.numel()
            total += labels.numel()
        scheduler.step()
        validation = evaluate(model, validation_loader, device)
        history.append(
            {
                "epoch": epoch + 1,
                "train_loss": total_loss / total,
                "validation_nll": validation["nll"],
                "validation_accuracy": validation["accuracy"],
            }
        )
        if validation["nll"] < best_nll:
            best_nll = validation["nll"]
            best_state = {key: value.detach().cpu().clone() for key, value in model.state_dict().items()}
            stale = 0
        else:
            stale += 1
            if stale >= config.patience:
                break

    _sync(device)
    training_seconds = time.perf_counter() - started
    if best_state is None:
        raise RuntimeError("training produced no checkpoint")
    model.load_state_dict(best_state)
    model.to(device)
    parameter_count = sum(parameter.numel() for parameter in model.parameters())
    peak_bytes = torch.cuda.max_memory_allocated(device) if device.type == "cuda" else None
    return model, {
        "training_seconds": training_seconds,
        "parameter_count": parameter_count,
        "device": str(device),
        "peak_cuda_bytes": peak_bytes,
        "epochs_completed": len(history),
        "history": history,
    }
