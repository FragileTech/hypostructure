"""Conventional Fashion-MNIST baselines."""

from __future__ import annotations

import time
from typing import Any

import numpy as np


def train_xgboost(
    x_train: np.ndarray,
    y_train: np.ndarray,
    x_validation: np.ndarray,
    y_validation: np.ndarray,
    *,
    seed: int,
    trees: int = 500,
    max_depth: int = 8,
    learning_rate: float = 0.08,
    jobs: int = -1,
) -> tuple[Any, dict[str, object]]:
    """Fit a histogram XGBoost model without inspecting the test set."""
    from xgboost import XGBClassifier

    classes = int(np.unique(y_train).size)
    objective = {"objective": "binary:logistic", "eval_metric": "logloss"}
    if classes > 2:
        objective = {
            "objective": "multi:softprob",
            "num_class": classes,
            "eval_metric": "mlogloss",
        }
    model = XGBClassifier(
        **objective,
        n_estimators=trees,
        max_depth=max_depth,
        learning_rate=learning_rate,
        subsample=0.9,
        colsample_bytree=0.9,
        min_child_weight=1.0,
        reg_lambda=1.0,
        tree_method="hist",
        n_jobs=jobs,
        random_state=seed,
        early_stopping_rounds=30,
    )
    started = time.perf_counter()
    model.fit(x_train, y_train, eval_set=[(x_validation, y_validation)], verbose=False)
    return model, {
        "training_seconds": time.perf_counter() - started,
        "trees": int(model.best_iteration + 1),
        "parameter_count": None,
        "device": "cpu",
    }


def evaluate_xgboost(model: Any, x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    started = time.perf_counter()
    probabilities = model.predict_proba(x)
    elapsed = time.perf_counter() - started
    chosen = np.clip(probabilities[np.arange(len(y)), y], 1e-12, 1.0)
    return {
        "accuracy": float((probabilities.argmax(1) == y).mean()),
        "nll": float(-np.log(chosen).mean()),
        "examples": len(y),
        "seconds": elapsed,
        "examples_per_second": len(y) / max(elapsed, 1e-12),
    }
