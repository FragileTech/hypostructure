"""Standard tabular benchmark suite for Wick and conventional classifiers."""

from __future__ import annotations

import argparse
import csv
import json
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
from sklearn.compose import ColumnTransformer
from sklearn.datasets import (
    fetch_covtype,
    fetch_openml,
    load_breast_cancer,
    load_digits,
    load_wine,
)
from sklearn.impute import SimpleImputer
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import accuracy_score, log_loss
from sklearn.model_selection import train_test_split
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import LabelEncoder, OneHotEncoder, StandardScaler
from torch.utils.data import DataLoader, TensorDataset

from .baselines import evaluate_xgboost, train_xgboost
from .models import TabularMLP, TabularWickClassifier
from .train import TrainConfig, evaluate, resolve_device, seed_everything, train_neural

BUILTIN_DATASETS = {
    "breast-cancer": load_breast_cancer,
    "wine": load_wine,
    "digits": load_digits,
}


def _load(name: str) -> tuple[Any, np.ndarray]:
    if name in BUILTIN_DATASETS:
        dataset = BUILTIN_DATASETS[name]()
        return dataset.data, np.asarray(dataset.target)
    if name == "adult":
        dataset = fetch_openml(name="adult", version=2, as_frame=True, parser="auto")
        return dataset.data, LabelEncoder().fit_transform(dataset.target)
    if name == "covertype":
        dataset = fetch_covtype(as_frame=True)
        return dataset.data, LabelEncoder().fit_transform(dataset.target)
    if name.startswith("openml:"):
        dataset_id = int(name.partition(":")[2])
        dataset = fetch_openml(data_id=dataset_id, as_frame=True, parser="auto")
        return dataset.data, LabelEncoder().fit_transform(dataset.target)
    raise ValueError(f"unknown dataset {name!r}")


def _preprocessor(x_train: Any) -> Any:
    if not hasattr(x_train, "select_dtypes"):
        return make_pipeline(SimpleImputer(strategy="median"), StandardScaler())
    numeric = list(x_train.select_dtypes(include=["number", "bool"]).columns)
    categorical = [column for column in x_train.columns if column not in numeric]
    return ColumnTransformer(
        [
            ("numeric", make_pipeline(SimpleImputer(strategy="median"), StandardScaler()), numeric),
            (
                "categorical",
                make_pipeline(
                    SimpleImputer(strategy="most_frequent"),
                    OneHotEncoder(handle_unknown="ignore", sparse_output=False),
                ),
                categorical,
            ),
        ],
        sparse_threshold=0.0,
    )


def prepare_dataset(
    name: str, seed: int, batch_size: int, max_samples: int | None = None
) -> tuple[DataLoader, DataLoader, DataLoader, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    x, y = _load(name)
    if max_samples is not None and max_samples < len(y):
        selected, _ = train_test_split(
            np.arange(len(y)),
            train_size=max_samples,
            random_state=seed,
            stratify=y,
        )
        x = x.iloc[selected] if hasattr(x, "iloc") else x[selected]
        y = y[selected]
    x_train_val, x_test, y_train_val, y_test = train_test_split(
        x, y, test_size=0.2, random_state=seed, stratify=y
    )
    x_train, x_val, y_train, y_val = train_test_split(
        x_train_val, y_train_val, test_size=0.2, random_state=seed + 1, stratify=y_train_val
    )
    transform = _preprocessor(x_train)
    x_train = np.asarray(transform.fit_transform(x_train), dtype=np.float32)
    x_val = np.asarray(transform.transform(x_val), dtype=np.float32)
    x_test = np.asarray(transform.transform(x_test), dtype=np.float32)

    def loader(features: np.ndarray, labels: np.ndarray, shuffle: bool) -> DataLoader:
        generator = torch.Generator().manual_seed(seed)
        dataset = TensorDataset(torch.from_numpy(features), torch.from_numpy(labels.astype(np.int64)))
        return DataLoader(dataset, batch_size=batch_size, shuffle=shuffle, generator=generator)

    return (
        loader(x_train, y_train, True),
        loader(x_val, y_val, False),
        loader(x_test, y_test, False),
        x_train,
        y_train,
        x_val,
        y_val,
        x_test,
        y_test,
    )


def _evaluate_sklearn(model: Any, x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    started = time.perf_counter()
    probabilities = model.predict_proba(x)
    elapsed = time.perf_counter() - started
    return {
        "accuracy": float(accuracy_score(y, probabilities.argmax(1))),
        "nll": float(log_loss(y, probabilities, labels=np.arange(probabilities.shape[1]))),
        "examples": len(y),
        "seconds": elapsed,
        "examples_per_second": len(y) / max(elapsed, 1e-12),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--datasets", nargs="+", default=list(BUILTIN_DATASETS))
    parser.add_argument(
        "--models",
        nargs="+",
        choices=("wick", "mlp", "logistic", "xgboost"),
        default=["wick", "mlp", "logistic", "xgboost"],
    )
    parser.add_argument("--output-dir", type=Path, default=Path("outputs/tabular-wick"))
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--patience", type=int, default=12)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--feature-dim", type=int, default=32)
    parser.add_argument("--geom-dim", type=int, default=16)
    parser.add_argument("--wick-lambda", type=float, default=0.25)
    parser.add_argument("--bridge-action-weight", type=float, default=0.0)
    parser.add_argument("--device", default="auto")
    parser.add_argument("--xgb-trees", type=int, default=500)
    parser.add_argument(
        "--max-samples",
        type=int,
        help="Predeclared stratified cap for large datasets; omitted uses all rows.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    output: dict[str, Any] = {"config": vars(args) | {"output_dir": str(args.output_dir)}, "datasets": {}}
    rows: list[dict[str, Any]] = []
    for dataset_name in args.datasets:
        train_loader, val_loader, test_loader, x_train, y_train, x_val, y_val, x_test, y_test = prepare_dataset(
            dataset_name, args.seed, args.batch_size, args.max_samples
        )
        classes = int(np.unique(y_train).size)
        dataset_results: dict[str, Any] = {"input_dim": int(x_train.shape[1]), "classes": classes, "models": {}}
        config = TrainConfig(
            epochs=args.epochs,
            patience=args.patience,
            seed=args.seed,
            device=args.device,
            bridge_action_weight=args.bridge_action_weight,
            learning_rate=1e-3,
        )
        for model_name in args.models:
            if model_name in {"wick", "mlp"}:
                seed_everything(args.seed)
                model = (
                    TabularWickClassifier(x_train.shape[1], args.feature_dim, args.geom_dim, classes, args.wick_lambda)
                    if model_name == "wick"
                    else TabularMLP(x_train.shape[1], args.feature_dim, classes)
                )
                model, fit = train_neural(model, train_loader, val_loader, config)
                result: dict[str, Any] = {"fit": fit, "test": evaluate(model, test_loader, resolve_device(args.device))}
                if model_name == "wick":
                    result["audit"] = model.wick.audit()
            elif model_name == "logistic":
                model = LogisticRegression(max_iter=2_000, random_state=args.seed)
                started = time.perf_counter()
                model.fit(x_train, y_train)
                result = {"fit": {"training_seconds": time.perf_counter() - started}, "test": _evaluate_sklearn(model, x_test, y_test)}
            else:
                model, fit = train_xgboost(x_train, y_train, x_val, y_val, seed=args.seed, trees=args.xgb_trees)
                result = {"fit": fit, "test": evaluate_xgboost(model, x_test, y_test)}
            dataset_results["models"][model_name] = result
            rows.append({"dataset": dataset_name, "model": model_name, "accuracy": result["test"]["accuracy"], "nll": result["test"]["nll"], "training_seconds": result["fit"]["training_seconds"]})
        output["datasets"][dataset_name] = dataset_results
        (args.output_dir / "results.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")

    with (args.output_dir / "summary.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


if __name__ == "__main__":
    main()
