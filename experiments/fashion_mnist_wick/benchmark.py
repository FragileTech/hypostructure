"""CLI for a reproducible Wick/CNN/XGBoost Fashion-MNIST benchmark."""

from __future__ import annotations

import argparse
import csv
import json
import platform
from dataclasses import asdict
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

import torch

from .baselines import evaluate_xgboost, train_xgboost
from .data import DataConfig, flatten_loader, make_loaders
from .models import ConvClassifier, WickClassifier
from .train import TrainConfig, evaluate, resolve_device, seed_everything, train_neural


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", nargs="+", choices=("wick", "cnn", "xgboost"), default=["wick", "cnn", "xgboost"])
    parser.add_argument("--data-dir", type=Path, default=Path("data/fashion-mnist"))
    parser.add_argument("--output-dir", type=Path, default=Path("outputs/fashion-mnist-wick"))
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--epochs", type=int, default=15)
    parser.add_argument("--patience", type=int, default=4)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--feature-dim", type=int, default=64)
    parser.add_argument("--geom-dim", type=int, default=32)
    parser.add_argument("--wick-lambda", type=float, default=0.25)
    parser.add_argument("--bridge-action-weight", type=float, default=0.0)
    parser.add_argument("--learning-rate", type=float, default=3e-4)
    parser.add_argument("--weight-decay", type=float, default=1e-4)
    parser.add_argument("--device", default="auto")
    parser.add_argument("--train-limit", type=int)
    parser.add_argument("--test-limit", type=int)
    parser.add_argument("--xgb-trees", type=int, default=500)
    parser.add_argument("--xgb-depth", type=int, default=8)
    return parser.parse_args()


def _metadata(args: argparse.Namespace) -> dict[str, object]:
    return {
        "created_at": datetime.now(UTC).isoformat(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "torch": torch.__version__,
        "cuda_available": torch.cuda.is_available(),
        "arguments": vars(args) | {"data_dir": str(args.data_dir), "output_dir": str(args.output_dir)},
    }


def _save(results: dict[str, Any], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "results.json").write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    with (output_dir / "summary.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["model", "accuracy", "nll", "training_seconds", "inference_seconds", "parameter_count"])
        writer.writeheader()
        for name, result in results["models"].items():
            writer.writerow(
                {
                    "model": name,
                    "accuracy": result["test"]["accuracy"],
                    "nll": result["test"]["nll"],
                    "training_seconds": result["fit"]["training_seconds"],
                    "inference_seconds": result["test"]["seconds"],
                    "parameter_count": result["fit"].get("parameter_count"),
                }
            )


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    data_config = DataConfig(
        root=args.data_dir,
        batch_size=args.batch_size,
        workers=args.workers,
        seed=args.seed,
        train_limit=args.train_limit,
        test_limit=args.test_limit,
    )
    train_loader, validation_loader, test_loader = make_loaders(data_config)
    train_config = TrainConfig(
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        weight_decay=args.weight_decay,
        bridge_action_weight=args.bridge_action_weight,
        patience=args.patience,
        seed=args.seed,
        device=args.device,
    )
    results: dict[str, Any] = {
        "metadata": _metadata(args),
        "data": asdict(data_config) | {"root": str(data_config.root)},
        "training": asdict(train_config),
        "models": {},
    }

    for name in args.models:
        if name in {"wick", "cnn"}:
            # Reset before construction so models start from reproducible,
            # independently comparable initial states.
            seed_everything(args.seed)
            model = (
                WickClassifier(args.feature_dim, args.geom_dim, lam=args.wick_lambda)
                if name == "wick"
                else ConvClassifier(args.feature_dim)
            )
            model, fit = train_neural(model, train_loader, validation_loader, train_config)
            test = evaluate(model, test_loader, resolve_device(args.device))
            result: dict[str, Any] = {"fit": fit, "test": test}
            if name == "wick":
                result["audit"] = model.wick.audit()
            results["models"][name] = result
            torch.save(model.state_dict(), args.output_dir / f"{name}.pt")
        else:
            x_train, y_train = flatten_loader(train_loader)
            x_validation, y_validation = flatten_loader(validation_loader)
            x_test, y_test = flatten_loader(test_loader)
            model, fit = train_xgboost(
                x_train,
                y_train,
                x_validation,
                y_validation,
                seed=args.seed,
                trees=args.xgb_trees,
                max_depth=args.xgb_depth,
            )
            results["models"][name] = {"fit": fit, "test": evaluate_xgboost(model, x_test, y_test)}
            args.output_dir.mkdir(parents=True, exist_ok=True)
            model.save_model(args.output_dir / "xgboost.ubj")
        _save(results, args.output_dir)


if __name__ == "__main__":
    main()
