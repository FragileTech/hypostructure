# Fashion-MNIST Wick benchmark

This experiment compares the finite-chart Wick response classifier from Part II
with a shared-encoder CNN control and histogram XGBoost. All models use the official
Fashion-MNIST test set and the same fixed 55,000/5,000 training/validation split.
The test set is evaluated only after model fitting and early stopping.

## Install and run

From the repository root:

```bash
uv sync --extra fashion-mnist
uv run --extra fashion-mnist python -m experiments.fashion_mnist_wick.benchmark
```

For a quick CPU smoke benchmark:

```bash
uv run --extra fashion-mnist python -m experiments.fashion_mnist_wick.benchmark \
  --epochs 1 --train-limit 2048 --test-limit 512 --workers 0 \
  --xgb-trees 20 --models wick cnn xgboost \
  --output-dir outputs/fashion-mnist-wick-smoke
```

The output directory contains `results.json`, a compact `summary.csv`, neural
checkpoints, and an XGBoost model. Run models in one invocation when making a
comparison so that configuration and split metadata are identical.

## Model implemented

The Wick model computes

```text
image -> shared CNN encoder h -> solve (I + F* F) f = h
      -> concatenate Re(f), Im(f) -> ten real logits
```

with

```text
F = lambda I + i H + C* (lambda I + G - Ay)^(-1) C,
H = Lh Lh^T,  G = Lg Lg^T,  Ay = (K - K^T)/2.
```

`torch.linalg.solve` is used rather than a matrix inverse. Since the default
quotient dimension is only 64, the dense backend is appropriate for this
benchmark and differentiates exactly through both solves. The saved audit
checks symmetry, positivity, skew symmetry, response conditioning, and bridge
action.

The default scientific objective is cross-entropy plus AdamW weight decay. The
optional `--bridge-action-weight` adds the explicitly declared zero-target
Euclidean action; it defaults to zero because shrinking the bridge is a task
choice, not an automatic consequence of classification.

## Interpreting the comparison

The CNN control uses the same encoder and feature width but omits the Wick
response. XGBoost sees the same normalized pixels and validation split. The
result file reports accuracy, negative log likelihood, training time, inference
throughput, neural parameter count, and Wick structural diagnostics.

These are empirical benchmark coordinates, not by themselves Part I confidence
certificates or a saturated-profile proof. A certified experiment must repeat
over a predeclared seed/hyperparameter stage, attach confidence bounds, and
compare complete resource/action records using the manuscript's selector.

## Tabular suite

The same response layer is benchmarked on Breast Cancer Wisconsin, Wine, and
Digits against a shared-encoder MLP, logistic regression, and XGBoost:

```bash
uv run --extra fashion-mnist python -m experiments.fashion_mnist_wick.tabular
```

Additional OpenML datasets can be addressed without baking an unstable name
mapping into the code, for example `--datasets openml:DATASET_ID`. Numeric
columns are median-imputed and standardized; categorical columns are
most-frequent-imputed and one-hot encoded. The preprocessing pipeline is fit on
the training partition only. Splits are stratified and fixed by the stored
seed.

Two harder named datasets are also available: `adult` (mixed-type binary
income prediction) and `covertype` (large seven-class forest cover
classification). For a workstation-scale comparison, use a predeclared
stratified cap rather than silently truncating rows:

```bash
uv run --extra fashion-mnist python -m experiments.fashion_mnist_wick.tabular \
  --datasets adult covertype --max-samples 50000
```
