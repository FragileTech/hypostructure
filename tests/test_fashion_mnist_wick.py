from __future__ import annotations

import pytest

torch = pytest.importorskip("torch")

from experiments.fashion_mnist_wick.models import (
    ConvClassifier,
    TabularMLP,
    TabularWickClassifier,
    WickClassifier,
    WickResponse,
)


def test_wick_response_shapes_gradients_and_structure() -> None:
    torch.manual_seed(3)
    layer = WickResponse(quotient_dim=8, geom_dim=5, lam=0.2)
    inputs = torch.randn(6, 8, requires_grad=True)
    output = layer(inputs)
    assert output.shape == (6, 16)
    output.square().mean().backward()
    assert inputs.grad is not None
    assert all(parameter.grad is not None for parameter in layer.parameters())

    audit = layer.audit()
    assert audit["h_symmetry_residual"] < 1e-6
    assert audit["g_symmetry_residual"] < 1e-6
    assert audit["ay_skew_residual"] < 1e-6
    assert audit["h_min_eigenvalue"] > -1e-5
    assert audit["g_min_eigenvalue"] > -1e-5
    assert audit["response_min_eigenvalue"] >= 1.0 - 1e-5


@pytest.mark.parametrize("model", [ConvClassifier(8), WickClassifier(8, 5)])
def test_classifiers_produce_ten_real_logits(model: torch.nn.Module) -> None:
    logits = model(torch.randn(4, 1, 28, 28))
    assert logits.shape == (4, 10)
    assert not logits.is_complex()
    torch.nn.functional.cross_entropy(logits, torch.tensor([0, 1, 2, 3])).backward()


@pytest.mark.parametrize(
    "model", [TabularMLP(12, 8, 3), TabularWickClassifier(12, 8, 5, 3)]
)
def test_tabular_classifiers_train_by_backprop(model: torch.nn.Module) -> None:
    logits = model(torch.randn(7, 12))
    assert logits.shape == (7, 3)
    torch.nn.functional.cross_entropy(logits, torch.arange(7) % 3).backward()
    assert all(parameter.grad is not None for parameter in model.parameters())
