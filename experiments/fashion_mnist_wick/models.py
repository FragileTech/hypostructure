"""Structure-preserving classifiers used by the benchmark."""

from __future__ import annotations

import torch
from torch import Tensor, nn


class ConvEncoder(nn.Module):
    """Small encoder shared by the CNN and Wick models."""

    def __init__(self, feature_dim: int = 64) -> None:
        super().__init__()
        self.features = nn.Sequential(
            nn.Conv2d(1, 32, 3, padding=1),
            nn.BatchNorm2d(32),
            nn.SiLU(),
            nn.MaxPool2d(2),
            nn.Conv2d(32, 64, 3, padding=1),
            nn.BatchNorm2d(64),
            nn.SiLU(),
            nn.MaxPool2d(2),
            nn.Flatten(),
            nn.Linear(64 * 7 * 7, feature_dim),
        )

    def forward(self, images: Tensor) -> Tensor:
        return self.features(images)


class ConvClassifier(nn.Module):
    """Capacity-matched conventional neural baseline."""

    def __init__(self, feature_dim: int = 64, classes: int = 10) -> None:
        super().__init__()
        self.encoder = ConvEncoder(feature_dim)
        self.head = nn.Linear(feature_dim, classes)

    def forward(self, images: Tensor) -> Tensor:
        return self.head(self.encoder(images))


class WickResponse(nn.Module):
    r"""Dense finite-chart response ``(I + F*F)^{-1}``.

    This is the manuscript's small-chart backend.  It never forms an inverse:
    one Hermitian positive-definite solve is shared by the minibatch.  The
    matrices are compiled as H=Lh Lh^T, G=Lg Lg^T, Ay=(K-K^T)/2.
    """

    def __init__(self, quotient_dim: int, geom_dim: int, lam: float = 0.25) -> None:
        super().__init__()
        if quotient_dim < 1 or geom_dim < 1 or lam <= 0:
            raise ValueError("dimensions and lam must be positive")
        self.quotient_dim = quotient_dim
        self.geom_dim = geom_dim
        self.lam = float(lam)
        scale = quotient_dim**-0.5
        self.lh = nn.Parameter(scale * torch.randn(quotient_dim, quotient_dim))
        self.lg = nn.Parameter(scale * torch.randn(geom_dim, geom_dim))
        self.ay_raw = nn.Parameter(scale * torch.randn(geom_dim, geom_dim))
        self.caus = nn.Parameter(scale * torch.randn(geom_dim, quotient_dim))

    def operators(self) -> tuple[Tensor, Tensor, Tensor, Tensor, Tensor]:
        """Compile H, G, Ay, C and F in complex precision."""
        h = self.lh @ self.lh.mT
        g = self.lg @ self.lg.mT
        ay = 0.5 * (self.ay_raw - self.ay_raw.mT)
        c = self.caus
        complex_dtype = torch.complex128 if h.dtype == torch.float64 else torch.complex64
        h_c, g_c, ay_c, c_c = (x.to(complex_dtype) for x in (h, g, ay, c))
        iq = torch.eye(self.quotient_dim, dtype=complex_dtype, device=h.device)
        iy = torch.eye(self.geom_dim, dtype=complex_dtype, device=h.device)
        b = self.lam * iy + g_c - ay_c
        # R=B^{-1}C; solve is differentiable and more stable than inverse.
        response_to_caus = torch.linalg.solve(b, c_c)
        f = self.lam * iq + 1j * h_c + c_c.mH @ response_to_caus
        return h, g, ay, c, f

    def forward(self, features: Tensor) -> Tensor:
        """Apply the response to a batch and return real and imaginary parts."""
        _, _, _, _, f = self.operators()
        iq = torch.eye(self.quotient_dim, dtype=f.dtype, device=f.device)
        a = iq + f.mH @ f
        rhs = features.to(f.dtype).mT
        solved = torch.linalg.solve(a, rhs).mT
        return torch.cat((solved.real, solved.imag), dim=-1)

    def bridge_action(self) -> Tensor:
        """Zero-target Euclidean bridge action, used only when configured."""
        return 0.5 * self.caus.square().sum()

    @torch.no_grad()
    def audit(self) -> dict[str, float]:
        """Return finite-chart structural and solve-conditioning diagnostics."""
        h, g, ay, _, f = self.operators()
        iq = torch.eye(self.quotient_dim, dtype=f.dtype, device=f.device)
        a = iq + f.mH @ f
        return {
            "h_symmetry_residual": float(torch.linalg.norm(h - h.mT).cpu()),
            "g_symmetry_residual": float(torch.linalg.norm(g - g.mT).cpu()),
            "ay_skew_residual": float(torch.linalg.norm(ay + ay.mT).cpu()),
            "h_min_eigenvalue": float(torch.linalg.eigvalsh(h).min().cpu()),
            "g_min_eigenvalue": float(torch.linalg.eigvalsh(g).min().cpu()),
            "response_min_eigenvalue": float(torch.linalg.eigvalsh(a).min().real.cpu()),
            "response_condition": float(torch.linalg.cond(a).real.cpu()),
            "bridge_action": float(self.bridge_action().cpu()),
        }


class WickClassifier(nn.Module):
    """CNN encoder, Wick response, and ten-class real readout."""

    def __init__(
        self,
        feature_dim: int = 64,
        geom_dim: int = 32,
        classes: int = 10,
        lam: float = 0.25,
    ) -> None:
        super().__init__()
        self.encoder = ConvEncoder(feature_dim)
        self.wick = WickResponse(feature_dim, geom_dim, lam)
        self.head = nn.Linear(2 * feature_dim, classes)

    def forward(self, images: Tensor) -> Tensor:
        return self.head(self.wick(self.encoder(images)))


class TabularMLP(nn.Module):
    """Conventional tabular control with the same hidden encoder."""

    def __init__(self, input_dim: int, feature_dim: int, classes: int) -> None:
        super().__init__()
        self.encoder = nn.Sequential(
            nn.Linear(input_dim, 2 * feature_dim),
            nn.LayerNorm(2 * feature_dim),
            nn.SiLU(),
            nn.Linear(2 * feature_dim, feature_dim),
            nn.SiLU(),
        )
        self.head = nn.Linear(feature_dim, classes)

    def forward(self, inputs: Tensor) -> Tensor:
        return self.head(self.encoder(inputs))


class TabularWickClassifier(nn.Module):
    """Tabular MLP followed by the same finite-chart Wick response."""

    def __init__(
        self,
        input_dim: int,
        feature_dim: int,
        geom_dim: int,
        classes: int,
        lam: float = 0.25,
    ) -> None:
        super().__init__()
        self.encoder = nn.Sequential(
            nn.Linear(input_dim, 2 * feature_dim),
            nn.LayerNorm(2 * feature_dim),
            nn.SiLU(),
            nn.Linear(2 * feature_dim, feature_dim),
            nn.SiLU(),
        )
        self.wick = WickResponse(feature_dim, geom_dim, lam)
        self.head = nn.Linear(2 * feature_dim, classes)

    def forward(self, inputs: Tensor) -> Tensor:
        return self.head(self.wick(self.encoder(inputs)))
