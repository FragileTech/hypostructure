"""The papers this repository publishes, each described as a `ProofSpec`."""

from __future__ import annotations

from proof_graph import ProofSpec

from . import erdos64, navier_stokes

SPECS: dict[str, ProofSpec] = {
    spec.slug: spec for spec in (erdos64.SPEC, navier_stokes.SPEC)
}

__all__ = ["SPECS"]
