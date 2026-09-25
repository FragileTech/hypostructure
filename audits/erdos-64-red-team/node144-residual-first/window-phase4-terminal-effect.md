# Proposed effect of terminal congestion on [144a]

Let `B` be the full post-[144] window-arm `ExactLedger`, with its selected
graph `G` and one bound handoff source witness. Extract that witness's
pattern `P`, demand union `D`, root `ρ`, and terminal set
`T = {d.2 : d ∈ D}`. The selected configurations make these the terminals
of actual declared routes. The proposed local output is

\[
  O_{\rm term}:
  \quad (\forall v\in V(G),\ |\{d\in D:d.2=v\}|\le3)
  \quad\land\quad
  (\exists f:P\to T,\ \forall v\in T,\ |f^{-1}(v)|\le3).
\]

The first conjunct follows from excess-port membership and the high-centre
normal form on the same `G`: `d.1` is adjacent to `d.2`, which has degree
three, and `d ↦ d.1` is injective on a fixed-terminal fibre. For the second
conjunct, choose one distinct demand per pattern edge (arbitrarily in a
matching; the noncentral demand in a star) and project its second coordinate.
The first conjunct bounds each fibre of this edge-to-terminal map by three.
The choices are local consequences of the existing finite pattern, not a new
incoming proof-history object.

The finite-fibre bound gives `|P| ≤ 3|T|`. Since the same witness carries
`|P| ≥ L_geom = Q_geom + 1`, it gives the effective terminal lower bound
`|T| ≥ ⌈(Q_geom+1)/3⌉`. The registered routing alphabet has at least two
members, hence `|P| ≥ 3`. In the special output `T = {ρ}`, the stronger full
demand counts are decisive: matching has `|D|=2|P|≥6`, and star has
`|D|=|P|+1≥4`; both contradict `|D_ρ|≤3`. Therefore `T\{ρ}` is nonempty.

This is a proposed **terminal** multiplicity restriction. It does not bound
how many routes pass through one edge, first separator, or Type B envelope.
It supplies neither the fixed homogeneous token caps nor the near-cubic
estimate. A Phase 5 admission task must judge whether this bound is an
effective advancement on the full residual and identify the exact survivor.
