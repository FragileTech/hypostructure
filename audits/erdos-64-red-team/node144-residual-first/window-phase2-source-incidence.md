# [144a] window history: pair-indexed source routes and physical attachments

Fix the literal post-[144] window ledger on `G = selected.object` and **one**
`typeBHandoff` witness with source matching or star `P` and envelope support
`S`. The separate `windowClassOverload` witness is not identified with it.
The routed-pattern statement quantifies first over `p∈P` and then over
`d∈p`. Its declared support is `sameTokenRoutingSupport token p`, which
depends on `p`. Thus the route index set is

```
I_P = {(p,d): p∈P, d∈p}.
```

For every incidence `(p,d)∈I_P`, choose one of the retained simple
configuration paths `r_{p,d}` from the common token root `ρ` to `d.2`,
inside the **pair-specific** support. Finiteness permits these choices
within the one handoff witness. If a star's centre demand occurs in
several pairs, its selected paths may be different; no cross-pair route
coherence is asserted. Define

```
U_p = ⋃_{d∈p} E(r_{p,d}),
W   = {(p,e): p∈P, e∈U_p}.
```

`W` records every physical graph edge used by at least one of the two
declared routes of each original source pair. It counts an edge once
within a pair even if both routes use it; distinct pairs remain distinct
indices. Write `w_p=|U_p|` and
`n_P(e)=|{p∈P:e∈U_p}|`. The exact identity is
`|W|=Σ_{p∈P}w_p=Σ_{e∈E(G)}n_P(e)`.

Let `D` be the reviewed assignment-indexed non-centre incidence set of
this same envelope and `B={e: ∃(h,a,e)∈D}` its set of **physical** edges.
Restrict the source relation to this set:

```
M = W ∩ (P×B),
z_p = |U_p∩B|,
m_P(e) = |{p∈P:e∈U_p}|   (e∈B),
|M| = Σ_{p∈P} z_p = Σ_{e∈B} m_P(e).
```

The uncovered index set `P_0={p∈P:z_p=0}` and covered set
`P_+={p∈P:z_p>0}` partition `P`. The handoff gives one envelope produced
from two selected source edges; it does not establish `P_0=∅` or a
public all-pair source-to-envelope assignment. The earlier bound
`μ(e)≤4` counts **fan assignments** at a physical edge, not the
different source-pair multiplicity `m_P(e)`.

For each actual component `C` of `G-S`, measure route visits by

```
V = {(p,C): p∈P, some d∈p has a vertex of r_{p,d} in C},
v_p = |{C:(p,C)∈V}|,
m_C(C) = |{p:(p,C)∈V}|,
|V| = Σ_{p∈P} v_p = Σ_C m_C(C).
```

This records repeated visits to one physical component and pairs that
visit none. A visited component need not carry an assigned fan edge.
For a finer crossing count let `b(p,d,C)` be the number of edges of
`r_{p,d}` in `δ_G(C)`, and put
`λ_I(e)=|{(p,d)∈I_P:e∈E(r_{p,d})}|`. Then, for every `C`,

```
Σ_{(p,d)∈I_P} b(p,d,C) = Σ_{e∈δ_G(C)} λ_I(e),
b(p,d,C) ≡ 1_{ρ∈C} + 1_{d.2∈C}  (mod 2).
```

The second identity toggles membership in `C` along the simple route.
A route with both endpoints outside `C` that visits it has at least two
crossings; one with exactly one endpoint inside has at least one.
Repeated star incidences are counted separately in `λ_I`, even when
their paths happen to use the same physical edge. Neither crossing
identity assigns distinct rank cost to distinct source pairs.

The union `R_all` of every `r_{p,d}` is connected because every path
contains `ρ`. This is the full pair-indexed route family. The earlier
reviewed relative-rank identity remains valid for `R_all` and its actual
vertex cut, but its cost terms can be shared by many pair incidences.

These exact relations expose both zero coverage and arbitrary physical
reuse. The retained facts give no positive lower bound on `|P_+|`, no
useful upper bound on `m_P(e)` or `m_C(C)` beyond `|P|`, and no comparison
from the original pattern count to distinct cycle-rank costs. Such a
bound would require a new argument on the complete [144a] residual.

Sources: complete window history in `phase0-evidence.md`;
`ObjectCapacityLedger.lean` lines 144–161 and 651–678 for the
pair-indexed support and routes; reviewed
`window-phase2-route-overlap.md`,
`window-phase2-all-route-boundary.md`, and
`window-phase2-incidence-ledger.md`; prior source-pair account in
`window-phase1-pair-account.md`.
