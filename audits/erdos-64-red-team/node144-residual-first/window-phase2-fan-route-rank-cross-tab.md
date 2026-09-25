# [144a] window history: fan edges against the full route-rank account

Fix the literal post-[144] window ledger on `G=selected.object` and one
`typeBHandoff` witness. Use its source pattern `P`, envelope vertex
support `S`, skeleton `F`, and assignment incidence set
`D={(h,a,e):h∈H, a∈K_h, e` is incident to `a`, `e≠ha}`.
Put `A={(h,a):h∈H,a∈K_h}`. Let
`B={e:∃(h,a,e)∈D}` and `μ(e)=|{(h,a):(h,a,e)∈D}|`. All these are from
the same witness. The separate window-overload existential is not
identified with it.

Choose a declared route `r_{p,d}` for **each** incidence
`(p,d)` with `p∈P,d∈p`, inside the support for that `p`. Let
`R` be the union of every chosen path and `T=V(R)`. Every path starts
at the common token root, so `R` is connected. Define
`J=E(G[T])∖E(R)`. The actual graph `G-T` has components `C`;
write `∂_T C=δ_G(C)` and `E_C=E(G[C])`.

There are two independent **disjoint exhaustive** partitions of `B`:

* Envelope location: `B_F=B∩E(F)`,
  `B_I=B∩(E(G[S])∖E(F))`, and `B_∂=B∩δ_G(S)`.
  Every `e∈B` meets `S` at its assigned first neighbour.
* Route location: `B_R=B∩E(R)`, `B_J=B∩J`,
  `B_{∂,C}=B∩∂_T C` for each component `C` of `G-T`,
  and `B_{E,C}=B∩E_C` for each such `C`.
  An edge outside `E(G[T])` has either one endpoint outside `T`,
  in which case it belongs to one `∂_T C`, or both outside `T`,
  in which case they lie in one component `C`.

For an envelope row `u∈{F,I,∂}` and a route column `v` from the
second list, put `B_{u,v}=B_u∩B_v` and
`D_{u,v}={(h,a,e)∈D:e∈B_{u,v}}`. These cells include empty cells;
no assumption that `S⊆T` or `T⊆S` deletes one. They give exact
identities

```
|D| = 2|A| = Σ_u Σ_v |D_{u,v}|
           = Σ_u Σ_v Σ_{e∈B_{u,v}} μ(e),
|B| = Σ_u Σ_v |B_{u,v}|.
```

Each envelope-row sum recovers the reviewed `D_F,D_I,D_∂` count.
Each route-column sum measures exactly how many *assignment incidences*
fall on existing routes, on extra chords, at the actual `G-T`
boundary, or inside actual exterior components. The `G-S` and
`G-T` component families are different cuts and are not identified.

The pair-to-fan-edge relation from the preceding measurement is
`M={(p,e):p∈P, e∈U_p∩B}`, where
`U_p=⋃_{d∈p}E(r_{p,d})`. Since `E(R)=⋃_{p∈P}U_p`,
the physical edge support of `M` is **exactly** `B_R`:

```
B_R = {e∈B:∃p∈P, (p,e)∈M}.
```

Consequently `m_P(e)≥1` on `B_R`, while every edge in
`B∖B_R` has `m_P(e)=0` for these chosen declared routes. This is
an exact relation between source indices and physical edges, not a
claim that every `p` meets `B`. The uncovered `P_0` remains possible.

The reviewed rank identity for this connected `R` is

```
β(G) = β(R) + |J| + Σ_C [β(G[C]) + |∂_T C| − 1].
```

An edge in `B_J` contributes one of the `|J|` units. An edge in
`B_R` is already part of `R`; even its assignment multiplicity and
source-pair multiplicity do not make it a *new* relative-rank unit.
Its contribution to `β(R)` depends on the whole connected route
network (or on a chosen spanning tree). Boundary and component-internal
edges enter their component's rank term **collectively**; the term is
not one unit per such edge or per assignment. The exact equality
`2|A|=Σ|D_{u,v}|` therefore supplies no lower bound on the positive
terms of the rank formula from `|A|` or `|P|`. Multiple assignments
and source pairs may occupy the same physical route edge.

This table measures every represented fan incidence against both
partitions. It does not determine the values of the cells, the return
lengths of exterior attachments, or a bounded source-pair-to-rank
charge. In particular, it does not import the distinct
`windowClassOverload` witness's excess into this envelope account.

Sources: full window ledger in `phase0-evidence.md`; reviewed
`window-phase2-incidence-ledger.md`,
`window-phase2-source-incidence.md`, and
`window-phase2-all-route-boundary.md`. The pair-dependent route
support is in `ObjectCapacityLedger.lean` lines 144–161 and
651–678.
