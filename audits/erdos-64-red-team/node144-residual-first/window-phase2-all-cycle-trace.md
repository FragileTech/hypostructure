# [144a] window history: complete cycle trace relative to source routes

Fix the literal post-[144] window ledger on `G=selected.object` and
one `typeBHandoff` witness. Choose one declared route for each
source-pair/demand incidence, retaining its pair-specific support.
Let `R` be the union of these routes, `T=V(R)`,
`J=E(G[T])∖E(R)`, and `C` range over components of the actual
`G-T`. Retain the same witness's physical fan-edge set `B` and
the original pair route-edge sets `U_p`. The earlier `G-S`
envelope cut remains a different partition.

Every simple cycle `Z` of `G` falls in **exactly one** of these
four categories:

1. `V(Z)⊆T` and `E(Z)⊆E(R)`: wholly in the selected route
   network.
2. `V(Z)⊆T` and `E(Z)∩J≠∅`: wholly on route vertices but
   using at least one extra chord.
3. `V(Z)∩T=∅`: wholly in one component `C` of `G-T`.
   A connected cycle cannot span two different such components.
4. `V(Z)∩T≠∅` and `V(Z)∖T≠∅`: mixed.

The first two categories partition cycles wholly on `T`, because
`E(G[T])=E(R)⊔J`. The third covers all cycles outside `T`.
These facts prove disjointness and coverage without assuming any
relation between `T` and the handoff envelope support.

For a mixed `Z`, walk around its cyclic vertex list. Each maximal
consecutive run of vertices outside `T` lies in one component
`C_i` of `G-T`. It is a simple internal path `P_i` (possibly
one vertex, with zero internal edges), preceded and followed by
distinct boundary **edges** `b_i^-,b_i^+∈δ_G(C_i)`.
Their endpoints in `T` may coincide. If they do, the simple-cycle
condition forces `P_i` to have at least one edge: a one-vertex
outside run would repeat the same physical boundary edge in a
simple graph.

The intervening maximal runs on `T` are simple paths `Q_i` in
`G[T]`, possibly trivial when two exterior excursions meet at
one `T` vertex. They may use edges of `R` and of `J`. The
outside and inside runs alternate cyclically, and

```
|E(Z)| = Σ_i (|E(P_i)| + 2) + Σ_i |E(Q_i)|.
```

The same component can occur in several outside runs of one cycle;
these are separately indexed excursions. This is a trace of an
**existing simple cycle**. Arbitrary choices of component paths and
`T` paths need not concatenate to a simple cycle, so the formula
does not manufacture one.

For every category, keep the exact physical fan marker
`E(Z)∩B` and original pair-use numbers
`a_Z(p)=|E(Z)∩U_p|`. Since every `U_p⊆E(R)`,
`a_Z(p)` counts only `R` edges. It is zero for a cycle in
category 3, and it never counts a chord or an exterior edge,
even when that edge belongs to `B`. Repeated pairs on an
`R` edge are retained as separate indices in the preceding
source-incidence ledger.

The elementary chord spectrum previously measured exactly the
category-2 cycles with **one** `J` edge and all remaining edges
in `R`. The elementary return spectrum measured exactly those
mixed cycles with **one** outside run and a complementary `T`
path wholly in `R` (including its trivial-path landing case).
Other cycles in categories 1–4 now have an explicit trace
category, but their lengths are not determined by the elementary
spectra. In particular, several excursions, repeated use of one
component, or several chords remain live configurations.

The retained `selection` fact supplies
`¬LengthOK |E(Z)|` for **every** simple cycle `Z` in all four
categories. This target exclusion was already known globally.
The trace does not prove that the additive length of any
prospective configuration is `LengthOK`, nor a lower bound on
distinct rank costs per original pair. It makes the unmeasured
multi-excursion and whole-route-cycle cases explicit rather than
treating the elementary spectra as all cycles.

Sources: complete window ledger in `phase0-evidence.md`; reviewed
`window-phase2-source-incidence.md`,
`window-phase2-fan-route-rank-cross-tab.md`,
`window-phase2-route-return-length-profile.md`, and
`window-phase2-route-reuse-support-profile.md`.
