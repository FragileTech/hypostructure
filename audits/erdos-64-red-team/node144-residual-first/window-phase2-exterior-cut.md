# [144a] window history: the boundary of each exterior component

Fix the complete post-[144] window-arm ledger on `G = selected.object` and
the source pattern and decorated envelope carried by one `typeBHandoff`
witness. Let `S` be the vertex union of that envelope's core `Y`, high
decorations `H`, and recorded arms. This is the same support used in the
reviewed first-neighbour incidence inventory. It contains every assigned
first neighbour `a ∈ K_h` and the edge `ha` has both endpoints in `S`.

**Conditional trace of an actual outside edge.** Suppose an assigned cubic
first neighbour `a` has an edge `ax` with `x ∉ S`, and let `C` be the
component of the induced graph `G-S` containing `x`. Define `δ_G(C)` to
be the edges with exactly one endpoint in `C`. The edge `ax` lies in
`δ_G(C)`. There is a second, distinct edge `ys ∈ δ_G(C)` with `y ∈ C`
and `s ∈ S`: if `ax` were its only boundary edge, deleting `ax` would
separate `C` from every vertex outside `C`, making `ax` a bridge of `G`.
The retained `bridgeless` fact rules this out. This uses a cut in the
actual graph `G`, unlike the earlier auxiliary cut in a union of selected
source routes.

The landing `s` is not prescribed. It can lie in the core, a recorded arm,
a high decoration, or another assigned first neighbour; these descriptions
can overlap when an arm has length zero or arms share later vertices.
It may even equal `a` if both of `a`'s non-`h` edges enter the same exterior
component. For an arm of **positive length whose first edge differs from
`ha`**, one non-`h` edge continues the recorded arm inside `S`; since
`d_G(a)=3`, `ax` is its only edge from `a` to `G-S`. Under that additional
condition the second boundary edge has `s ≠ a`. Positive length by itself
does not supply the condition: the literal retained envelope permits an arm
`[a,h]` ending in `Y` when `h ∈ Y`, and its first edge is `ha`. For a
**length-zero** arm, `a ∈ Y`, and the same-`a` landing also remains possible.
The second attachment need not land at another member of
`K_h`, nor at a vertex associated with any other source pair.

If there is no outside incidence at any assigned neighbour, there is no
component to which this cut argument applies. This case remains live. If
outside incidences exist, the result is a two-edge boundary for each
component they meet, with the stated landing exceptions. It does not give
the length of a return, a forbidden cycle, a bound on the original
matching/star, or a charge against strict surplus. The handoff still
publishes one envelope selected from two source edges and no map from all
source pairs to these boundary edges.

The earlier Type B local profile classifies the two non-`h` incidences of
cubic-closed neighbours by window location. That prior count does not
establish cubic closure for every assigned neighbour and does not record
this exterior-component boundary. The earlier route-union cut did not
constitute a cut of `G`. The unresolved interaction is where each forced
second attachment lands relative to the *same* source pattern and whether
that landing has a proved local consumer.

Sources: the complete ledger in `phase0-evidence.md`; `erdos_64_proof.tex`,
`def:decorated-fan-envelope`, `def:marked-typeB-fan`, and
`def:typeB-window-incidence-profile`; reviewed
`window-phase2-fan-attachments.md`; prior
`window-phase5-terminal-significance.md`. The literal envelope and handoff
contracts are `DecoratedHandoffEnvelope.lean:902–940` and
`SpineVocabulary.lean:3944–3979`; the producer's local separator avoidance
is not exported by this handoff proposition.
