# [144a] window history: cycle-rank account of the handoff boundary

Work on the same selected graph `G` and one actual source-and-envelope
`typeBHandoff` witness. Let `S` be the envelope's vertex support: its
core `Y`, decorations `H`, and every recorded arm. Let `F` be the graph
on `S` containing every edge of `G[Y]`, every edge `ha` with `h ∈ H`
and `a ∈ K_h`, and every recorded arm edge, with duplicates included
once. **Connectedness is unknown.** The paper's envelope definition calls
the core connected, but the literal retained handoff proposition has no
core-connectedness field. The concrete producer's two core terminals are
not shown adjacent in that returned proposition. We therefore retain the
actual component count `c(F)` instead of asserting `c(F)=1`.

Write `I = E(G[S]) \ E(F)` for actual internal edges beyond this declared
skeleton. The envelope has a nonempty decoration set, so `S` is nonempty.
The same selected-graph ledger retains connectivity of `G` through its
capacity-token presentation. Hence **every** component `C_1,…,C_r` of
`G-S` has an edge to `S`; put `k_i=|δ_G(C_i)|`. The reviewed cut trace
gives `k_i≥2`, since `G` is bridgeless. `F` may be disconnected, but `G`
is connected.

For any finite graph `X`, define its cycle rank by
`β(X)=|E(X)|−|V(X)|+c(X)`, with `c(X)` its number of connected components.
Directly counting disjoint component vertices, internal edges, and the
`k_i` boundary edges yields the **exact** identity

```
β(G) = β(F) + |I| + Σ_i [β(G[C_i]) + k_i − 1]
       − [c(F) − 1].
```

Indeed, `G[S]` has the same vertices as `F` and exactly `|I|` additional
edges. For each connected `C_i`, its internal edge-minus-vertex count is
`β(G[C_i])−1`; adjoining it adds another `k_i` edges. The final component
count changes from `c(F)` to `c(G)=1`. The nonnegative term
`c(F)−1` counts mergers of previously separate pieces of the
declared skeleton. The simpler formula without this term holds only after
one proves that `F` is connected. Together with the retained exact
`2m=3n+s`, this also reads `β(G)=(n+s)/2+1`; it does not allocate that
global rank to the original blocked pairs.

This correction changes the cost interpretation. An internal edge in `I`
may join two components of `F` and add **no** cycle rank. An attached
component with `k_i≥2` may also spend its boundary edges joining
previously separate pieces, so its positive raw term cannot be charged
independently without accounting for mergers. A non-`h` incidence of an
assigned cubic neighbour may already lie on somebody else's recorded arm
or in `G[Y]`, contributing nothing to `I`; several outside incidences
may enter the same `C_i`. A positive arm `[a,h]` need not consume a
non-`h` incidence, and the outside-incidence set may be empty.

The formula identifies a previously missing relative attachment account.
It gives **no** lower bound on its net cycle-rank increment from the size
of the original source matching/star. The handoff provides no map from
all distinct source pairs to these edges or components, nor a bound on
the multiplicity of such a map. A comparison with the retained global
cycle-rank and surplus ledgers must keep the component-merger term and
prove that map first. No homogeneous cap or closure follows here.

Sources: complete post-[144] ledger in `phase0-evidence.md`;
`erdos_64_proof.tex`, `def:decorated-fan-envelope`; reviewed
`window-phase2-fan-attachments.md` and
`window-phase2-exterior-cut.md`. The literal retained fields are in
`DecoratedHandoffEnvelope.lean:902–940` and
`SpineVocabulary.lean:3944–3979`. The retained capacity-token ledger
supplies connectivity of this same `G`.
