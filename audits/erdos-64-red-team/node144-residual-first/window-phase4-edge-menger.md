# [144] window arm: one textbook linkage/separator candidate

Fix one source tuple of the retained `typeBHandoff` on `G`, choose one of its
declared configurations for each demand in its finite pattern `P`, and let
`ρ` be their common root. Let `H` have precisely the vertices and edges
traversed by this finite route family. Let `T` be the set of their terminal
vertices in `H`. The set `T` is nonempty. Put `T₊ = T \ {ρ}`. This gives an
exhaustive first split:

1. If `T₊ = ∅`, every selected route ends at `ρ`. Since each route is a
   nonempty simple path starting at `ρ`, its vertex list is the singleton
   `[ρ]`. Thus `H` has no route edge. The entire source pattern and all its
   indices remain in this outcome; there is no linkage claim and no closure.
2. If `T₊ ≠ ∅`, apply the theorem below to `ρ` and `T₊`. Any source routes
   ending at `ρ` stay retained but receive no linkage or cut charge from
   this application. When `ρ ∉ T`, this case has `T₊ = T`.

**Finite edge Menger dichotomy.** For a finite undirected graph `H`, a root
`ρ`, a nonempty terminal set `T₊` with `ρ ∉ T₊`, and an integer `k ≥ 1`,
either there are `k` pairwise edge-disjoint paths in `H` from `ρ` to `T₊`, or
there is an edge set `F ⊆ E(H)` with `|F| < k` such that `ρ` and `T₊` are
disconnected in `H − F`. Endpoints in `T₊` may repeat across the disjoint
paths. This is the finite edge-linkage/edge-cut form of Menger's theorem.

The theorem applies to `H` in the `T₊ ≠ ∅` outcome.
Its linked paths are paths in `G` because `H ⊆ G`, but they need not be
declared routes for distinct source pairs and may leave each pair's
declared routing support. Conversely, an edge cut of `H` need not separate
the root from `T₊` in `G`; `G` may have edges outside the route union. Thus
the theorem gives an exact **route-union** split, not a graph-level closure
or pair-capacity charge. The number `k` and the payoff of both outcomes
remain separate obligations.

The manuscript workflow's warning about a Menger dichotomy with no consumer
is in `repair_and_closure.md` §4. This task catalogues the theorem and its
exception arm only. It does not authorize its use as a structural move.
