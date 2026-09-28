import Hypostructure.Graph.Statements.Parameters
import Hypostructure.Graph.CycleCounting.Object

/-!
# Statements: cycles through the vertices of G

The cycle-counting facts of G, each stated at G's own vertices, walks and
cycles (library: `Graph/CycleCounting/`):

* every vertex `h`: `G[N(h)]` is a matching and the nonadjacent pair counts of
  `N(h)`; the star and meeting constraints on two paths of `G − h` to distinct
  neighbours of `h`;
* the pair sums `Σ_{d_h ≠ δ} C(d_h, 2)` against the surplus `σ`;
* every vertex `h`: `G − h` connected, or `d_h` even with every component of
  `G − h` holding exactly two neighbours of `h`; the count of cycles through
  `h`; in the disconnected case the block paths, returns, cross splits and
  their dyadic residues;
* the double count of the cycles at the high vertices.

Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **Neighbourhood pairs of G**: for every vertex `h`, `G[N(h)]` is a
matching, `N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and
every `x ∈ N(h)` has at least `d_h − 2` nonadjacent partners in `N(h)`. -/
noncomputable abbrev NeighbourhoodPairCountStatement (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.CycleCounting.NeighbourhoodPairs object

/-- **Star constraint at G**: for every vertex `h`, distinct neighbours `y, z`
and paths `P : x → y`, `Q : x → z` of `G − h` meeting only at `x`,
`|P| + |Q| + 2 ≠ 2^k` (`k ≥ 2`); in particular two such paths never both have
length `2^j − 1`. -/
abbrev StarCycleConstraintStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.StarConstraint object

/-- **Meeting constraint at G**: for every vertex `h`, distinct neighbours
`y, z` and paths `P : x → y`, `Q : x → z` of `G − h`, the paths meet at a
vertex `t` reached along them by `P₁`, `Q₁` with
`|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`. -/
abbrev MeetingCycleConstraintStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.MeetingConstraint object

/-- **Pair sums at the high vertices of G** `H = {d ≠ δ}`:
`σ = Σ_H (d_h − 3)`, `5σ ≤ Σ_H C(d_h, 2)`,
`σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, `2 Σ_H C(d_h, 2) ≤ 16σ²`, and
`σ = 0` or some `h ∈ H` has `σ ≤ |H|(d_h − 3)`. -/
noncomputable abbrev HighDegreePairSumStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.HighPairSum object data.threshold

/-- **Vertex deletions of G**: for every vertex `h`, `G − h` is connected, or
`d_h` is even, `d_h = 2·#blocks(h)`, and every component of `G − h` meeting
`N(h)` holds exactly two neighbours of `h`. -/
noncomputable abbrev VertexDeletionComponentsStatement (object : Graph.FiniteObject.{u}) :
    Prop :=
  Graph.CycleCounting.VertexDeletionShape object

/-- **Cycles through every vertex of G**: `C(d_h, 2) ≤ #cycles(h)` when
`G − h` is connected; otherwise `2·#pairs(h) = d_h` and `d_h/2 ≤ #cycles(h)`. -/
noncomputable abbrev CyclesThroughVertexStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.CyclesThroughVertex object

/-- **Block paths at the cut vertices of G**: for every vertex `h` with
`G − h` disconnected and every neighbour `a`, the block `{a, b}` of `a`; the
`a → b` paths of `G − h` have `|r| + 2 ≠ 2^k`; every return of `ha` ends by
`bh`; an `a → b` path avoiding `ha`, `hb` avoids `h` (residue `3 mod 4` at
length `2^j − 1`); a path to another block splits at `h` (residue `1 mod 4`,
opposite parities, at length `2^j − 1`). -/
noncomputable abbrev CutVertexBlockPathsStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.BlockPaths object

/-- **Double count of the cycles of G at its high vertices** `H = {d ≠ δ}`:
`2 Σ_H #cycles(h) ≤ n · #cycles(G)`, `2 Σ_H L_h ≤ n · #cycles(G)` with
`L_h = C(d_h, 2)` (`G − h` connected) or `d_h / 2`, and `#cycles(G) ≤ 2^m`. -/
noncomputable abbrev CycleDoubleCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.CycleCounting.CycleDoubleCount object data.threshold

end Hypostructure.Graph.Strategy.Spine
