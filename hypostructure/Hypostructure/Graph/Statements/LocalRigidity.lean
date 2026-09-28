import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.LocalRigidity

/-!
# Statements: local rigidity of G

The configurations G cannot contain around a vertex and across its windows,
each stated at G's own vertices, paths and canonical packing `P₀`
(library: `Graph/LocalRigidity.lean`):

* the length-3 fan at every vertex `h`, and the chain `3, 3, 3`;
* the cross-edge gap of two vertex-disjoint placed paths of G, and at the
  windows of `P₀`: legal attachment labels, `C₁` safety, the gap rule between
  two windows and the excluded ladder;
* the placements of the windows of `P₀` and their per-vertex stub counts.

Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The length-3 fan at G**: at every vertex `h`, two paths `a p₁ p₂ b`,
`a q₁ q₂ c` of length `3` of `G − h` from a neighbour `a` of `h` to distinct
neighbours `b ≠ c` of `h` have `p₁ = q₁`, `p₂ ≠ q₂`, `p₂ ≠ c`, `q₂ ≠ b`; two
such paths with distinct first steps would close the 8-cycle `h b p₂ p₁ a q₁ q₂ c`. -/
abbrev ThreeRouteFanStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.ThreeRouteFan object

/-- **The chain `3, 3, 3` at G**: at every vertex `h`, paths `a p₁ p₂ b`,
`b r₁ r₂ c`, `c q₁ q₂ d` of length `3` of `G − h` between neighbours of `h`
(`a ≠ c`, `b ≠ d`) have `r₁ = p₂` and `r₂ = q₁`. -/
abbrev ThreeRouteChainStatement (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.ThreeRouteChain object

/-- **The cross-edge gap at G and at the windows of `P₀`**: two
vertex-disjoint placed paths of G joined at `(i, j)` and `(i', j')` have
`|i − i'| + 2 + |j − j'|` not accepted; at every placed window of `P₀`, every
outside vertex carries a legal label (in `Labels 13`), two adjacent outside
vertices carry `C₁`-safe labels, two distinct windows obey the same gap rule,
and no two windows form a ladder. -/
noncomputable abbrev WindowAttachmentGapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.CrossGap object ∧
    Graph.LocalRigidity.WindowAttachmentRules object data.windowOrder
      (canonicalWindowPacking data object)

/-- **Window positions of `P₀`**: every window of `P₀` has a placement; at
every placement an interior vertex carries `d − 2` external neighbours (exactly
one when cubic) and an end vertex `d − 1`. -/
noncomputable abbrev WindowPositionStubsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.LocalRigidity.WindowPositionStubs object data.windowOrder
    (canonicalWindowPacking data object)

end Hypostructure.Graph.Strategy.Spine
