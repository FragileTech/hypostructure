import Hypostructure.Graph.Statements.Parameters
import Hypostructure.Graph.SwitchForcedPaths

/-!
# Statements: the forced paths and cycles of G's switches and vertex splits

Every lexicographically smaller baseline object carries an accepted cycle, and
G does not.  An edge switch or a vertex split of G that keeps the baseline
with fewer edges or vertices is such an object, so each one forces an explicit
accepted path or cycle of G, at G's own vertices:

* the two-edge switch `G − {u₁v₁, u₂v₂} + u₁u₂` at two edges whose far ends
  have slack (`TwoSwitchForcedPathStatement`);
* the same-vertex switch `G − {hu₁, hu₂} + u₁u₂` at a centre of degree at
  least `δ + 2`, with the exact split of the forced path by the return
  avoidance of G (`SameVertexSwitchForcedPathStatement`);
* the vertex split `(G − h) ⊔ M_h` at every high centre `h`, `M_h` the
  non-adjacent pairs of `N(h)` (`HighCentreSplitForcedStatement`);
* the cross-vertex switch family at an edge `u₁v` and a second high vertex
  `h'`, with the dyadic star obstruction on equal-length forced paths
  (`CrossSwitchFamilyStatement`).

Each statement is a fact about G, stated at G's concrete vertices; the
registered constants are explicit `Parameters` fields.  This module imports no
strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The two-edge switch of G forces a path.**  For edges `u₁v₁`, `u₂v₂` of G
with `u₁, v₁, u₂, v₂` distinct, `u₁ ≁ u₂` and `deg v₁, deg v₂ ≥ δ + 1`, the
graph `G − {u₁v₁, u₂v₂}` has a simple `u₁`–`u₂` path `p` with `|p| + 1`
accepted. -/
def TwoSwitchForcedPathStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ ⦃u₁ v₁ u₂ v₂ : object.Vertex⦄,
    object.graph.Adj u₁ v₁ → object.graph.Adj u₂ v₂ →
    u₁ ≠ u₂ → u₁ ≠ v₂ → v₁ ≠ u₂ → v₁ ≠ v₂ → ¬ object.graph.Adj u₁ u₂ →
    data.threshold + 1 ≤ object.degree v₁ → data.threshold + 1 ≤ object.degree v₂ →
    ∃ p : (object.graph.deleteEdges {s(u₁, v₁), s(u₂, v₂)}).Walk u₁ u₂,
      p.IsPath ∧ data.LengthOK (p.length + 1)

/-- **The same-vertex switch of G forces a path, and splits it exactly.**  For
non-adjacent neighbours `u₁ ≠ u₂` of a vertex `h` of G with
`deg h ≥ δ + 2`, the graph `G − {hu₁, hu₂}` has a simple `u₁`–`u₂` path `p`
with `|p| + 1` accepted; and either `p` avoids `h` and the closing cycle
`p + u₂h + hu₁` of length `|p| + 2` is not accepted, or `p` passes through `h`
and splits into two returns of `hu₁`, `hu₂` of lengths `ℓ₁ + ℓ₂ = |p|` with
neither `ℓᵢ + 1` accepted. -/
def SameVertexSwitchForcedPathStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ ⦃h u₁ u₂ : object.Vertex⦄,
    object.graph.Adj h u₁ → object.graph.Adj h u₂ → u₁ ≠ u₂ →
    ¬ object.graph.Adj u₁ u₂ → data.threshold + 2 ≤ object.degree h →
    ∃ p : (object.graph.deleteEdges {s(h, u₁), s(h, u₂)}).Walk u₁ u₂,
      p.IsPath ∧ data.LengthOK (p.length + 1) ∧
        ((h ∉ p.support ∧ ¬ data.LengthOK (p.length + 2)) ∨
          ∃ ℓ₁ ℓ₂, ℓ₁ + ℓ₂ = p.length ∧ ¬ data.LengthOK (ℓ₁ + 1) ∧
            ¬ data.LengthOK (ℓ₂ + 1))

/-- **The vertex split of G at every high centre forces a cycle.**  At every
vertex `h` of G of degree above `δ`, the graph `G ⊔ M_h` (`M_h` the
non-adjacent pairs of `N(h)`) has an accepted cycle that avoids `h` and uses
an edge of `M_h` absent from G. -/
def HighCentreSplitForcedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ h : object.Vertex, data.threshold < object.degree h →
    ∃ (v : object.Vertex)
      (c : (object.graph ⊔ Graph.SwitchForcedPaths.antiPairs object h).Walk v v),
      c.IsCycle ∧ data.LengthOK c.length ∧ h ∉ c.support ∧
        ∃ e ∈ c.edges, e ∈ (Graph.SwitchForcedPaths.antiPairs object h).edgeSet ∧
          e ∉ object.graph.edgeSet

/-- **The cross-vertex switch family of G.**  Fix an edge `u₁v` of G and a
vertex `h' ≠ v`, both `v` and `h'` of degree at least `δ + 1`.  Every
neighbour `u` of `h'` with `u ≁ u₁` (four distinct endpoints) has a forced
simple path `u₁ → u` in `G − {u₁v, uh'}` with accepted closing length; and two
simple paths of G from `u₁` into two distinct neighbours of `h'`, both of
length `2^j − 1` (`j ≥ 1`), are never simultaneously `h'`-free and internally
disjoint. -/
def CrossSwitchFamilyStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ ⦃u₁ v h' : object.Vertex⦄, object.graph.Adj u₁ v → v ≠ h' →
    data.threshold + 1 ≤ object.degree v → data.threshold + 1 ≤ object.degree h' →
    (∀ u, object.graph.Adj u h' → u ≠ u₁ → u ≠ v → u₁ ≠ h' → ¬ object.graph.Adj u₁ u →
      ∃ p : (object.graph.deleteEdges {s(u₁, v), s(u, h')}).Walk u₁ u,
        p.IsPath ∧ data.LengthOK (p.length + 1)) ∧
    (∀ u u' j (P : object.graph.Walk u₁ u) (Q : object.graph.Walk u₁ u'),
      object.graph.Adj u h' → object.graph.Adj u' h' → u ≠ u' → 1 ≤ j →
      P.IsPath → Q.IsPath → P.length + 1 = 2 ^ j → Q.length + 1 = 2 ^ j →
      ¬ (h' ∉ P.support ∧ h' ∉ Q.support ∧ ∀ w ∈ P.support, w ∈ Q.support → w = u₁))

end Hypostructure.Graph.Strategy.Spine
