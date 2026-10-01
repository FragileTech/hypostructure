import Hypostructure.Graph.Statements.SparseExitResidual
import Hypostructure.Graph.EdgeSwitchPaths
import Hypostructure.Graph.Statements.SwitchForcedPaths

/-!
# Statements: the edge switches of G

Facts about G and its fixed objects, each stated over the registered
`Parameters`:

* **Edge switches of G** (from the selection, the baseline and the tight/slack
  structure): two high vertices, or one vertex of degree `≥ δ + 2`, force paths
  in G minus two edges whose length plus one is accepted; where the surplus of G
  sits; the switch at every high/baseline edge.

Every registered constant is an explicit `Parameters` argument; this module
imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-! ## Edge switches of G -/

/-- **Where the surplus of G sits**: G has a vertex of degree `≥ δ + 2`, or two
distinct vertices of degree exactly `δ + 1`. -/
def HighSurplusConfigurationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (∃ h, data.threshold + 2 ≤ object.degree h) ∨
    ∃ h₁ h₂, h₁ ≠ h₂ ∧ object.degree h₁ = data.threshold + 1 ∧
      object.degree h₂ = data.threshold + 1

/-- **The switch at every high/baseline edge `hc`**: a forced path from `c`,
by the same-vertex switch at `h` when `deg h ≥ δ + 2` (to a neighbour `u` of
`h` with `u ≠ c`, `u ≁ c`, in `G − {hc, hu}`), else by the two-edge switch with
a second high vertex `h₂ ≠ h` and its neighbour `u₂ ≠ c`, `u₂ ≁ c` (in
`G − {ch, u₂h₂}`). -/
def HighEndpointSwitchStatement (data : Parameters) (object : Graph.FiniteObject.{u}) :
    Prop :=
  ∀ h c : object.Vertex, data.threshold + 1 ≤ object.degree h →
    object.degree c = data.threshold → object.graph.Adj h c →
    (data.threshold + 2 ≤ object.degree h ∧ ∃ u, object.graph.Adj h u ∧ u ≠ c ∧
        ¬ object.graph.Adj c u ∧
        ∃ p : (object.graph.deleteEdges {s(h, c), s(h, u)}).Walk c u,
          p.IsPath ∧ data.LengthOK (p.length + 1)) ∨
      ∃ h₂ u₂, h₂ ≠ h ∧ data.threshold + 1 ≤ object.degree h₂ ∧
        object.graph.Adj u₂ h₂ ∧ u₂ ≠ c ∧ ¬ object.graph.Adj c u₂ ∧
        ∃ p : (object.graph.deleteEdges {s(c, h), s(u₂, h₂)}).Walk c u₂,
          p.IsPath ∧ data.LengthOK (p.length + 1)

end Hypostructure.Graph.Strategy.Spine
