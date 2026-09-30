import Hypostructure.Graph.LocalRigidity

/-!
# Rungs between two placed windows

For placements `p`, `q` of two 13-vertex windows, `rungSet p q` is the set of position pairs
`(i, j)` with `p i ~ q j`, and `rungCount p q` its size.
-/

namespace Hypostructure.Graph.WindowExchange

open Hypostructure
open Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}

open Classical in
/-- The rungs between two placed 13-vertex windows. -/
noncomputable def rungSet (p q : Fin 13 → object.Vertex) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun ij => object.graph.Adj (p ij.1) (q ij.2)

/-- The number of rungs between two placed 13-vertex windows. -/
noncomputable def rungCount (p q : Fin 13 → object.Vertex) : ℕ := (rungSet p q).card

theorem mem_rungSet {p q : Fin 13 → object.Vertex} {ij : Fin 13 × Fin 13} :
    ij ∈ rungSet p q ↔ object.graph.Adj (p ij.1) (q ij.2) := by
  classical
  unfold rungSet
  simp

end Hypostructure.Graph.WindowExchange
