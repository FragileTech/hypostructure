import Hypostructure.Graph.WedgeLowerBound

/-!
# The raw internal curvature tests of a region

`def:curvature-target-rank` computes a rank over `𝒲₂(C)`, "the set of raw
internal length-two curvature tests in `C`".  `Graph.WedgeLowerBound` already
counts them — `internalWedgeCount` is `Σ_{v∈X} C(d_X(v), 2)` — but a rank is
taken over the *family*, not over its size: a subfamily has to be nameable
before it can survive a quotient.

This module names it.  A raw internal curvature test at a region `X` is a
centre in `X` together with an unordered pair of two distinct neighbours of
that centre inside `X`, which is what a length-two wedge is; the family is the
sigma of those pairs over the centres, and `internalWedgeFamily_card` says it
has exactly `W₂(X)` members, so the family and the count are the same object
seen twice.

Nothing here mentions curvature, rank, or a quotient: those live where the rank
is taken.
-/

namespace Hypostructure.Graph

namespace FiniteObject

universe u

/-- The neighbours a vertex has inside a support.  Its cardinality is
`internalDegree`, which is how it is defined. -/
noncomputable def internalNeighborFinset (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  exact (object.graph.neighborFinset vertex) ∩ support

@[simp] theorem card_internalNeighborFinset (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    (object.internalNeighborFinset support vertex).card =
      object.internalDegree support vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  simp [internalNeighborFinset, internalDegree]

/-- **A raw internal length-two curvature test of a region.**  A centre
together with an unordered pair of two of its neighbours inside the region.
No response value, quotient image, or rank outcome is stored: the test is the
coordinate, and what a quotient does to it is the quotient's business. -/
abbrev InternalWedge (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Type u :=
  Σ centre : object.Vertex,
    { pair : Finset object.Vertex //
      pair ∈ (object.internalNeighborFinset support centre).powersetCard 2 }

/-- **`𝒲₂(X)`**: the exact finite family of raw internal curvature tests of a
region. -/
noncomputable def internalWedgeFamily (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    Finset (object.InternalWedge support) :=
  support.sigma fun centre =>
    ((object.internalNeighborFinset support centre).powersetCard 2).attach

/-- The family has exactly as many members as the count counts: `|𝒲₂(X)| =
W₂(X)`.  This is what lets a rank taken over the family be compared with the
wedge lower bound proved for the count. -/
theorem internalWedgeFamily_card (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    (object.internalWedgeFamily support).card =
      object.internalWedgeCount support := by
  classical
  rw [internalWedgeFamily, Finset.card_sigma, internalWedgeCount]
  refine Finset.sum_congr rfl fun centre _member => ?_
  rw [Finset.card_attach, Finset.card_powersetCard, card_internalNeighborFinset]

end FiniteObject

end Hypostructure.Graph
