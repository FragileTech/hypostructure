import Hypostructure.Graph.Statements.Route8RateFailsRoute
import Hypostructure.Graph.Statements.LocalRigidity
import Hypostructure.Graph.Statements.JointHubs
import Hypostructure.Graph.WindowRPathCycle

/-!
# Statements: cycles through two windows via the remainder, and the stubs to hubs

G audit of `Route8RateFailsOutcome` (thin arm): on the thin remainder almost all window
stubs go to `R`.  Two windows of `P₀`, joined through `R` by two vertex-disjoint paths at
fixed stub positions, close a cycle whose length is fixed by the positions and the two
path sizes; it must avoid every power of two.  The stubs to vertices above the baseline
(hubs) are bounded by the degree surplus.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **Cycles through two windows via `R`.**  For distinct windows `P ≠ Q` of `P₀` with
placements `p`, `q`, stub positions `i, i'` on `p` and `j, j'` on `q`, and vertex-disjoint
paths `r₁ : a₁ ⇝ b₁`, `r₂ : a₂ ⇝ b₂` of `G` inside the remainder with
`p i – a₁`, `b₁ – q j`, `p i' – a₂`, `b₂ – q j'` edges, the cycle they close has length
`|i−i'| + |j−j'| + |r₁| + |r₂| + 4` (`|r|` the edge length), and it is not a power of two. -/
def Route8WindowRPathGapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ P ∈ canonicalWindowPacking data object, ∀ Q ∈ canonicalWindowPacking data object,
    P ≠ Q →
    ∀ p q : Fin data.windowOrder → object.Vertex,
      Graph.LocalRigidity.IsWindowPlacement object P p →
      Graph.LocalRigidity.IsWindowPlacement object Q q →
      ∀ (i i' j j' : Fin data.windowOrder) (a₁ b₁ a₂ b₂ : object.Vertex)
        (r₁ : object.graph.Walk a₁ b₁) (r₂ : object.graph.Walk a₂ b₂),
        r₁.IsPath → r₂.IsPath →
        (∀ v ∈ r₁.support, v ∈ object.remainderSupport (canonicalWindowPacking data object)) →
        (∀ v ∈ r₂.support, v ∈ object.remainderSupport (canonicalWindowPacking data object)) →
        (∀ v ∈ r₁.support, v ∉ r₂.support) →
        object.graph.Adj (p i) a₁ → object.graph.Adj b₁ (q j) →
        object.graph.Adj (p i') a₂ → object.graph.Adj b₂ (q j') →
        ¬ Core.DyadicLength.PowerOfTwoLength
          (Nat.dist i.1 i'.1 + Nat.dist j.1 j'.1 + r₁.length + r₂.length + 4)

/-- The hub incidences of a vertex: its neighbours of degree above the baseline. -/
noncomputable def hubNeighbours (object : Graph.FiniteObject.{u}) (threshold : Nat)
    (vertex : object.Vertex) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (Finset.univ.filter fun other => threshold < object.degree other).filter
    fun other => object.graph.Adj vertex other

/-- **The stubs to hubs.**  The incidences from the windows of `P₀` to vertices of degree
above the baseline number at most `(δ+1)·σ(G)`: by double counting they are at most the
degree sum of the hubs, and a hub of degree `δ + t`, `t ≥ 1`, has degree
`≤ (δ+1)·t`.  So at `σ_W = 0` (all window vertices cubic) all but `(δ+1)·T(n)` of the
`15p` window stubs go to cubic vertices of `R` or of other windows. -/
noncomputable def Route8HubStubsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∑ vertex ∈ object.windowSupport (canonicalWindowPacking data object),
      (hubNeighbours object data.threshold vertex).card ≤
    (data.threshold + 1) * object.degreeSurplus data.threshold

/-- **Cycles through one window via `R`.**  A path of the remainder joining two stubs of one
window `P` (positions `i`, `i'`, with `i ≠ i'` or distinct end vertices) closes a cycle of
length `|i−i'| + |r| + 2` with the window path; it is not a power of two.  At `|r| = 0`
(one remainder vertex) this is the attachment rule; for a longer path it is new. -/
def Route8WindowSelfRPathGapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ P ∈ canonicalWindowPacking data object,
    ∀ p : Fin data.windowOrder → object.Vertex,
      Graph.LocalRigidity.IsWindowPlacement object P p →
      ∀ (i i' : Fin data.windowOrder) (a b : object.Vertex)
        (r : object.graph.Walk a b), r.IsPath →
        (∀ v ∈ r.support, v ∈ object.remainderSupport (canonicalWindowPacking data object)) →
        object.graph.Adj (p i) a → object.graph.Adj b (p i') → (i ≠ i' ∨ a ≠ b) →
        ¬ Core.DyadicLength.PowerOfTwoLength (Nat.dist i.1 i'.1 + r.length + 2)

/-- **The pieces of the remainder against the bridgeless cut.**  With a window present every
canonical piece `X` of `G[R]` is a nonempty proper set, so at least two edges leave it
(`DensityExcess`), and the pieces partition the cut: `2·#pieces ≤ |∂R|`. -/
noncomputable def Route8PieceBoundaryStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (canonicalWindowPacking data object).Nonempty →
    (∀ piece ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
      2 ≤ object.boundaryIncidence (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece)) ∧
    2 * (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))).card ≤
      object.boundaryIncidence (object.remainderSupport (canonicalWindowPacking data object))

end Hypostructure.Graph.Strategy.Spine
