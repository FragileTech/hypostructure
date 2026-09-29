import Hypostructure.Graph.Statements.Route8WindowRPath

/-!
# Statements: the window-piece multigraph, its cycle rank, and the achievable cycle lengths

G audit of `Route8RateFailsOutcome` (thin arm).  Windows of `P₀` and canonical pieces of
`G[R]` are the vertices of the stub multigraph `B` (one edge per stub, `e(R,W)` edges).  Every
choice of stubs and of paths inside the pieces closes a cycle of `G`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The lengths of the paths from `a` to `b` inside a vertex set `X`: the set of cycle
lengths a piece can contribute between two stubs. -/
def pieceLengthSet (object : Graph.FiniteObject.{u}) (X : Finset object.Vertex)
    (a b : object.Vertex) : Set Nat :=
  {length | ∃ r : object.graph.Walk a b, r.IsPath ∧ (∀ v ∈ r.support, v ∈ X) ∧
    r.length = length}

/-- **The cycle rank of the window-piece multigraph.**  `B` has `p + #pieces` vertices and one
edge per stub, `e(R,W)` edges, and (with a window present) `2·#pieces ≤ e(R,W)`.  Its cycle
rank is at least `e(R,W) − (p + #pieces)`, and with the exact window join
`e(R,W) + X = β·p + σ_W`:

  `β·p + σ_W ≤ 2·(e(R,W) − (p + #pieces)) + 2p + X`,

i.e. the number of independent cycles of `B` is at least `(β − 2)p/2 − X/2 + σ_W/2`
(`6.5 p` at `β = 15`). -/
noncomputable def Route8WindowPieceRankStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (canonicalWindowPacking data object).Nonempty →
    coldExternalStubCount data * (canonicalWindowPacking data object).card +
        object.ambientSurplus (object.windowSupport (canonicalWindowPacking data object))
          data.threshold ≤
      2 * (object.boundaryIncidence (object.remainderSupport (canonicalWindowPacking data object)) -
          ((canonicalWindowPacking data object).card +
            (object.canonicalPieces
              (object.remainderSupport (canonicalWindowPacking data object))).card)) +
        2 * (canonicalWindowPacking data object).card +
        (object.crossWindowIncidences (canonicalWindowPacking data object)).card

/-- **The achievable lengths of the pieces and the cycles of `B`.**
* between any two vertices of a canonical piece the set of path lengths inside the piece is
  nonempty (the piece is connected) and each length is below the piece size;
* two distinct windows and two distinct pieces, with stubs at fixed positions, close a cycle
  for every choice of a path in each piece: every element of the sumset
  `dist(i,i') + dist(j,j') + L_X(a₁,b₁) + L_Y(a₂,b₂) + 4` is not a power of two;
* one window and one piece: every `dist(i,i') + L_X(a,b) + 2` is not a power of two. -/
noncomputable def Route8AchievableLengthsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  (∀ piece ∈ object.canonicalPieces remainder,
      ∀ a ∈ object.pieceSupport remainder piece, ∀ b ∈ object.pieceSupport remainder piece,
        (pieceLengthSet object (object.pieceSupport remainder piece) a b).Nonempty ∧
          ∀ length ∈ pieceLengthSet object (object.pieceSupport remainder piece) a b,
            length < (object.pieceSupport remainder piece).card) ∧
    (∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q →
      ∀ p q : Fin data.windowOrder → object.Vertex,
        Graph.LocalRigidity.IsWindowPlacement object P p →
        Graph.LocalRigidity.IsWindowPlacement object Q q →
        ∀ X ∈ object.canonicalPieces remainder, ∀ Y ∈ object.canonicalPieces remainder, X ≠ Y →
        ∀ (i i' j j' : Fin data.windowOrder) (a₁ b₁ a₂ b₂ : object.Vertex),
          a₁ ∈ object.pieceSupport remainder X → b₁ ∈ object.pieceSupport remainder X →
          a₂ ∈ object.pieceSupport remainder Y → b₂ ∈ object.pieceSupport remainder Y →
          object.graph.Adj (p i) a₁ → object.graph.Adj b₁ (q j) →
          object.graph.Adj (p i') a₂ → object.graph.Adj b₂ (q j') →
          ∀ ℓ₁ ∈ pieceLengthSet object (object.pieceSupport remainder X) a₁ b₁,
          ∀ ℓ₂ ∈ pieceLengthSet object (object.pieceSupport remainder Y) a₂ b₂,
            ¬ Core.DyadicLength.PowerOfTwoLength
              (Nat.dist i.1 i'.1 + Nat.dist j.1 j'.1 + ℓ₁ + ℓ₂ + 4)) ∧
    (∀ P ∈ packing, ∀ p : Fin data.windowOrder → object.Vertex,
      Graph.LocalRigidity.IsWindowPlacement object P p →
      ∀ X ∈ object.canonicalPieces remainder,
      ∀ (i i' : Fin data.windowOrder) (a b : object.Vertex),
        a ∈ object.pieceSupport remainder X → b ∈ object.pieceSupport remainder X →
        object.graph.Adj (p i) a → object.graph.Adj b (p i') → (i ≠ i' ∨ a ≠ b) →
        ∀ ℓ ∈ pieceLengthSet object (object.pieceSupport remainder X) a b,
          ¬ Core.DyadicLength.PowerOfTwoLength (Nat.dist i.1 i'.1 + ℓ + 2))

end Hypostructure.Graph.Strategy.Spine
