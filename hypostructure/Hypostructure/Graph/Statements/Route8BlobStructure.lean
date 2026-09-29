import Hypostructure.Graph.Statements.RouteEight
import Hypostructure.Graph.Statements.Route8WindowPieceLengths

/-!
# Statements: the pieces of the remainder against the windows of `P₀` (route 8, rate arm)

On the branch where the private-carrier rate `K .route8Rate` holds,
`(δs+1)·|∂R| + δ·slack < δ·|R|` (`Route8Census.Rate` at `P₀`), the uncontrolled term is the
remainder `R = G − W(P₀)`.  These statements name its canonical pieces `X` (components of
`G[R]`, `canonicalPieces`), their exits (edges of `G` from `X` to a window of `P₀`, at a
position of a placement `IsWindowPlacement`), and the rate term itself:

* `Route8PieceWindowAttachmentStatement` (key `9900`): two exits of one piece landing on one
  window at positions `i`, `i'` close, with every internal path of length `ℓ` between the exit
  vertices, a cycle of length `ℓ + |i−i'| + 2`, which is not a power of two; hence every run
  `[lo, hi]` of internal path lengths satisfies the dyadic run bound.
* `Route8PieceChainCycleStatement` (key `9901`): `k` distinct pieces and `k` distinct windows
  joined cyclically by exits close, for every choice of internal path lengths `ℓᵢ`, a cycle of
  length `Σ ℓᵢ + Σ |jᵢ − j'ᵢ| + 2k`, which is not a power of two (pairs: `k = 2`).
* `Route8PiecewiseRateStatement` (key `9902`): `|R| = Σ_X |X|`, `|∂R| = Σ_X E(X)` with
  `E(X) = |cutEdges X|`, the rate written over the pieces,
  `δ·slack < Σ_X (δ·|X| − (δs+1)·E(X))`, and the heavy pieces
  (`(δs+1)·E(X) < δ·|X|`) are nonempty.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open scoped BigOperators

universe u

/-- **Key `9900`: a piece attached twice to one window.**  For every canonical piece `X` of
`G[R]` (`R` the remainder of `P₀`), every window `P ∈ P₀` with a placement `p`, and two exits
`p i — a`, `b — p i'` of `X` (`a, b ∈ X`, not the same exit):

* every internal path `a ⇝ b` inside `X` of length `ℓ` closes a cycle of length
  `|i−i'| + ℓ + 2`, which is not a power of two;
* every run `[lo, hi]` of internal path lengths (all contained in the length set of `X`
  between `a` and `b`) satisfies `hi + |i−i'| + 2 < 4` or
  `hi + |i−i'| + 3 < 2·(lo + |i−i'| + 2)` (the dyadic run bound). -/
def Route8PieceWindowAttachmentStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ X ∈ object.canonicalPieces remainder, ∀ P ∈ packing,
    ∀ p : Fin data.windowOrder → object.Vertex,
      Graph.LocalRigidity.IsWindowPlacement object P p →
      ∀ (i i' : Fin data.windowOrder) (a b : object.Vertex),
        a ∈ object.pieceSupport remainder X → b ∈ object.pieceSupport remainder X →
        object.graph.Adj (p i) a → object.graph.Adj b (p i') → (i ≠ i' ∨ a ≠ b) →
        (∀ ℓ ∈ pieceLengthSet object (object.pieceSupport remainder X) a b,
            ¬ Core.DyadicLength.PowerOfTwoLength (Nat.dist i.1 i'.1 + ℓ + 2)) ∧
          ∀ lo hi : Nat,
            (∀ ℓ, lo ≤ ℓ → ℓ ≤ hi →
              ℓ ∈ pieceLengthSet object (object.pieceSupport remainder X) a b) →
            hi + Nat.dist i.1 i'.1 + 2 < 4 ∨
              hi + Nat.dist i.1 i'.1 + 3 < 2 * (lo + Nat.dist i.1 i'.1 + 2)

/-- **Key `9901`: chain cycles through pieces and windows.**  For `k = n + 1` pairwise
distinct canonical pieces `X i` and pairwise distinct windows `P i ∈ P₀` with placements
`p i`, exit vertices `a i, b i ∈ X i`, exits `b i — p i (j i)` into window `i`, exits
`p i (j' i) — a (i+1)` out of window `i` into the next piece, and the closing exit
`p k (j' k) — a 0`: for every choice of internal path lengths `ℓ i` of `X i` between `a i`
and `b i`, with total `≥ 3`, the chain cycle has length
`Σ (ℓ i + |j i − j' i|) + 2k`, which is not a power of two. -/
def Route8PieceChainCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  ∀ (n : Nat) (X : Fin (n + 1) → Graph.SupportComponents.Connected.Component object remainder)
    (P : Fin (n + 1) → Finset object.Vertex)
    (p : Fin (n + 1) → Fin data.windowOrder → object.Vertex)
    (j j' : Fin (n + 1) → Fin data.windowOrder) (a b : Fin (n + 1) → object.Vertex)
    (ℓ : Fin (n + 1) → Nat),
    Function.Injective X → Function.Injective P →
    (∀ i, X i ∈ object.canonicalPieces remainder) → (∀ i, P i ∈ packing) →
    (∀ i, Graph.LocalRigidity.IsWindowPlacement object (P i) (p i)) →
    (∀ i, a i ∈ object.pieceSupport remainder (X i)) →
    (∀ i, b i ∈ object.pieceSupport remainder (X i)) →
    (∀ i, object.graph.Adj (b i) (p i (j i))) →
    (∀ i : Fin n, object.graph.Adj (p i.castSucc (j' i.castSucc)) (a i.succ)) →
    object.graph.Adj (p (Fin.last n) (j' (Fin.last n))) (a 0) →
    (∀ i, ℓ i ∈ pieceLengthSet object (object.pieceSupport remainder (X i)) (a i) (b i)) →
    3 ≤ (∑ i, (ℓ i + Nat.dist (j i).1 (j' i).1)) + 2 * (n + 1) →
    ¬ Core.DyadicLength.PowerOfTwoLength
      ((∑ i, (ℓ i + Nat.dist (j i).1 (j' i).1)) + 2 * (n + 1))

/-- **Key `9902`: the rate over the pieces.**  With `R` the remainder of `P₀`, its canonical
pieces `X`, `|X|` their sizes and `E(X) = |cutEdges X|` their exit counts, and
`slack = F·s·T(n)` the rate's allowance:

* `|R| = Σ_X |X|` and `|∂R| = Σ_X E(X)` (the pieces partition `R` and its cut);
* the rate `(δs+1)·|∂R| + δ·slack < δ·|R|` written over the pieces:
  `δ·slack < Σ_X (δ·|X| − (δs+1)·E(X))` (in `ℤ`);
* the heavy pieces, `(δs+1)·E(X) < δ·|X|` (exit ratio `|X|/E(X)` above `(δs+1)/δ`, i.e.
  `13/3` at `δ = 3`, `s = 4`), are nonempty. -/
noncomputable def Route8PiecewiseRateStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let pieces := object.canonicalPieces remainder
  let size := fun X => (object.pieceSupport remainder X).card
  let exits := fun X => (Graph.Route8.cutEdges object (object.pieceSupport remainder X)).card
  let slack := data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount
  remainder.card = ∑ X ∈ pieces, size X ∧
    (Graph.Route8.cutEdges object remainder).card = ∑ X ∈ pieces, exits X ∧
    (data.threshold : ℤ) * slack <
      ∑ X ∈ pieces, ((data.threshold : ℤ) * size X -
        ((data.threshold * data.dischargeScale + 1 : Nat) : ℤ) * exits X) ∧
    (pieces.filter fun X =>
      (data.threshold * data.dischargeScale + 1) * exits X <
        data.threshold * size X).Nonempty

end Hypostructure.Graph.Strategy.Spine
