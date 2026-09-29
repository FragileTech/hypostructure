import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Contracts.RouteEight.RateFailsThin
import Hypostructure.Graph.Statements.Route8RateFailsJoin

/-!
# Contracts: the failed private-carrier rate on the connected pieces of `R`

The canonical pieces of the remainder partition `|R|` and `|∂R|` exactly, so the
failed rate has a connected piece of nonpositive rate charge up to its share of
the slack.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- `Σ_i |∂X_i| = |∂R|`: a vertex of a piece has the same neighbours in the
piece as in the region. -/
theorem sum_boundaryIncidence_canonicalPieces (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    ∑ piece ∈ object.canonicalPieces support,
        object.boundaryIncidence (object.pieceSupport support piece) =
      object.boundaryIncidence support := by
  classical
  have pointwise : ∀ piece ∈ object.canonicalPieces support,
      object.boundaryIncidence (object.pieceSupport support piece) =
        ∑ vertex ∈ object.pieceSupport support piece,
          (object.degree vertex - object.internalDegree support vertex) :=
    fun piece _ => by
      unfold FiniteObject.boundaryIncidence
      exact Finset.sum_congr rfl fun vertex inside => by
        rw [object.internalDegree_pieceSupport support piece inside]
  rw [Finset.sum_congr rfl pointwise]
  exact object.sum_canonicalPieces support
    (fun vertex => object.degree vertex - object.internalDegree support vertex)

/-- **The failed rate on the connected pieces of G's remainder.** -/
theorem route8RateFailsPiece (data : Parameters) (object : FiniteObject.{u})
    (fails : Route8RateFailsStatement data object) :
    Route8RateFailsPieceStatement data object := by
  classical
  set packing := canonicalWindowPacking data object with hpack
  set remainder := object.remainderSupport packing with hrem
  set pieces := object.canonicalPieces remainder with hpieces
  have cardSum := object.sum_pieceSupport_card remainder
  have cutSum := sum_boundaryIncidence_canonicalPieces object remainder
  have failsLe : data.threshold * remainder.card ≤
      (data.threshold * data.dischargeScale + 1) * object.boundaryIncidence remainder +
        data.threshold * (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount) :=
    route8RateFails_oldLe data object fails
  refine ⟨cardSum, cutSum, ?_⟩
  intro nonempty
  obtain ⟨vertex, member⟩ := nonempty
  obtain ⟨piece, present, _⟩ :=
    (SupportComponents.Connected.mem_support_iff_mem_component object remainder
      vertex).mp member
  have piecesNonempty : pieces.Nonempty :=
    ⟨piece, (object.mem_canonicalPieces remainder).mpr present⟩
  by_contra none
  push Not at none
  set m := pieces.card with hm
  have mPos : 0 < m := Finset.card_pos.mpr piecesNonempty
  set S := data.threshold * (data.bridgeMassFactor * data.dischargeScale *
    data.surplusThreshold object.vertexCount) with hS
  rw [← hpieces] at cardSum cutSum
  have strict := Finset.sum_lt_sum_of_nonempty piecesNonempty
    (f := fun piece => m * ((data.threshold * data.dischargeScale + 1) *
        object.boundaryIncidence (object.pieceSupport remainder piece)) + S)
    (g := fun piece => m * (data.threshold *
        (object.pieceSupport remainder piece).card))
    (fun piece present => none piece present)
  have sumA : ∑ piece ∈ pieces, m * ((data.threshold * data.dischargeScale + 1) *
      object.boundaryIncidence (object.pieceSupport remainder piece)) =
      m * ((data.threshold * data.dischargeScale + 1) *
        object.boundaryIncidence remainder) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, cutSum]
  have sumB : ∑ piece ∈ pieces, m * (data.threshold *
      (object.pieceSupport remainder piece).card) =
      m * (data.threshold * remainder.card) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, cardSum]
  have sumC : ∑ piece ∈ pieces, (m * ((data.threshold * data.dischargeScale + 1) *
      object.boundaryIncidence (object.pieceSupport remainder piece)) + S) =
      m * ((data.threshold * data.dischargeScale + 1) *
        object.boundaryIncidence remainder) + m * S := by
    rw [Finset.sum_add_distrib, sumA, Finset.sum_const, smul_eq_mul]
  rw [sumC, sumB] at strict
  have scaled := Nat.mul_le_mul_left m failsLe
  rw [Nat.mul_add] at scaled
  omega

end Hypostructure.Graph.Contracts.RouteEight
