import Hypostructure.Graph.Contracts.RouteEight.WindowRPath
import Hypostructure.Graph.Contracts.RouteEight.RateFailsFlow
import Hypostructure.Graph.Statements.Route8WindowPieceLengths

/-!
# Contracts: the rank of the window-piece multigraph and the achievable cycle lengths
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- **The cycle rank of the window-piece multigraph.** -/
theorem route8WindowPieceRank (data : Parameters) (object : FiniteObject.{u})
    (threeLe : 3 ≤ data.threshold)
    (join : Route8RateFailsJoinStatement data object)
    (boundary : Route8PieceBoundaryStatement data object) :
    Route8WindowPieceRankStatement data object := by
  intro nonempty
  have two := (boundary nonempty).2
  have joinEq := join.1
  have prod : coldExternalStubCount data * (canonicalWindowPacking data object).card =
      data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) -
        2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card := by
    simp only [coldExternalStubCount]
    rw [Nat.sub_mul, Nat.mul_assoc]
  have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
    have := Nat.mul_le_mul_right data.windowOrder threeLe
    omega
  have debit' : 2 * (data.windowOrder - 1) * (canonicalWindowPacking data object).card ≤
      data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) := by
    have := Nat.mul_le_mul_right (canonicalWindowPacking data object).card debit
    rw [Nat.mul_assoc data.threshold] at this
    exact this
  change _ + (2 * (data.windowOrder - 1) * _ + _) = _ at joinEq
  rw [prod]
  omega

/-- **The achievable lengths of the pieces and the cycles of `B`.** -/
theorem route8AchievableLengths (data : Parameters) (object : FiniteObject.{u})
    (gap : Route8WindowRPathGapStatement data object)
    (selfGap : Route8WindowSelfRPathGapStatement data object) :
    Route8AchievableLengthsStatement data object := by
  classical
  unfold Route8AchievableLengthsStatement
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro piece present a ha b hb
    have connected := SupportComponents.Connected.connectedOn_of_mem_order object _
      ((object.mem_canonicalPieces _).mp present)
    obtain ⟨r, rp, rS⟩ := connected.2 ha hb
    refine ⟨⟨r.length, r, rp, rS, rfl⟩, ?_⟩
    rintro length ⟨r', rp', rS', rfl⟩
    have sub : r'.support.toFinset ⊆ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece := by
      intro v hv; exact rS' v (List.mem_toFinset.mp hv)
    have card := Finset.card_le_card sub
    rw [List.toFinset_card_of_nodup rp'.support_nodup, SimpleGraph.Walk.length_support] at card
    omega
  · intro P hP Q hQ ne p q hp hq X hX Y hY XY i i' j j' a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂
      e₁ e₁' e₂ e₂' ℓ₁ hℓ₁ ℓ₂ hℓ₂
    obtain ⟨r₁, r₁p, r₁S, rfl⟩ := hℓ₁
    obtain ⟨r₂, r₂p, r₂S, rfl⟩ := hℓ₂
    have disjoint := SupportComponents.Connected.disjoint_members object
      (object.remainderSupport (canonicalWindowPacking data object)) XY
    exact gap P hP Q hQ ne p q hp hq i i' j j' a₁ b₁ a₂ b₂ r₁ r₂ r₁p r₂p
      (fun v hv => object.pieceSupport_subset _ X (r₁S v hv))
      (fun v hv => object.pieceSupport_subset _ Y (r₂S v hv))
      (fun v hv hv' => Finset.disjoint_left.mp disjoint (r₁S v hv) (r₂S v hv'))
      e₁ e₁' e₂ e₂'
  · intro P hP p hp X hX i i' a b ha hb e₁ e₂ ne ℓ hℓ
    obtain ⟨r, rp, rS, rfl⟩ := hℓ
    exact selfGap P hP p hp i i' a b r rp
      (fun v hv => object.pieceSupport_subset _ X (rS v hv)) e₁ e₂ ne

end Hypostructure.Graph.Contracts.RouteEight
