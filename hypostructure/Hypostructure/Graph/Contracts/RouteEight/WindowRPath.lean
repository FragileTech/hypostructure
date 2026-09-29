import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Contracts.RouteEight.RateFailsPiece
import Hypostructure.Graph.Statements.Route8WindowRPath

/-!
# Contracts: cycles through two windows via the remainder, and the stubs to hubs
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- **Cycles through two windows via `R` avoid every power of two.** -/
theorem route8WindowRPathGap (data : Parameters) (object : FiniteObject.{u})
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    Route8WindowRPathGapStatement data object := by
  classical
  intro P hP Q hQ ne p q hpP hqQ i i' j j' a₁ b₁ a₂ b₂ r₁ r₂ r₁p r₂p r₁S r₂S r₁₂
    e₁ e₁' e₂ e₂' forbidden
  have valid := (canonicalWindowPacking_spec data object).1
  have inR : ∀ v, v ∈ object.remainderSupport (canonicalWindowPacking data object) →
      ∀ window ∈ canonicalWindowPacking data object, v ∉ window := by
    intro v hv window hwindow hvw
    have inW := FiniteObject.mem_windowSupport hwindow hvw
    unfold FiniteObject.remainderSupport at hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    exact hv inW
  have disj : ∀ a b, p a ≠ q b := by
    intro a b eq
    have inP := hpP.2.1 a
    have inQ := hqQ.2.1 b
    rw [eq] at inP
    exact Finset.disjoint_left.mp (valid.2 P hP Q hQ ne) inP inQ
  obtain ⟨v, c, cc, cl⟩ := Graph.LocalRigidity.cross_cycle_paths
    (S := {w | w ∈ object.remainderSupport (canonicalWindowPacking data object)})
    hpP.isPlacedPath hqQ.isPlacedPath disj
    (fun a hS => inR _ hS P hP (hpP.2.1 a))
    (fun b hS => inR _ hS Q hQ (hqQ.2.1 b))
    r₁ r₂ r₁p r₂p r₁S r₂S r₁₂ e₁ e₁' e₂ e₂'
  obtain ⟨k, hk, e⟩ := (Core.DyadicLength.powerOfTwoLength_iff _).mp forbidden
  exact CycleCounting.no_dyadic_cycle avoid lengthLaw c cc k hk (cl.trans e)

/-- **The stubs to hubs.** -/
theorem route8HubStubs (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree) :
    Route8HubStubsStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  let H : Finset object.Vertex := Finset.univ.filter fun h => data.threshold < object.degree h
  let W := object.windowSupport (canonicalWindowPacking data object)
  change ∑ v ∈ W, (H.filter fun h => object.graph.Adj v h).card ≤ _
  have double := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := W) (t := H) (fun v h => object.graph.Adj v h)
  have below : ∀ h ∈ H, (Finset.bipartiteBelow (fun v h => object.graph.Adj v h) W h).card ≤
      object.degree h := by
    intro h _
    unfold FiniteObject.degree
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_le_card ?_
    intro v hv
    simp only [Finset.bipartiteBelow, Finset.mem_filter] at hv
    simpa using hv.2.symm
  have hubDegree : ∀ h ∈ H, object.degree h ≤ (data.threshold + 1) * (object.degree h - data.threshold) := by
    intro h hh
    have gt : data.threshold < object.degree h := (Finset.mem_filter.mp hh).2
    obtain ⟨t, ht⟩ : ∃ t, object.degree h = data.threshold + 1 + t := ⟨object.degree h - data.threshold - 1, by omega⟩
    rw [ht]
    have : data.threshold + 1 + t - data.threshold = t + 1 := by omega
    rw [this]
    nlinarith
  calc ∑ v ∈ W, (H.filter fun h => object.graph.Adj v h).card
      = ∑ h ∈ H, (Finset.bipartiteBelow (fun v h => object.graph.Adj v h) W h).card := double
    _ ≤ ∑ h ∈ H, object.degree h := Finset.sum_le_sum below
    _ ≤ ∑ h ∈ H, (data.threshold + 1) * (object.degree h - data.threshold) :=
        Finset.sum_le_sum hubDegree
    _ = (data.threshold + 1) * object.ambientSurplus H data.threshold := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ (data.threshold + 1) * object.degreeSurplus data.threshold :=
        Nat.mul_le_mul_left _ (object.ambientSurplus_le_degreeSurplus H data.threshold baselineAll)

/-- **Cycles through one window via `R` avoid every power of two.** -/
theorem route8WindowSelfRPathGap (data : Parameters) (object : FiniteObject.{u})
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    Route8WindowSelfRPathGapStatement data object := by
  classical
  intro P hP p hpP i i' a b r rp rS e₁ e₂ ne forbidden
  have inR : ∀ v, v ∈ object.remainderSupport (canonicalWindowPacking data object) →
      ∀ window ∈ canonicalWindowPacking data object, v ∉ window := by
    intro v hv window hwindow hvw
    have inW := FiniteObject.mem_windowSupport hwindow hvw
    unfold FiniteObject.remainderSupport at hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    exact hv inW
  obtain ⟨v, c, cc, cl⟩ := Graph.LocalRigidity.self_cycle_path
    (S := {w | w ∈ object.remainderSupport (canonicalWindowPacking data object)})
    hpP.isPlacedPath (fun x hS => inR _ hS P hP (hpP.2.1 x)) r rp rS e₁ e₂ ne
  obtain ⟨k, hk, e⟩ := (Core.DyadicLength.powerOfTwoLength_iff _).mp forbidden
  exact CycleCounting.no_dyadic_cycle avoid lengthLaw c cc k hk (cl.trans e)

/-- **The pieces of the remainder against the bridgeless cut.** -/
theorem route8PieceBoundary (data : Parameters) (object : FiniteObject.{u})
    (density : DensityExcessStatement object) :
    Route8PieceBoundaryStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro nonempty
  obtain ⟨P, hP⟩ := nonempty
  have valid := (canonicalWindowPacking_spec data object).1
  have windowNonempty : P.Nonempty := by
    have card := (valid.1 P hP).2
    have pos := data.windowOrder_pos
    exact Finset.card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := windowNonempty
  have each : ∀ piece ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
      2 ≤ object.boundaryIncidence (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece) := by
    intro piece present
    have pieceNonempty := SupportComponents.Connected.member_nonempty object
      (object.remainderSupport (canonicalWindowPacking data object))
      ((object.mem_canonicalPieces _).mp present)
    have proper : object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece ≠ Finset.univ := by
      intro eq
      have wIn : w ∈ object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) piece := by
        rw [eq]; exact Finset.mem_univ w
      have := object.pieceSupport_subset _ piece wIn
      unfold FiniteObject.remainderSupport at this
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
      exact this (FiniteObject.mem_windowSupport hP hw)
    have cut := density.2.2.1 _ pieceNonempty proper
    have conv : ∀ u, ((object.graph.neighborFinset u) \ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece).card =
        object.degree u - object.internalDegree (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) piece) u := by
      intro u
      have h := Finset.card_sdiff_add_card_inter (object.graph.neighborFinset u)
        (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object))
          piece)
      have hd : (object.graph.neighborFinset u).card = object.degree u :=
        SimpleGraph.card_neighborFinset_eq_degree object.graph u
      have hi : (object.graph.neighborFinset u ∩ object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) piece).card =
          object.internalDegree (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) piece) u := rfl
      omega
    unfold FiniteObject.boundaryIncidence
    simp only [← conv]
    exact cut
  refine ⟨each, ?_⟩
  have cutSum := sum_boundaryIncidence_canonicalPieces object
    (object.remainderSupport (canonicalWindowPacking data object))
  rw [← cutSum]
  calc 2 * (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))).card
      = ∑ _piece ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)), 2 := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum each

end Hypostructure.Graph.Contracts.RouteEight
