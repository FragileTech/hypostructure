import Hypostructure.Graph.Contracts.RouteEight.Basic
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

end Hypostructure.Graph.Contracts.RouteEight
