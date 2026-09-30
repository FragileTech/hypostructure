import Hypostructure.Graph.Contracts.RouteEight.PackingExchange
import Hypostructure.Graph.Statements.Route8ArmCap

/-!
# Contracts: net-cap excess, clean landings and the arm-closure residual (keys `9804`–`9807`)

* `9804` combines key `222` (`L < |R|` under `SufficientlyLargeForNetCap`) with key `9902`
  (`δ·slack < δ|R| − (δs+1)|∂R|`, the rate summed over the pieces) multiplied by `s`.
* `9805` and `9806` instantiate `PackingExchange.long_pair_rule`,
  `PackingExchange.false_of_clean_triple` and `PackingExchange.long_landing_cap` at `P₀` and
  the canonical pieces of `R` (distinct pieces are disjoint and joined by no edge).
* `9807` combines `9804`, `9806` (summed over `P₀` by double counting,
  `Σ_X ν(X) = Σ_P Λ(P)`) and `Σ_X δ(X) ≤ Σ_{δ(X)>0} δ(X)`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- **Key `9804`**: the net-cap excess `L + s·δ·slack < (δs+1)·(|R| − s·|∂R|)`. -/
theorem route8NetCapExcess (data : Parameters) (object : FiniteObject.{u})
    (cap : NetDeficiencyCapStatement data object)
    (rate : Route8PiecewiseRateStatement data object) :
    Route8NetCapExcessStatement data object := by
  classical
  unfold Route8NetCapExcessStatement
  unfold NetDeficiencyCapStatement at cap
  unfold Route8PiecewiseRateStatement at rate
  dsimp only at cap rate ⊢
  intro large
  have h222 := cap large
  obtain ⟨sizeSum, exitSum, rateSum, _⟩ := rate
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Nat.cast_sum,
    ← Nat.cast_sum, ← sizeSum, ← exitSum] at rateSum
  have h1 : ((data.dischargeScale *
          (data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) +
            data.spineScale * Core.ceilSqrt object.vertexCount) : Nat) : ℤ) <
      ((data.dischargeScale * (2 * (data.windowOrder - 1) *
        (canonicalWindowPacking data object).card) : Nat) : ℤ) +
        ((object.remainderSupport (canonicalWindowPacking data object)).card : ℤ) := by
    exact_mod_cast h222
  have hs : (0 : ℤ) ≤ data.dischargeScale := by positivity
  have key := mul_le_mul_of_nonneg_left rateSum.le hs
  push_cast at h1 key rateSum ⊢
  nlinarith [key, h1]

/-- **Key `9805`**: the pair and triple landing rules on every placed window of `P₀`. -/
theorem route8CleanLandingRules (data : Parameters) (object : FiniteObject.{u}) :
    Route8CleanLandingRulesStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  unfold Route8CleanLandingRulesStatement
  dsimp only
  intro four P hP p hp
  refine ⟨?_, ?_⟩
  · intro X _ Y _ XY i j x y lx ly
    exact PackingExchange.long_pair_rule four spec.1 spec.2.1 hP hp
      (object.pieceSupport_subset _ X) (object.pieceSupport_subset _ Y)
      (SupportComponents.Connected.disjoint_members object _ XY) lx ly
  · intro X _ Y _ Z _ XY XZ YZ e k x y z a b c l m cx cy ha hb hab cz bz ek sz avoid
    exact PackingExchange.false_of_clean_triple (by omega) spec.1 spec.2.1 hP hp
      (object.pieceSupport_subset _ X) (object.pieceSupport_subset _ Y)
      (object.pieceSupport_subset _ Z)
      (SupportComponents.Connected.disjoint_members object _ XY)
      (SupportComponents.Connected.disjoint_members object _ XZ)
      (SupportComponents.Connected.disjoint_members object _ YZ)
      (PackingExchange.pieceSupport_not_adj object _ XY) cx cy ha hb hab cz l m bz ek sz avoid

/-- **Key `9806`**: the clean-landing cap, per placed window and summed over `P₀`. -/
theorem route8CleanLandingCap (data : Parameters) (object : FiniteObject.{u}) :
    Route8CleanLandingCapStatement data object := by
  classical
  have spec := canonicalWindowPacking_spec data object
  unfold Route8CleanLandingCapStatement
  dsimp only
  intro four
  have perWindow : ∀ P ∈ canonicalWindowPacking data object,
      ∀ p : Fin data.windowOrder → object.Vertex,
      LocalRigidity.IsWindowPlacement object P p →
      route8LongLandingCount data object p ≤
        (data.threshold - 1) + object.ambientSurplus P data.threshold := by
    intro P hP p hp
    unfold route8LongLandingCount
    dsimp only
    exact PackingExchange.long_landing_cap four spec.1 spec.2.1 hP hp data.threshold _
      (object.pieceSupport _)
      (fun X _ => object.pieceSupport_subset _ X)
      (fun X _ Y _ ne => SupportComponents.Connected.disjoint_members object _ ne)
      (fun X _ Y _ ne => PackingExchange.pieceSupport_not_adj object _ ne)
  refine ⟨perWindow, fun place hplace => ?_⟩
  calc ∑ P ∈ canonicalWindowPacking data object, route8LongLandingCount data object (place P)
      ≤ ∑ P ∈ canonicalWindowPacking data object,
          ((data.threshold - 1) + object.ambientSurplus P data.threshold) :=
        Finset.sum_le_sum fun P hP => perWindow P hP _ (hplace P hP)
    _ = (data.threshold - 1) * (canonicalWindowPacking data object).card +
          object.ambientSurplus (FiniteObject.windowSupport (canonicalWindowPacking data object))
            data.threshold := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
          PackingExchange.sum_ambientSurplus_packing spec.1]

/-- The arithmetic of key `9807`: from `lhs < a·Σ e` and `Σ ν ≤ bound` (with `a, c ≥ 0`),
`lhs − c·bound < Σ_{e > 0} (a·e − c·ν)`. -/
theorem arm_closure_arith {ι : Type*} (s : Finset ι) (e : ι → ℤ) (ν : ι → Nat)
    (a c lhs bound total : ℤ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hD : ∑ x ∈ s, e x = total) (hex : lhs < a * total)
    (hν : ∑ x ∈ s, (ν x : ℤ) ≤ bound) :
    lhs - c * bound < ∑ x ∈ s.filter (fun x => 0 < e x), (a * e x - c * ν x) := by
  classical
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have split := Finset.sum_filter_add_sum_filter_not s (fun x => 0 < e x) e
  have neg : ∑ x ∈ s.filter (fun x => ¬ 0 < e x), e x ≤ 0 :=
    Finset.sum_nonpos fun x hx => not_lt.1 (Finset.mem_filter.1 hx).2
  have pos : total ≤ ∑ x ∈ s.filter (fun x => 0 < e x), e x := by linarith
  have νsub : ∑ x ∈ s.filter (fun x => 0 < e x), (ν x : ℤ) ≤ ∑ x ∈ s, (ν x : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have m1 := mul_le_mul_of_nonneg_left pos ha
  have m2 := mul_le_mul_of_nonneg_left (νsub.trans hν) hc
  linarith

/-- **Key `9807`**: the arm-closure residual, from `9804`, `9806` and `9902`. -/
theorem route8ArmClosureResidual (data : Parameters) (object : FiniteObject.{u})
    (excessFact : Route8NetCapExcessStatement data object)
    (capFact : Route8CleanLandingCapStatement data object)
    (rate : Route8PiecewiseRateStatement data object) :
    Route8ArmClosureResidualStatement data object := by
  classical
  unfold Route8ArmClosureResidualStatement
  unfold Route8NetCapExcessStatement at excessFact
  unfold Route8CleanLandingCapStatement at capFact
  unfold Route8PiecewiseRateStatement at rate
  dsimp only at excessFact capFact rate ⊢
  intro four large place hplace c
  obtain ⟨sizeSum, exitSum, _, _⟩ := rate
  have capSum := (capFact four).2 place hplace
  refine arm_closure_arith _ _ (route8LongLandingWindows data object place) _ c _ _ _
    (by positivity) (by positivity) ?_ (excessFact large) ?_
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, ← sizeSum,
      ← exitSum]
  · have dc : ∑ X ∈ object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object)),
          route8LongLandingWindows data object place X =
        ∑ P ∈ canonicalWindowPacking data object, route8LongLandingCount data object (place P) := by
      unfold route8LongLandingWindows route8LongLandingCount
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [← Nat.cast_sum, dc]
    exact_mod_cast capSum

end Hypostructure.Graph.Contracts.RouteEight
