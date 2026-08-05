import Hypostructure.Core.EntropyPackingBudget

/-!
# The finite statements used by the finite-state capacity row

These are the finite, non-asymptotic forms of the rank, curvature-cost,
entropy-cap, and support-accounting steps.  The hypotheses are facts retained
by the predecessor ledger; the theorems only perform the paper's arithmetic.
In particular, no theorem below treats a registration field as a proof of its
own conclusion.
-/

namespace Hypostructure.Core.Strategy.FiniteStateCapacity

open Hypostructure.Core

structure FullRankFact where
  rank : Nat
  coordinateCount : Nat
  coordinateLowerBound : Nat
  rank_eq_coordinateCount : rank = coordinateCount
  coordinateLowerBound_le_count : coordinateLowerBound ≤ coordinateCount

theorem FullRankFact.lower_bound (fact : FullRankFact) :
    fact.coordinateLowerBound ≤ fact.rank := by
  rw [fact.rank_eq_coordinateCount]
  exact fact.coordinateLowerBound_le_count

structure ForcedCurvatureCostFact where
  rank : Nat
  coordinateLowerBound : Nat
  costPerCoordinate : ℝ
  windowDensity : ℝ
  remainderCard : Nat
  error : ℝ
  rank_lower : coordinateLowerBound ≤ rank
  costPerCoordinate_nonneg : 0 ≤ costPerCoordinate
  windowLowerBound : windowDensity * remainderCard ≤ coordinateLowerBound

theorem ForcedCurvatureCostFact.cost_lower_bound
    (fact : ForcedCurvatureCostFact) :
    fact.costPerCoordinate * fact.windowDensity * fact.remainderCard ≤
      fact.costPerCoordinate * fact.rank := by
  have h₁ := mul_le_mul_of_nonneg_left fact.windowLowerBound
    fact.costPerCoordinate_nonneg
  have h₂ : fact.costPerCoordinate * (fact.coordinateLowerBound : ℝ) ≤
      fact.costPerCoordinate * (fact.rank : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast fact.rank_lower)
      fact.costPerCoordinate_nonneg
  calc
    fact.costPerCoordinate * fact.windowDensity * fact.remainderCard
        = fact.costPerCoordinate *
            (fact.windowDensity * (fact.remainderCard : ℝ)) := by ring
    _ ≤ fact.costPerCoordinate * fact.coordinateLowerBound := h₁
    _ ≤ fact.costPerCoordinate * fact.rank := h₂

structure EntropyCapFact where
  remainingBudget : ℝ
  forcedCurvatureDemand : ℝ
  cap : remainingBudget < forcedCurvatureDemand

theorem EntropyCapFact.closes (fact : EntropyCapFact) :
    ¬ fact.forcedCurvatureDemand ≤ fact.remainingBudget :=
  not_le_of_gt fact.cap

structure CanonicalChargeDecomposition where
  componentCount : Nat
  componentDeficiency : Fin componentCount → Int
  componentSurplus : Fin componentCount → Int
  componentCard : Fin componentCount → Int
  totalDeficiency : Int
  totalSurplus : Int
  totalCard : Int
  deficiency_sum : (Finset.univ.sum componentDeficiency) = totalDeficiency
  surplus_sum : (Finset.univ.sum componentSurplus) = totalSurplus
  card_sum : (Finset.univ.sum componentCard) = totalCard

def CanonicalChargeDecomposition.netCharge4
    (decomposition : CanonicalChargeDecomposition)
    (component : Fin decomposition.componentCount) : Int :=
  4 * decomposition.componentDeficiency component -
    4 * decomposition.componentSurplus component -
      decomposition.componentCard component

theorem CanonicalChargeDecomposition.netCharge_sum
    (decomposition : CanonicalChargeDecomposition) :
    (Finset.univ.sum decomposition.netCharge4) =
      4 * decomposition.totalDeficiency - 4 * decomposition.totalSurplus -
        decomposition.totalCard := by
  simp only [netCharge4]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [decomposition.deficiency_sum, decomposition.surplus_sum,
    decomposition.card_sum]

theorem CanonicalChargeDecomposition.exists_negative_of_negative_total
    (decomposition : CanonicalChargeDecomposition)
    (negative : 4 * decomposition.totalDeficiency -
        4 * decomposition.totalSurplus - decomposition.totalCard < 0) :
    ∃ component, decomposition.netCharge4 component < 0 := by
  by_contra no_negative
  push Not at no_negative
  have nonnegative : 0 ≤ Finset.univ.sum decomposition.netCharge4 := by
    exact Finset.sum_nonneg fun component _ => no_negative component
  rw [decomposition.netCharge_sum] at nonnegative
  omega

end Hypostructure.Core.Strategy.FiniteStateCapacity
