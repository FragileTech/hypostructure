import Hypostructure.Graph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite labelled-edge budgets

The framework count for a finite family of labelled simple-graph edge strata.
All quantities are explicit natural-number counts; a caller supplies only the
set of admissible edge counts.
-/

namespace Hypostructure.Graph

/-- The number of labelled simple graphs on a fixed `vertexCount`-element
vertex set with exactly `edgeCount` edges. -/
def edgeStratumCount (vertexCount edgeCount : Nat) : Nat :=
  (vertexCount.choose 2).choose edgeCount

/-- The elementary union bound for a finite family of exact edge strata. -/
def variableEdgeBudget (vertexCount : Nat) (edgeCounts : Finset Nat) : Nat :=
  edgeCounts.card * edgeCounts.sup (edgeStratumCount vertexCount)

/-- Summing the disjoint exact-edge strata is bounded by the number of allowed
edge counts times the largest stratum.  This is the finite combinatorial
content of the variable-edge budget; no asymptotic approximation is used. -/
theorem sum_edgeStratumCount_le_variableEdgeBudget
    (vertexCount : Nat) (edgeCounts : Finset Nat) :
    ∑ edgeCount ∈ edgeCounts, edgeStratumCount vertexCount edgeCount ≤
      variableEdgeBudget vertexCount edgeCounts := by
  simpa [variableEdgeBudget, nsmul_eq_mul] using
    (edgeCounts.sum_le_card_nsmul (edgeStratumCount vertexCount)
      (edgeCounts.sup (edgeStratumCount vertexCount)) fun edgeCount member =>
        Finset.le_sup member)

noncomputable def edgeFamilyEntropy
    (vertexCount : Nat) (edgeCounts : Finset Nat) : ℝ :=
  Real.logb 2 (∑ edgeCount ∈ edgeCounts,
    edgeStratumCount vertexCount edgeCount : Nat)

noncomputable def largestStratumEntropy
    (vertexCount : Nat) (edgeCounts : Finset Nat) : ℝ :=
  Real.logb 2 ((edgeCounts.sup (edgeStratumCount vertexCount) : Nat) : ℝ)

theorem edgeFamilyEntropy_le_card_add_largest
    (vertexCount : Nat) (edgeCounts : Finset Nat)
    (familyPositive : 0 < ∑ edgeCount ∈ edgeCounts,
      edgeStratumCount vertexCount edgeCount)
    (cardPositive : 0 < edgeCounts.card)
    (largestPositive : 0 < edgeCounts.sup (edgeStratumCount vertexCount)) :
    edgeFamilyEntropy vertexCount edgeCounts ≤
      Real.logb 2 edgeCounts.card +
        largestStratumEntropy vertexCount edgeCounts := by
  have countBound := sum_edgeStratumCount_le_variableEdgeBudget
    vertexCount edgeCounts
  have castBound :
      ((∑ edgeCount ∈ edgeCounts,
        edgeStratumCount vertexCount edgeCount : Nat) : ℝ) ≤
      (edgeCounts.card : ℝ) *
        ((edgeCounts.sup (edgeStratumCount vertexCount) : Nat) : ℝ) := by
    exact_mod_cast countBound
  rw [edgeFamilyEntropy, largestStratumEntropy]
  calc
    Real.logb 2 (∑ edgeCount ∈ edgeCounts,
        edgeStratumCount vertexCount edgeCount : Nat)
        ≤ Real.logb 2
          ((edgeCounts.card : ℝ) *
            ((edgeCounts.sup (edgeStratumCount vertexCount) : Nat) : ℝ)) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num)
        (by exact_mod_cast familyPositive) castBound
    _ = Real.logb 2 edgeCounts.card +
          Real.logb 2 ((edgeCounts.sup (edgeStratumCount vertexCount) : Nat) : ℝ) := by
      rw [Real.logb_mul]
      · exact_mod_cast (Nat.ne_of_gt cardPositive)
      · exact_mod_cast (Nat.ne_of_gt largestPositive)

theorem edgeCountFamily_log_loss_le_two_log
    (vertexCount : Nat) (edgeCounts : Finset Nat)
    (cardPositive : 0 < edgeCounts.card)
    (cardBound : edgeCounts.card ≤ vertexCount ^ 2) :
    Real.logb 2 edgeCounts.card ≤ 2 * Real.logb 2 vertexCount := by
  calc
    Real.logb 2 edgeCounts.card ≤ Real.logb 2 (vertexCount ^ 2) := by
      apply Real.logb_le_logb_of_le (b := 2) (by norm_num)
      · exact_mod_cast cardPositive
      · exact_mod_cast cardBound
    _ = 2 * Real.logb 2 vertexCount := by
      simpa using Real.logb_pow 2 (vertexCount : ℝ) 2

end Hypostructure.Graph
