import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: the cold-branch entry `[145]`--`[149]`

Proof-agnostic contract lemmas for the entry of the cold branch.  Each lemma is
stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every paper hypothesis explicit; its conclusion is exactly the
statement of the fact it proves.  This module imports no strategy, row, or
vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[149]`, `prop:p13-density`'s entropy step on the cold branch.**
On the no-edge of `[22]` the live-hot package fits the labelled skeleton budget,
`2^{rate·scales·|𝒫_hot|} ≤ skeletonBudget` (`BarrierCapStatement`).  Spending that
budget against the near-cubic spine (`SurplusAtOrBelowStatement`, the minimum
degree `δ ≥ 3`, and the handshake) gives the exact finite live-hot entropy cap
`2·rate·scales·|𝒫_hot| ≤ (⌊log₂ n⌋+1)(δn + T(n))`. -/
theorem coldHotEntropyCap_of_barrierCap (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (three : 3 ≤ data.threshold)
    (cap : BarrierCapStatement data object)
    (nearCubic : SurplusAtOrBelowStatement data object) :
    ColdHotEntropyCapStatement data object := by
  have spine : data.threshold * object.vertexCount ≤ 2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
      data.threshold fun vertex =>
        le_trans baseline (object.minDegree_le_degree vertex)
  have bound := Graph.two_mul_exponent_le_scale_mul_edgeBudget object
    (data.windowRate * data.separatedScaleCount object.vertexCount *
      (canonicalHotWindows data object).card)
    data.threshold (data.surplusThreshold object.vertexCount)
    cap spine three nearCubic
  simp only [ColdHotEntropyCapStatement, coldSkeletonAllowance, coldWindowBitRate]
  rw [Nat.mul_assoc]
  exact bound

end Hypostructure.Graph.Contracts.Spine
