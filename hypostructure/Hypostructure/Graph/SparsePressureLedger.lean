import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.SparseEntropySandwich

/-!
# From the entropy sandwich to the object's certified capacity ledger and the
square-root surplus estimate

Nodes `[131]`, `[137]` and `[138]` of the sparse surplus branch, at the level of
the finite arithmetic the rows commit.

* `prop:sparse-entropy-sandwich-with-blockers`, in the log-cleared form
  `entropySandwich` already proves, followed by `log₂`: from
  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)` and `C(N,m₀) ≤ 2^{|ℐ_spine| + E}` one gets
  `|Π_free| ≤ E + (m − m₀)(⌊log₂ n⌋ + 1)` (`freeCount_le_of_sandwich`); with
  `lem:incremental-skeleton-room`'s `2(m − m₀) ≤ σ + 2` that is the manuscript's
  `E_spine(n) + (½σ(G) + 1) log₂ n`.
* `def:capacity-token-ledger` at a declared presentation, certified with the
  node-`[129]` deficit and that budget (`certifiedLedger_of_sandwich`), which is
  what `[137]`'s second production and `[138]`'s estimate consume.
* `cor:spine-lower-bound-surplus-estimates` / `[138]`: at the full pair schedule
  (`prop:sparse-entropy-sandwich`), `C(σ,2)` is bounded by the same budget, so
  `σ(G) ≤ C_sp ⌈√n⌉` by the generic quadratic absorption
  (`surplus_le_scale_of_pairSandwich`); and at a capped capacity ledger
  (`prop:single-graph-sparse-pressure-routing` (a)) the same estimate follows
  from `R_L(n)` (`surplus_le_scale_of_capped`).

Nothing here decides whether the entropy count holds: that is the node's own
decision on its residual.  These are the consequences it commits once it does.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- `n^k ≤ 2^{k(⌊log₂ n⌋+1)}`. -/
theorem pow_le_two_pow_mul_log2_succ (n k : Nat) :
    n ^ k ≤ 2 ^ (k * (Nat.log2 n + 1)) := by
  rw [Nat.pow_mul']
  exact Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_log2_self) k

/-- **`prop:sparse-entropy-sandwich-with-blockers`, after `log₂`.**  From the
entropy count on the mixed family and the baseline demand,
`|Π_free| ≤ E + (m − m₀)(⌊log₂ n⌋ + 1)`. -/
theorem freeCount_le_of_sandwich (object : FiniteObject.{u})
    {baselineDegree spineCount freeCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + freeCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    freeCount ≤ deficit +
      (object.edgeCount - cubicBaselineEdgeCount object.vertexCount baselineDegree) *
        (Nat.log2 object.vertexCount + 1) := by
  have sandwich := entropySandwich object baseline above entropy demand
  set slack := object.edgeCount - cubicBaselineEdgeCount object.vertexCount baselineDegree
  have bound : 2 ^ freeCount ≤ 2 ^ (deficit + slack * (Nat.log2 object.vertexCount + 1)) := by
    calc 2 ^ freeCount ≤ 2 ^ deficit * object.vertexCount ^ slack := sandwich
      _ ≤ 2 ^ deficit * 2 ^ (slack * (Nat.log2 object.vertexCount + 1)) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow_mul_log2_succ _ _)
      _ = 2 ^ (deficit + slack * (Nat.log2 object.vertexCount + 1)) := by rw [pow_add]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 bound

/-- **The object's certified capacity ledger at a declared presentation, from
the sandwich.**  `def:capacity-token-ledger` with `lem:capacity-token-supply`,
node `[130]`'s pair count, `𝔗_cap ≠ ∅`, and the entropy budget
`E + (m − m₀)(⌊log₂ n⌋+1)` of `prop:sparse-entropy-sandwich-with-blockers`. -/
noncomputable def certifiedLedger_of_sandwich {object : FiniteObject.{u}}
    {threshold order deficitScale : Nat}
    (data : CapacityPresentation object threshold order)
    (baseline : 2 ≤ threshold)
    (above : cubicBaselineEdgeCount object.vertexCount threshold ≤ object.edgeCount)
    (spineCount deficit : Nat)
    (demand : cubicBaselineBudget object.vertexCount threshold ≤
      2 ^ (spineCount + deficit))
    (deficit_le : deficit ≤ deficitScale * object.vertexCount)
    (slack_le : object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold ≤
      object.degreeSurplus threshold)
    (entropy : 2 ^ (spineCount +
      (freeSide object.vertexPairDecidableEq (object.portPairSchedule threshold)
        data.tokenOrder data.Eligible data.eligibleDecidable).card) ≤ skeletonBudget object)
    (scheduleCard : (object.portPairSchedule threshold).card =
      (object.degreeSurplus threshold).choose 2)
    (orderNonempty : data.tokens.Nonempty)
    (supply : data.tokens.card ≤
      object.capacityTokenSupply threshold + object.degreeSurplus threshold) :
    CertifiedObjectCapacityLedger object threshold order deficitScale data where
  ledger := ObjectCapacityLedger.ofCapacityCharge data scheduleCard orderNonempty
    (deficit + (object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold) *
      (Nat.log2 object.vertexCount + 1))
    (freeCount_le_of_sandwich object baseline above entropy demand) supply
  spineDeficit := deficit
  edgeSlack := object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold
  entropyBudget_eq := by
    simp only [ObjectCapacityLedger.ofCapacityCharge]
    ring
  spineDeficit_le := deficit_le
  edgeSlack_le := slack_le

/-- **`[138]` from `prop:single-graph-sparse-pressure-routing` (a).**  When every
capacity ledger of the object respects the geometric cap, the certified ledger
at any presentation gives `σ(G) ≤ C_sp ⌈√n⌉` by the generic quadratic
absorption, with `C_sp` derived from the routing alphabet, the baseline degree
and the deficit scale exactly as the presentation registers it. -/
theorem surplus_le_scale_of_capped {object : FiniteObject.{u}}
    {threshold order deficitScale : Nat}
    (data : CapacityPresentation object threshold order)
    (certified : CertifiedObjectCapacityLedger object threshold order deficitScale data)
    (routingLabelBound : Nat)
    (capped : SparsePressureCappedAt certified routingLabelBound)
    (sizePos : 0 < object.vertexCount)
    (safety : TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * homogeneousTokenCap routingLabelBound) +
        (2 * deficitScale + 2 * homogeneousTokenCap routingLabelBound *
          (3 * (threshold - 1) + 2))) :
    object.degreeSurplus threshold ≤
      (2 * (1 + 2 * homogeneousTokenCap routingLabelBound) +
        (2 * deficitScale + 2 * homogeneousTokenCap routingLabelBound *
          (3 * (threshold - 1) + 2))) * Core.ceilSqrt object.vertexCount := by
  exact certified.degreeSurplus_le_mul_ceilSqrt sizePos
    (homogeneousTokenCap routingLabelBound) safety capped

/-- **`[138]` at the full pair schedule** (`prop:sparse-entropy-sandwich`,
`cor:spine-lower-bound-surplus-estimates`): if the free-pair code
`2^{|ℐ_spine| + C(σ,2)}` is realized within the skeleton budget, then
`σ(G) ≤ C_sp ⌈√n⌉`. -/
theorem surplus_le_scale_of_pairSandwich (object : FiniteObject.{u})
    {threshold deficitScale : Nat} (cap : Nat)
    (baseline : 2 ≤ threshold)
    (above : cubicBaselineEdgeCount object.vertexCount threshold ≤ object.edgeCount)
    (spineCount deficit : Nat)
    (demand : cubicBaselineBudget object.vertexCount threshold ≤
      2 ^ (spineCount + deficit))
    (deficit_le : deficit ≤ deficitScale * object.vertexCount)
    (slack_le : object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold ≤
      object.degreeSurplus threshold)
    (entropy : 2 ^ (spineCount + (object.degreeSurplus threshold).choose 2) ≤
      skeletonBudget object)
    (sizePos : 0 < object.vertexCount)
    (safety : TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * cap) + (2 * deficitScale + 2 * cap * (3 * (threshold - 1) + 2))) :
    object.degreeSurplus threshold ≤
      (2 * (1 + 2 * cap) + (2 * deficitScale + 2 * cap * (3 * (threshold - 1) + 2))) *
        Core.ceilSqrt object.vertexCount := by
  set slack := object.edgeCount - cubicBaselineEdgeCount object.vertexCount threshold
  have package := freeCount_le_of_sandwich object baseline above entropy demand
  have root := TokenLoad.demand_le_of_package (object.degreeSurplus threshold)
    (deficit + slack * (Nat.log2 object.vertexCount + 1)) package
  apply TokenLoad.demand_le_mul_ceilSqrt object.vertexCount (object.degreeSurplus threshold)
    deficit slack cap deficitScale (3 * (threshold - 1) + 2) _ sizePos deficit_le slack_le
    _ le_rfl safety
  calc object.degreeSurplus threshold
      ≤ 1 + Nat.sqrt (2 * (deficit + slack * (Nat.log2 object.vertexCount + 1))) := root
    _ ≤ 1 + 2 * cap +
        Nat.sqrt (2 * (deficit + (Nat.log2 object.vertexCount + 1) * slack) +
          2 * (cap * ((3 * (threshold - 1) + 2) * object.vertexCount))) := by
        have inner : 2 * (deficit + slack * (Nat.log2 object.vertexCount + 1)) ≤
            2 * (deficit + (Nat.log2 object.vertexCount + 1) * slack) +
              2 * (cap * ((3 * (threshold - 1) + 2) * object.vertexCount)) := by
          rw [Nat.mul_comm slack]
          omega
        have := Nat.sqrt_le_sqrt inner
        omega

end Hypostructure.Graph
