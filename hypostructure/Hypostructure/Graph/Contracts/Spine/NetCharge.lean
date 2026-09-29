import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: the net-deficiency cap and the net charge, `[56]`--`[61]`, `[173]`--`[174]`

Proof-agnostic contract lemmas for the large-budget net-deficiency cap of
`prop:negative-net-charge` (density, dense and route-8 arms),
`lem:exact-collision-test`, `lem:netcharge-superadd`, the net-charge sign test
and `lem:bridgeless`.  Each lemma is stated over a `Graph.FiniteObject` with the
registered `Parameters` as a parameter and every paper hypothesis explicit; its
conclusion is exactly the statement of the fact it proves.  This module imports
no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Node `[56]`, density-cap arm.**  `def⁺(R) − σ(R) ≤ (1/4 − ε)|R|` for all
sufficiently large `n`, in exact cleared finite form: the density cap, the
registered dyadic scale count, `δ ≥ 3` and the strict window-rate slack give
the strict scaled inequality at every maximal packing. -/
theorem netDeficiencyCap_of_densityCap (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (scaleCount : ∀ size : Nat, data.separatedScaleCount size = Nat.log2 size)
    (three : 3 ≤ data.threshold)
    (rateSlack :
      Graph.FiniteObject.netCapWindowCost data.threshold data.dischargeScale
          data.windowOrder * data.threshold <
        2 * data.windowRate)
    (densityCap : DensityCapStatement data object) :
    NetDeficiencyCapStatement data object := by
  intro large
  set packing := canonicalWindowPacking data object with packingDef
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have cardinality : packing.card = object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  have density :
      2 * (data.windowRate *
        data.separatedScaleCount object.vertexCount *
        object.windowPackingNumber data.windowOrder) ≤
      (Graph.dyadicScaleCount object + 1) *
        (data.threshold * object.vertexCount +
          data.surplusThreshold object.vertexCount) +
      data.densitySlack * (data.windowRate *
        data.separatedScaleCount object.vertexCount) *
        data.surplusThreshold object.vertexCount :=
    densityCap
  have density' :
      2 * (data.windowRate * Nat.log2 object.vertexCount *
        packing.card) ≤
      (Nat.log2 object.vertexCount + 1) *
        (data.threshold * object.vertexCount +
          data.spineScale *
            Core.ceilSqrt object.vertexCount) +
      data.densitySlack * (data.windowRate * Nat.log2 object.vertexCount) *
        (data.spineScale *
          Core.ceilSqrt object.vertexCount) := by
    rw [scaleCount, Graph.dyadicScaleCount,
      ← cardinality] at density
    simpa [Parameters.surplusThreshold] using density
  have cardinality' :
      data.windowOrder * packing.card +
          (object.remainderSupport packing).card =
        object.vertexCount := by
    simpa [Nat.add_comm] using
      object.remainderSupport_card_add_eq valid
  have thresholdPos : 0 < data.threshold :=
    lt_of_lt_of_le (by omega) three
  have debitLe :
      2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
    calc
      2 * (data.windowOrder - 1) ≤ 2 * data.windowOrder := by omega
      _ ≤ data.threshold * data.windowOrder :=
        Nat.mul_le_mul_right data.windowOrder
          (le_trans (by omega) three)
  exact Graph.FiniteObject.strictCap_of_densityCap_of_sufficientlyLarge
    data.threshold data.dischargeScale data.windowOrder data.windowRate
    data.spineScale data.densitySlack object.vertexCount packing.card
    (object.remainderSupport packing).card
    data.windowOrder_pos thresholdPos debitLe rateSlack
    large density' cardinality'

/-- **Node `[56]`, dense arm.**  The strict comparison `τ(θ) < 1/4` at the fixed
maximal packing is the same conditional cap at every maximal packing: all have
the same size and the same remainder count `n − order·p`. -/
theorem netDeficiencyCap_of_denseDeficiencyBelow (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (below : DenseDeficiencyBelowStatement data object) :
    NetDeficiencyCapStatement data object := by
  intro _large
  set packing := canonicalWindowPacking data object with packingDef
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have cardinality : packing.card = object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  have canonicalCard :
      (canonicalWindowPacking data object).card =
        object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  change data.dischargeScale *
      (data.threshold * (data.windowOrder *
        (canonicalWindowPacking data object).card) +
        data.spineScale * Core.ceilSqrt object.vertexCount) <
    data.dischargeScale *
        (2 * (data.windowOrder - 1) *
          (canonicalWindowPacking data object).card) +
      (object.vertexCount - data.windowOrder *
        (canonicalWindowPacking data object).card) at below
  rw [canonicalCard, ← cardinality] at below
  have cardinality' :
      data.windowOrder * packing.card +
          (object.remainderSupport packing).card =
        object.vertexCount := by
    simpa [Nat.add_comm] using
      object.remainderSupport_card_add_eq valid
  have remainder :
      object.vertexCount - data.windowOrder * packing.card =
        (object.remainderSupport packing).card := by
    omega
  rw [remainder] at below
  exact below

/-- **Node `[56]`, route-8 arm.**  At the cubic baseline the route-8 carrier
inequality `(δs+1)·(stubs·p + T(n)) + δ·F·s·T(n) < δ·(n − order·p)` implies
the cap `s·(δ·order·p + T(n)) < s·2(order−1)·p + |R|` outright. -/
theorem netDeficiencyCap_of_coldRoute8Below (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (cubic : data.threshold = 3)
    (below : ColdRoute8BelowStatement data object) :
    NetDeficiencyCapStatement data object := by
  intro _large
  set packing := canonicalWindowPacking data object with packingDef
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have cardinality : packing.card = object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  have canonicalCard :
      (canonicalWindowPacking data object).card =
        object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  change (data.threshold * data.dischargeScale + 1) *
      (coldExternalStubCount data *
        (canonicalWindowPacking data object).card +
        data.surplusThreshold object.vertexCount) +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.vertexCount -
      data.windowOrder * (canonicalWindowPacking data object).card)
    at below
  rw [canonicalCard, ← cardinality] at below
  have cardinality' :
      (object.remainderSupport packing).card +
          data.windowOrder * packing.card =
        object.vertexCount :=
    object.remainderSupport_card_add_eq valid
  have remEq : object.vertexCount -
      data.windowOrder * packing.card =
      (object.remainderSupport packing).card := by omega
  have three := cubic
  simp only [coldExternalStubCount, Parameters.surplusThreshold] at below ⊢
  rw [three, remEq] at below
  rw [three]
  obtain ⟨o, ho⟩ : ∃ o, data.windowOrder = o + 1 :=
    ⟨data.windowOrder - 1, by have := data.windowOrder_pos; omega⟩
  rw [ho] at below ⊢
  have stubsEq : 3 * (o + 1) - 2 * (o + 1 - 1) = o + 3 := by omega
  rw [stubsEq] at below
  simp only [Nat.add_sub_cancel] at below ⊢
  nlinarith [below, Nat.zero_le ((o + 3) * packing.card),
    Nat.zero_le (data.spineScale * Core.ceilSqrt object.vertexCount),
    Nat.zero_le (data.bridgeMassFactor * data.dischargeScale *
      (data.spineScale * Core.ceilSqrt object.vertexCount))]

/-- **`def:cold-window-ledger`: `θ < 1/78` forces `τ(θ) < 1/4`.**  The exact
route-`8` private-support comparison `(δs+1)·(stubs·p + T(n)) + δ·F·s·T(n) <
δ·(n − order·p)` of node `[146]` implies the exact deficiency comparison
`s·(δ·order·p + T(n)) < s·2(order−1)·p + (n − order·p)` of node `[160]`: after
dividing by `δ`, the remainder exceeds `s·(stubs·p + T(n))`, and
`stubs = δ·order − 2(order−1)`.  (At the registered numbers this is
`195p + 109T < 3|R|` against `3|R| ≤ 180p + 12T`.) -/
theorem denseDeficiencyBelow_of_coldRoute8Below (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (below : ColdRoute8BelowStatement data object) :
    DenseDeficiencyBelowStatement data object := by
  unfold ColdRoute8BelowStatement coldExternalStubCount Parameters.surplusThreshold at below
  unfold DenseDeficiencyBelowStatement
  set a := data.threshold
  set s := data.dischargeScale
  set k := data.windowOrder
  set F := data.bridgeMassFactor
  set p := (canonicalWindowPacking data object).card
  set T := data.spineScale * Core.ceilSqrt object.vertexCount
  set X := object.vertexCount - k * p
  set c := a * k - 2 * (k - 1)
  -- `δ·s·(stubs·p + T) ≤ (δs+1)·(stubs·p + T) < δ·X`, so `s·(stubs·p + T) < X`.
  have scaled : a * (s * (c * p + T)) < a * X := by
    have grow : a * (s * (c * p + T)) ≤ (a * s + 1) * (c * p + T) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  have remainder : s * (c * p + T) < X := Nat.lt_of_mul_lt_mul_left scaled
  -- `δ·order ≤ stubs + 2(order−1)`, scaled by `s·p`.
  have split : a * k ≤ c + 2 * (k - 1) := by omega
  have splitScaled : s * (a * (k * p)) ≤ s * (c * p) + s * (2 * (k - 1) * p) := by
    have := Nat.mul_le_mul_right p split
    have := Nat.mul_le_mul_left s this
    calc s * (a * (k * p)) = s * (a * k * p) := by rw [Nat.mul_assoc a]
      _ ≤ s * ((c + 2 * (k - 1)) * p) := this
      _ = s * (c * p) + s * (2 * (k - 1) * p) := by rw [Nat.add_mul, Nat.mul_add]
  rw [Nat.mul_add s (a * (k * p)) T]
  rw [Nat.mul_add s (c * p) T] at remainder
  omega

/-- **Node `[173]`, `lem:exact-collision-test`, no arm.**  If the remainder
`R₀` of the fixed maximum packing is not negatively charged, its net charge is
nonnegative. -/
theorem exactCollisionFails_of_not_netChargeCap (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (notCap : ¬ NetChargeCapStatement data object) :
    ExactCollisionFailsStatement data object := by
  exact (Graph.FiniteObject.not_negativeNetCharge_iff object _ _ _).1 notCap

/-- **Node `[174]`, `lem:exact-collision-test`, the failure consequence.**  At
the fixed maximum packing `P₀` the remainder has nonnegative net charge; the exact
boundary demand `def⁺(R) ≤ e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`, the count
`|R| + order·p = n` and the hot/cold split `p = |𝒫_hot| + |𝒫_cold|` rearrange
it to `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`. -/
theorem absorbedConfigurationResidual_of_exactCollisionFails (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (fails : ExactCollisionFailsStatement data object)
    (demand : BoundaryDemandStatement data object)
    (split : HotColdWindowStatement data object) :
    AbsorbedConfigurationResidualStatement data object := by
  classical
  simp only [AbsorbedConfigurationResidualStatement,
    ExactCollisionFailsStatement, BoundaryDemandStatement] at fails demand ⊢
  set packing := canonicalWindowPacking data object with packingDef
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have cardinality : packing.card = object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  have nonneg := fails
  obtain ⟨deficiencyLe, incidenceLe⟩ := demand
  have sizes := object.remainderSupport_card_add_eq valid
  obtain ⟨_, canonicalCard, _, _, _, disjoint, cover⟩ := split
  -- `p = |𝒫_hot| + |𝒫_cold|`: the fixed packing is the disjoint union.
  have union :
      canonicalWindowPacking data object =
        canonicalHotWindows data object ∪
          canonicalColdWindows data object := by
    ext window
    simp only [Finset.mem_union]
    exact cover window
  have countEq :
      packing.card =
        (canonicalHotWindows data object).card +
          (canonicalColdWindows data object).card := by
    rw [packingDef, union, Finset.card_union_of_disjoint disjoint]
  rw [← countEq]
  unfold Graph.FiniteObject.NonNegativeNetCharge at nonneg
  unfold Parameters.netChargeCoefficient
  -- `e(R,W) ≤ (δ·order − 2(order−1))·p + σ_W`, in both truncation cases.
  have assoc :
      data.threshold * data.windowOrder * packing.card =
        data.threshold * (data.windowOrder * packing.card) :=
    Nat.mul_assoc _ _ _
  have supply :
      object.boundaryIncidence
          (object.remainderSupport packing) ≤
        (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) *
            packing.card +
          object.ambientSurplus
            (Graph.FiniteObject.windowSupport packing) data.threshold := by
    rcases Nat.le_total (2 * (data.windowOrder - 1))
        (data.threshold * data.windowOrder) with small | large
    · have recombine :
          (data.threshold * data.windowOrder - 2 * (data.windowOrder - 1)) *
              packing.card +
            2 * (data.windowOrder - 1) * packing.card =
            data.threshold * data.windowOrder * packing.card := by
        rw [← Nat.add_mul, Nat.sub_add_cancel small]
      omega
    · rw [Nat.sub_eq_zero_of_le large, Nat.zero_mul, Nat.zero_add]
      have := Nat.mul_le_mul_right packing.card large
      omega
  have scaledDeficiency := Nat.mul_le_mul_left data.dischargeScale deficiencyLe
  have scaledSupply := Nat.mul_le_mul_left data.dischargeScale supply
  rw [Nat.mul_add] at scaledSupply
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- **Nodes `[57]`--`[58]`, `lem:netcharge-superadd`.**  A remainder of negative
total charge has a connected canonical piece of negative charge. -/
theorem netChargeLocalization (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    NetChargeLocalizationStatement data object :=
  fun negative =>
    object.exists_canonicalPiece_negativeNetCharge
      (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold data.dischargeScale negative

/-- **Node `[59]`, yes arm.**  `N₀(R₀) ≥ 0` at the fixed maximum packing `P₀`. -/
theorem netChargeNonNegative_of_nonNegative (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (nonNegative : object.NonNegativeNetCharge
      (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold data.dischargeScale) :
    NetChargeNonNegativeStatement data object :=
  nonNegative

/-- **Node `[59]`, no arm.**  `N₀(R) < 0` at the fixed maximum packing. -/
theorem netChargeNegative_of_not_nonNegative (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (notNonNegative : ¬ object.NonNegativeNetCharge
      (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold data.dischargeScale) :
    NetChargeNegativeStatement data object :=
  Nat.lt_of_not_le notNonNegative

/-- **Node `[61]`, `prop:negative-net-charge`.**  The negative remainder of the
fixed maximum packing, localized through the canonical component
decomposition, has a connected negative piece. -/
theorem negativeSupport_of_netChargeNegative (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (negativeFact : NetChargeNegativeStatement data object)
    (localization : NetChargeLocalizationStatement data object) :
    NegativeSupportStatement data object := by
  obtain ⟨component, present, charge⟩ := localization negativeFact
  exact ⟨component, present, charge⟩

/-- **`lem:bridgeless`.**  A bridge of the selected minimal counterexample
contracts to a smaller counterexample; the degree side condition is the
baseline `δ ≥ 3`. -/
theorem bridgeless_of_selection
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (three : 3 ≤ data.threshold)
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    BridgelessStatement object := fun contraction => by
  have degreeSum : data.threshold + 2 ≤
      object.degree contraction.tail + object.degree contraction.head := by
    have left := le_trans baseline (object.minDegree_le_degree contraction.tail)
    have right := le_trans baseline (object.minDegree_le_degree contraction.head)
    omega
  exact contraction.hasReturn_of_minimal (LengthOK := data.LengthOK)
    degreeSum baseline selection.1 selection.2

end Hypostructure.Graph.Contracts.Spine
