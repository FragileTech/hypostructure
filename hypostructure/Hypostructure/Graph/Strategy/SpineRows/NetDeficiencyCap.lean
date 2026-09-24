import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[56]`: the large-budget net-deficiency cap (density-cap arm)

This is the manuscript's displayed bound `def⁺(R) − σ(R) ≤ (1/4 − ε)|R|`
"for all sufficiently large `n`", in the exact cleared finite form: reading the
density cap and the registered sufficiently-large predicate gives the strict
scaled inequality the net-charge step consumes.  The implication is stored on
the literal Residual C ledger of the `[24]` bounded arm. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def netDeficiencyCapRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .densityCap]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _residual := (inputs.get (K .largeBudgetResidual)).down
      .cons (key := K .netDeficiencyCap)
        (show Value BranchState Presentation presentation data
            .netDeficiencyCap inputs.current from
          ⟨by
            intro packing valid cardinality large
            have density :
                2 * (data.windowRate *
                  data.separatedScaleCount inputs.current.object.vertexCount *
                  inputs.current.object.windowPackingNumber data.windowOrder) ≤
                (Graph.dyadicScaleCount inputs.current.object + 1) *
                  (data.threshold * inputs.current.object.vertexCount +
                    data.surplusThreshold inputs.current.object.vertexCount) +
                data.densitySlack * (data.windowRate *
                  data.separatedScaleCount inputs.current.object.vertexCount) *
                  data.surplusThreshold inputs.current.object.vertexCount :=
              (inputs.get (K .densityCap)).down
            have density' :
                2 * (data.windowRate * Nat.log2 inputs.current.object.vertexCount *
                  packing.card) ≤
                (Nat.log2 inputs.current.object.vertexCount + 1) *
                  (data.threshold * inputs.current.object.vertexCount +
                    data.spineScale *
                      Core.ceilSqrt inputs.current.object.vertexCount) +
                data.densitySlack * (data.windowRate * Nat.log2 inputs.current.object.vertexCount) *
                  (data.spineScale *
                    Core.ceilSqrt inputs.current.object.vertexCount) := by
              rw [data.separatedScaleCount_eq_log2, Graph.dyadicScaleCount,
                ← cardinality] at density
              simpa [Data.surplusThreshold] using density
            have cardinality' :
                data.windowOrder * packing.card +
                    (inputs.current.object.remainderSupport packing).card =
                  inputs.current.object.vertexCount := by
              simpa [Nat.add_comm] using
                inputs.current.object.remainderSupport_card_add_eq valid
            have thresholdPos : 0 < data.threshold :=
              lt_of_lt_of_le (by omega) data.three_le_threshold
            have debitLe :
                2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
              calc
                2 * (data.windowOrder - 1) ≤ 2 * data.windowOrder := by omega
                _ ≤ data.threshold * data.windowOrder :=
                  Nat.mul_le_mul_right data.windowOrder
                    (le_trans (by omega) data.three_le_threshold)
            exact Graph.FiniteObject.strictCap_of_densityCap_of_sufficientlyLarge
              data.threshold data.dischargeScale data.windowOrder data.windowRate
              data.spineScale data.densitySlack inputs.current.object.vertexCount packing.card
              (inputs.current.object.remainderSupport packing).card
              data.windowOrder_pos thresholdPos debitLe data.netCapRateSlack
              large density' cardinality'⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
