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

/-! ## Node `[56]`, the large-budget net-deficiency cap (dense arm).

On the `[21]` unrealized residual the manuscript's `τ(θ) < 1/4` reading of
`prop:negative-net-charge` is a decision of its own (`K .denseDeficiencyBelow`,
the exact strict comparison at the fixed maximal packing); this row is node
`[56]` on its yes arm: the same conditional cap for every maximal packing, read
off that decision (all maximal packings have the same size and the same
remainder count `n − order·p`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def denseNetDeficiencyCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.denseNetDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .denseDeficiencyBelow]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _residual := (inputs.get (K .largeBudgetResidual)).down
      let below := (inputs.get (K .denseDeficiencyBelow)).down
      .cons (key := K .netDeficiencyCap)
        (show Value BranchState Presentation presentation data
            .netDeficiencyCap inputs.current from
          ⟨by
            intro packing valid cardinality _large
            have canonicalCard :
                (canonicalWindowPacking data inputs.current.object).card =
                  inputs.current.object.windowPackingNumber data.windowOrder :=
              (Classical.choose_spec
                (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)).2
            change data.dischargeScale *
                (data.threshold * (data.windowOrder *
                  (canonicalWindowPacking data inputs.current.object).card) +
                  data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount) <
              data.dischargeScale *
                  (2 * (data.windowOrder - 1) *
                    (canonicalWindowPacking data inputs.current.object).card) +
                (inputs.current.object.vertexCount - data.windowOrder *
                  (canonicalWindowPacking data inputs.current.object).card) at below
            rw [canonicalCard, ← cardinality] at below
            have cardinality' :
                data.windowOrder * packing.card +
                    (inputs.current.object.remainderSupport packing).card =
                  inputs.current.object.vertexCount := by
              simpa [Nat.add_comm] using
                inputs.current.object.remainderSupport_card_add_eq valid
            have remainder :
                inputs.current.object.vertexCount - data.windowOrder * packing.card =
                  (inputs.current.object.remainderSupport packing).card := by
              omega
            rw [remainder] at below
            exact below⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
