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

/-! ## Node `[21]`: the finite barrier enumeration

`lem:curv-enum` is already computed by the registered certified presentation.
This row reads no predecessor fact (`Requires := []`, exactly as `lem:labels`
at node `[18]`) and publishes the safe, curvature-positive, and flat counts
and their exact logarithmic entropy ratio on the literal incoming ledger.  It
performs no second enumeration, copies no numerical answer, and constructs no
label carrier.  `lem:curv-enum` is projected directly from the registered
presentation.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def barrierEnumerationRow :
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
    `Hypostructure.Graph.Strategy.Spine.barrierEnumeration
    { Requires := []
      Produces := [K .barrierEnumeration]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .barrierEnumeration)
        (show Value BranchState Presentation presentation data
            .barrierEnumeration inputs.current from
          ⟨by
            change BarrierEnumerationStatement data
            let barrier := data.windowBarrier
            letI := barrier.indexFintype
            let row := data.curvatureBarrierRow
            let left := barrier.table.counts.leftLength row
            let right := barrier.table.counts.rightLength row
            let safe := barrier.table.counts.storedSafe row
            let flat := barrier.table.counts.storedFlat row
            let curvaturePositive := safe - flat
            refine ⟨safe, curvaturePositive, flat, rfl, rfl, rfl,
              barrier.table.storedSafe_eq row, ?_,
              barrier.table.storedFlat_eq row, rfl⟩
            change barrier.table.counts.storedSafe row -
                barrier.table.counts.storedFlat row =
              barrier.profile.obstructedCount left right
            rw [barrier.table.storedSafe_eq, barrier.table.storedFlat_eq]
            rfl⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
