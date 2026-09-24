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

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- The silent entry of the shared exit segment: node `[94]`
(`lem:typeA-unpeeled-silent-routing`) commits the same saturated exit entry at
the empty peeling set. -/
@[reducible] noncomputable def typeASilentExitEntryRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitEntry
    { Requires := [K .typeAVisibleFirstExcess]
      Produces := [K .typeASaturatedExitEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedExitEntry)
        (show Value BranchState Presentation presentation data
            .typeASaturatedExitEntry inputs.current from ⟨by
          classical
          obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            _noVisible,
            receiver, isReceiver, saturated, _silent, _count⟩ :=
            (inputs.get (K .typeAVisibleFirstExcess)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, ∅, Finset.empty_subset _,
            (Graph.ExitFour.saturatedAfter_empty piece data.threshold
              data.dischargeScale receiver).mpr saturated,
            Graph.ExitFour.peeledByWitnesses_empty _ piece data.threshold
              data.dischargeScale receiver⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
