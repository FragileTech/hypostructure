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
@[reducible] noncomputable def route8CarrierDeletionWitnessesRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.route8CarrierDeletionWitnesses
    { Requires := [K .route8TwoCarrierEntry]
      Produces := [K .route8CarrierDeletionWitnesses]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := inputs.get (K .route8TwoCarrierEntry)
      .cons (key := K .route8CarrierDeletionWitnesses)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          obtain ⟨index, indexMem, two⟩ := selected.down
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let routeEight := (inputs.current.object.canonicalPieces support).filter
            (Route8Survives data inputs.current.object packing)
          let entries := Graph.Route8Census.entriesOfComponents
            inputs.current.object packing routeEight data.threshold
              data.dischargeScale
          let presented := Graph.Route8Census.presented inputs.current.object
            data.threshold data.LengthOK index
          let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
          refine ⟨index, indexMem, two, ?_⟩
          exact Graph.Route8.twoCarrierDeletionWitnesses (Target :=
            Graph.HasCycleWithLength data.LengthOK) entry.carriers
            entry.coordinates entry.car entry.car_subset entry.state entries
            (Graph.Route8Census.core inputs.current.object data.threshold
              data.LengthOK) two rfl⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
