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
@[reducible] noncomputable def route8TrueResidualRow
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
    `Hypostructure.Graph.Strategy.Spine.route8TrueResidual
    { Requires := [K .route8ResidualProfile, K .route8GlobalSqueeze]
      Produces := [K .route8TrueResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let profile := inputs.get (K .route8ResidualProfile)
      let _global := inputs.get (K .route8GlobalSqueeze)
      .cons (key := K .route8TrueResidual)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let routeEight :=
            (inputs.current.object.canonicalPieces support).filter
              (Route8Survives data inputs.current.object packing)
          change Route8TrueResidual data inputs.current.object
          refine ⟨profile.down, ?_⟩
          intro component componentMem
          let piece := inputs.current.object.pieceSupport support component
          have survives :
              Route8Survives data inputs.current.object packing component :=
            (Finset.mem_filter.mp componentMem).2
          obtain ⟨_negative, _zero, silentFirst, entries⟩ := survives
          refine ⟨silentFirst, ?_⟩
          intro receiver receiverMem
          have receiverFacts :
              receiver ∈ inputs.current.object.receivers piece data.threshold ∧
                inputs.current.object.Saturated piece data.threshold
                  data.dischargeScale receiver := by
            simpa [Graph.VisibleEntry.saturatedReceivers] using receiverMem
          have isReceiver :
              inputs.current.object.IsReceiver piece data.threshold receiver :=
            inputs.current.object.mem_receivers.mp receiverFacts.1
          refine ⟨isReceiver, receiverFacts.2, ?_⟩
          intro load loadMem
          let index : Graph.Route8Census.Index inputs.current.object :=
            (piece, receiver, load)
          let basin := Graph.Route8Census.basin inputs.current.object
            data.threshold index
          obtain ⟨routeEntry, noExitFour⟩ :=
            entries receiver receiverMem load loadMem
          obtain ⟨selectedBasin, selectedEq, minimal⟩ := routeEntry
          have basinEq : basin = selectedBasin := by
            change (Graph.Route8.TraceBasin.select? inputs.current.object piece
              data.threshold receiver load).getD ∅ = selectedBasin
            rw [selectedEq]
            rfl
          refine ⟨?_, ?_, noExitFour⟩
          · change (Graph.Route8.TraceBasin.select? inputs.current.object piece
              data.threshold receiver load) = some basin
            rw [basinEq]
            exact selectedEq
          · change Graph.Route8.TraceBasin.TargetCompleteMinimal
              inputs.current.object piece data.threshold data.LengthOK receiver load basin
            rw [basinEq]
            exact minimal⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
