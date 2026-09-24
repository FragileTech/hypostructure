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
@[reducible] noncomputable def route8CarrierCutParityRow
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
    `Hypostructure.Graph.Strategy.Spine.route8CarrierCutParity
    { Requires := [K .route8TrueResidual]
      Produces := [K .route8CarrierCutParity]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let trueResidual := inputs.get (K .route8TrueResidual)
      .cons (key := K .route8CarrierCutParity)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let routeEight :=
            (inputs.current.object.canonicalPieces support).filter
              (Route8Survives data inputs.current.object packing)
          change Route8CarrierCutParity data inputs.current.object
          dsimp only [Route8CarrierCutParity]
          intro component componentMem
          let piece := inputs.current.object.pieceSupport support component
          intro receiver receiverMem
          intro load loadMem
          let index : Graph.Route8Census.Index inputs.current.object :=
            (piece, receiver, load)
          let basin := Graph.Route8Census.basin inputs.current.object
            data.threshold index
          let presented := Graph.Route8Census.presented inputs.current.object
            data.threshold data.LengthOK index
          let entry := presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)
          intro coordinate retained event eventEq internalEdge outsideEdge
          have componentFacts := trueResidual.down.2 component componentMem
          have receiverFacts := componentFacts.2 receiver receiverMem
          have loadFacts := receiverFacts.2.2 load loadMem
          have minimal := loadFacts.2.1
          have basinSubset : basin ⊆ piece := minimal.1.1
          obtain ⟨insideLeft, _insideRight, insideEdgeMem,
            insideLeftBasin, _insideRightBasin⟩ := internalEdge
          have insideWalk : insideLeft ∈ event.walk.support :=
            event.walk.fst_mem_support_of_mem_edges insideEdgeMem
          have insidePiece : insideLeft ∈ piece :=
            basinSubset insideLeftBasin
          obtain ⟨outsideLeft, outsideRight, outsideEdgeMem,
            outsidePiece⟩ := outsideEdge
          have outsideWitness : ∃ outside,
              outside ∈ event.walk.support ∧ outside ∉ piece := by
            rcases outsidePiece with outsideLeftPiece | outsideRightPiece
            · exact ⟨outsideLeft,
                event.walk.fst_mem_support_of_mem_edges outsideEdgeMem,
                outsideLeftPiece⟩
            · exact ⟨outsideRight,
                event.walk.snd_mem_support_of_mem_edges outsideEdgeMem,
                outsideRightPiece⟩
          obtain ⟨outside, outsideWalk, outsidePiece⟩ := outsideWitness
          have crossing : presented.Crossing coordinate :=
            ⟨event, eventEq, ⟨insideLeft, insideWalk, insidePiece⟩,
              outside, outsideWalk, outsidePiece⟩
          have parity : 2 ≤ (presented.car coordinate).card :=
            presented.two_le_card_car crossing
          have retainedSubset : entry.car coordinate ⊆ entry.essentialCore :=
            (entry.mem_retained.mp retained).2
          rw [Finset.inter_eq_left.mpr retainedSubset]
          exact parity⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
