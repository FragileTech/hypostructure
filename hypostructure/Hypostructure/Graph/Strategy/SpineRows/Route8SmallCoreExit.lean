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

set_option maxHeartbeats 1000000 in
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8SmallCoreExitRow
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
    `Hypostructure.Graph.Strategy.Spine.route8SmallCoreExit
    { Requires := [K .route8TrueResidual, K .route8SmallCoreEntry,
          K .route8CarrierCutParity]
      Produces := [K .route8SmallCoreCollapse]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let trueResidual := inputs.get (K .route8TrueResidual)
      let smallFact := inputs.get (K .route8SmallCoreEntry)
      let cutParity := inputs.get (K .route8CarrierCutParity)
      .cons (key := K .route8SmallCoreCollapse)
        ⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          refine ⟨smallFact.down, ?_⟩
          obtain ⟨_componentCore, component, componentMem, receiver,
            receiverMem, load, loadMem, alphaSmall⟩ := smallFact.down
          let packing := canonicalWindowPacking data inputs.current.object
          let support := inputs.current.object.remainderSupport packing
          let piece := inputs.current.object.pieceSupport support component
          let index : Graph.Route8Census.Index inputs.current.object :=
            (piece, receiver, load)
          let basin := Graph.Route8Census.basin inputs.current.object
            data.threshold index
          let presented := Graph.Route8Census.presented inputs.current.object
            data.threshold data.LengthOK index
          let entry := presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)
          have minimal : Graph.Route8.TraceBasin.TargetCompleteMinimal
              inputs.current.object piece data.threshold data.LengthOK receiver load
                basin :=
            (trueResidual.down.2 component componentMem).2 receiver receiverMem |>.2.2
              load loadMem |>.2.1
          have loadRouted : load ∈ inputs.current.object.routedLoads piece
              data.threshold receiver := by
            have excess := (Finset.mem_sdiff.mp loadMem).1
            exact (Finset.mem_sdiff.mp excess).1
          have loadDegree : inputs.current.object.internalDegree piece load =
              data.threshold :=
            (inputs.current.object.mem_routedLoads.mp loadRouted).2.1
          have receiverDegree : inputs.current.object.internalDegree piece receiver <
              data.threshold :=
            (inputs.current.object.mem_receivers.mp
              (by
                have receiverFacts :
                    receiver ∈ inputs.current.object.receivers piece data.threshold ∧
                      inputs.current.object.Saturated piece data.threshold
                        data.dischargeScale receiver := by
                  simpa [Graph.VisibleEntry.saturatedReceivers] using receiverMem
                exact receiverFacts.1)).2
          have loadNeReceiver : load ≠ receiver := by
            intro same
            subst load
            omega
          obtain ⟨trace, traceSelected, traceInside⟩ := minimal.1.2.1
          have tracePositive : 0 < trace.1.length := by
            apply Nat.pos_of_ne_zero
            intro zero
            exact loadNeReceiver (trace.1.eq_of_length_eq_zero zero)
          let crossing := (entry.retained entry.essentialCore).filter
            (fun coordinate =>
              ∃ event : Graph.Route8.CoordinateEvent inputs.current.object,
                presented.event? coordinate = some event ∧
                  (∃ left right : inputs.current.object.Vertex,
                    s(left, right) ∈ event.walk.edges ∧
                      left ∈ basin ∧ right ∈ basin) ∧
                    ∃ left right : inputs.current.object.Vertex,
                      s(left, right) ∈ event.walk.edges ∧
                        (left ∉ piece ∨ right ∉ piece))
          have parity : ∀ coordinate ∈ crossing,
              2 ≤ (entry.car coordinate).card := by
            intro coordinate member
            obtain ⟨retained, event, eventEq, internalEdge, outsideEdge⟩ :=
              Finset.mem_filter.mp member
            have cut := cutParity.down component componentMem receiver receiverMem
              load loadMem coordinate retained event eventEq internalEdge outsideEdge
            have retainedSubset : entry.car coordinate ⊆ entry.essentialCore :=
              (entry.mem_retained.mp retained).2
            rw [Finset.inter_eq_left.mpr retainedSubset] at cut
            exact cut
          have alternatives :
              Graph.Route8.TraceBasin.TraceLocalTargetDefect
                  inputs.current.object piece data.threshold data.LengthOK
                    receiver load basin ∨
                (∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient
                  inputs.current.object piece data.threshold data.LengthOK
                    receiver load basin retained) ∨
                Graph.Route8.TraceBasin.TraceDelocalization
                  inputs.current.object piece data.threshold data.LengthOK
                    receiver load basin ∨
                Graph.Route8.TraceBasin.TraceSurvivingSeparator
                  inputs.current.object piece data.threshold data.LengthOK
                    receiver load basin := by
            apply entry.smallCoreCollapseFacts parity
            intro crossingEq
            right
            left
            let traceCoordinate : presented.Coordinate :=
              Graph.Route8.PresentedEntry.TraceCoordinate.traceIncidence
            let retained :=
              (entry.retained entry.essentialCore \ crossing).erase traceCoordinate
            refine ⟨retained, ?_, ?_, ?_⟩
            · intro coordinate member
              have retainedMember := (Finset.mem_erase.mp member).2
              have crossingMember := (Finset.mem_sdiff.mp retainedMember).1
              exact (entry.mem_retained.mp crossingMember).1
            · refine ⟨traceCoordinate, ?_, ?_, ?_⟩
              · change Graph.Route8.PresentedEntry.TraceCoordinate.traceIncidence ∈
                  Graph.Route8.PresentedEntry.traceCoordinates
                    inputs.current.object piece data.threshold receiver load
                exact Finset.mem_insert_self _ _
              · exact Finset.notMem_erase _ _
              · left
                refine ⟨rfl, trace, traceSelected, tracePositive, ?_⟩
                exact traceInside
            · have retainedBaseEq :
                  Graph.Route8.PresentedEntry.retainedBaseCoordinates
                      inputs.current.object piece retained =
                    Graph.Route8.PresentedEntry.retainedBaseCoordinates
                      inputs.current.object piece
                        (entry.retained entry.essentialCore \ crossing) := by
                apply Finset.ext
                intro coordinate
                simp only [Graph.Route8.PresentedEntry.retainedBaseCoordinates,
                  Finset.mem_filter]
                constructor
                · intro member
                  exact ⟨member.1, (Finset.mem_erase.mp member.2).2⟩
                · intro member
                  refine ⟨member.1, Finset.mem_erase.mpr ⟨?_, member.2⟩⟩
                  simp [traceCoordinate]
              have traceErase :
                  presented.state retained =
                    presented.state (entry.retained entry.essentialCore \ crossing) := by
                change Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold data.LengthOK
                      (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                        inputs.current.object piece retained) =
                  Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold data.LengthOK
                      (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                        inputs.current.object piece
                          (entry.retained entry.essentialCore \ crossing))
                exact congrArg
                  (Graph.Route8.PresentedEntry.retainedReading
                    inputs.current.object piece basin data.threshold data.LengthOK)
                  retainedBaseEq
              have retainedEq :
                  presented.state retained = entry.restriction entry.essentialCore :=
                traceErase.trans crossingEq
              -- `lem:typeA-one-terminal-collapse` step 3:
              -- the quotient is target-complete against the declared
              -- `u`-supported target algebra (`def:typeA-trace-basin`) because `alpha <= 1`
              -- refutes the failure side -- a surviving mixed return would carry
              -- two distinct boundary incidences of the core
              -- (`lem:typeA-carrier-cut-parity`).  This replaces the
              -- `essentialCore_complete` shortcut.
              exact fun realization _realizes =>
                Graph.Route8.TraceBasin.allQuotientRealizations_declaredEquivalent_of_alpha_le_one
                  alphaSmall realization _
            exact alphaSmall
          refine ⟨component, componentMem, receiver, receiverMem, load, loadMem,
            alphaSmall, alternatives⟩⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
