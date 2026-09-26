import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: nodes `[115]`--`[116]`, the zero/one-core collapse

`lem:typeA-one-terminal-collapse` on the route-`8` collection `𝒳_A`: an entry
with at most one essential incidence realizes one of the trace-basin failure
alternatives of exits `(4)`--`(7)`.  Every such alternative is excluded by the
target-complete minimality the true route-`8` residual records
(`route8TrueResidual_smallCoreCollapse_false`).
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[116]`, `lem:typeA-one-terminal-collapse`**: on the true route-`8`
residual with the carrier cut parity of `lem:typeA-carrier-cut-parity`, a
zero/one-core entry of `𝒳_A` realizes, in order, a trace-local target defect,
a nontrivial target-complete response quotient, a delocalization, or a
surviving separator: the trace-basin alternatives of exits `(4)`--`(7)`. -/
theorem route8SmallCoreCollapse (data : Parameters) (object : FiniteObject.{u})
    (trueResidual : Route8TrueResidual data object)
    (small : Route8SmallCoreEntry data object)
    (cutParity : Route8CarrierCutParity data object) :
    Route8SmallCoreCollapse data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨component, componentMem, receiver,
    receiverMem, load, loadMem, alphaSmall⟩ := small
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let piece := object.pieceSupport support component
  let index : Graph.Route8Census.Index object :=
    (piece, receiver, load)
  let basin := Graph.Route8Census.basin object
    data.threshold index
  let presented := Graph.Route8Census.presented object
    data.threshold data.LengthOK index
  let entry := presented.toEntry
    (Graph.HasCycleWithLength data.LengthOK)
  have minimal : Graph.Route8.TraceBasin.TargetCompleteMinimal
      object piece data.threshold data.LengthOK receiver load
        basin :=
    (trueResidual.2 component componentMem).2 receiver receiverMem |>.2.2
      load loadMem |>.2.1
  have loadRouted : load ∈ object.routedLoads piece
      data.threshold receiver := by
    have excess := (Finset.mem_sdiff.mp loadMem).1
    exact (Finset.mem_sdiff.mp excess).1
  have loadDegree : object.internalDegree piece load =
      data.threshold :=
    (object.mem_routedLoads.mp loadRouted).2.1
  have receiverDegree : object.internalDegree piece receiver <
      data.threshold :=
    (object.mem_receivers.mp
      (by
        have receiverFacts :
            receiver ∈ object.receivers piece data.threshold ∧
              object.Saturated piece data.threshold
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
      ∃ event : Graph.Route8.CoordinateEvent object,
        presented.event? coordinate = some event ∧
          (∃ left right : object.Vertex,
            s(left, right) ∈ event.walk.edges ∧
              left ∈ basin ∧ right ∈ basin) ∧
            ∃ left right : object.Vertex,
              s(left, right) ∈ event.walk.edges ∧
                (left ∉ piece ∨ right ∉ piece))
  have parity : ∀ coordinate ∈ crossing,
      2 ≤ (entry.car coordinate).card := by
    intro coordinate member
    obtain ⟨retained, event, eventEq, internalEdge, outsideEdge⟩ :=
      Finset.mem_filter.mp member
    have cut := cutParity component componentMem receiver receiverMem
      load loadMem coordinate retained event eventEq internalEdge outsideEdge
    have retainedSubset : entry.car coordinate ⊆ entry.essentialCore :=
      (entry.mem_retained.mp retained).2
    rw [Finset.inter_eq_left.mpr retainedSubset] at cut
    exact cut
  have alternatives :
      Graph.Route8.TraceBasin.TraceLocalTargetDefect
          object piece data.threshold data.LengthOK
            receiver load basin ∨
        (∃ retained, Graph.Route8.TraceBasin.TraceResponseQuotient
          object piece data.threshold data.LengthOK
            receiver load basin retained) ∨
        Graph.Route8.TraceBasin.TraceDelocalization
          object piece data.threshold data.LengthOK
            receiver load basin ∨
        Graph.Route8.TraceBasin.TraceSurvivingSeparator
          object piece data.threshold data.LengthOK
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
            object piece data.threshold receiver load
        exact Finset.mem_insert_self _ _
      · exact Finset.notMem_erase _ _
      · left
        refine ⟨rfl, trace, traceSelected, tracePositive, ?_⟩
        exact traceInside
    · have retainedBaseEq :
          Graph.Route8.PresentedEntry.retainedBaseCoordinates
              object piece retained =
            Graph.Route8.PresentedEntry.retainedBaseCoordinates
              object piece
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
            object piece basin data.threshold data.LengthOK
              (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                object piece retained) =
          Graph.Route8.PresentedEntry.retainedReading
            object piece basin data.threshold data.LengthOK
              (Graph.Route8.PresentedEntry.retainedBaseCoordinates
                object piece
                  (entry.retained entry.essentialCore \ crossing))
        exact congrArg
          (Graph.Route8.PresentedEntry.retainedReading
            object piece basin data.threshold data.LengthOK)
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
    alphaSmall, alternatives⟩

/-- **Node `[116]`**: each collapse alternative is excluded by the
target-complete minimality the true route-`8` residual records for that entry
(`def:typeA-true-route8-residual`). -/
theorem route8TrueResidual_smallCoreCollapse_false (data : Parameters)
    (object : FiniteObject.{u})
    (trueResidual : Route8TrueResidual data object)
    (collapse : Route8SmallCoreCollapse data object) : False := by
  classical
  obtain ⟨component, componentMem, receiver, receiverMem, load, loadMem,
    _alphaSmall, alternatives⟩ := collapse
  have minimal :=
    (trueResidual.2 component componentMem).2 receiver receiverMem |>.2.2
      load loadMem |>.2.1
  rcases alternatives with localDefect | compression | delocalization |
      separator
  · exact minimal.2.1 localDefect
  · exact minimal.2.2.1 compression
  · exact minimal.2.2.2.1 delocalization
  · exact minimal.2.2.2.2 separator

end Hypostructure.Graph.Contracts.RouteEight
