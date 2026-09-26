import Hypostructure.Graph.Contracts.RouteEight.EntryCensus

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
            receiver load basin :=
    Or.inr (Or.inl (route8Entry_smallCoreQuotient data object piece receiver load
      (Finset.mem_filter.mp receiverMem).1 loadRouted minimal.1 parity alphaSmall))
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
