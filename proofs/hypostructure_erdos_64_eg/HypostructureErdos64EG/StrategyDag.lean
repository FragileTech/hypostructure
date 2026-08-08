import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Erdős--Gyárfás strategy DAG, rooted on the entry spine

This application-owned file contains only the root topology.  The generic
`runChapterOne` endpoint invokes `runCore` once, attaches every implemented
continuation immediately, and returns only the genuine next continuation
families with their literal `ExactLedger` ancestry.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-! ## The problem the spine argues about is this problem

Not a copy and not a coincidence: `Problem.lean` registers the baseline degree
that `spineData.threshold` reads, so the spine's own problem *is* the one the
public target is stated against.  The check below is `rfl`; if the two ever
drifted it would stop being one. -/

example :
    problem.{u} =
      Hypostructure.Graph.Strategy.Spine.problem BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        spineData.{u} := rfl

/-- The public target's predicate is the spine's accepted-cycle predicate.  It
is `rfl` for the same reason: `minimumDegreeCycleTarget`'s `Predicate` field is
`HasCycleWithLength` at the length family this problem registers.  It is an
`example` rather than a theorem: this file authors topology, and a named lemma
here would be an application-local helper.  The endpoint below passes the same
`rfl` to the framework, which is what actually consumes it. -/
example :
    (target.{u}).Predicate =
      Graph.HasCycleWithLength (spineData.{u}).LengthOK := rfl

/-! ## One root execution, with no exported intermediate

This unnamed check is the complete application topology currently available.
Because it is an `example`, the surviving internal phase boundary is not an
application endpoint.
-/

noncomputable example
    (opened : Core.Strategy.OpenedScope
      (P := Hypostructure.Graph.Strategy.Spine.problem BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        spineData.{u})
      (Hypostructure.Graph.Strategy.Spine.K (BranchState := BranchState)
        (presentation := erdosReceiverLoadProfile) (data := spineData.{u})
        .selection))
    (sufficientlyLarge :
      Graph.FiniteObject.SufficientlyLargeForNetCap (spineData.{u}).threshold
        (spineData.{u}).dischargeScale (spineData.{u}).windowOrder
        (spineData.{u}).windowRate (spineData.{u}).spineScale
        opened.selected.object.vertexCount) :
    ChapterOneContinuation opened.selected :=
  runChapterOne (BranchState := BranchState)
    (presentation := erdosReceiverLoadProfile) (data := spineData.{u})
    target.{u} rfl opened sufficientlyLarge

end HypostructureErdos64EG
