import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineRun

/-!
# Erdős--Gyárfás strategy DAG, rooted on the entry spine

Block A has exactly one implementation, `Graph.Strategy.Spine`, and this module
roots the DAG on it: `strategyDag` below runs it against the data `Problem.lean`
registers, with Figure 8's Type A exit list and node `[19]`'s sparse surplus
branch attached.

What that gives, and what it does not, is stated exactly.  `strategyDag` is a total
function from an opened minimal-counterexample scope to one of the block's
exits, every one of which carries the canonical `ExactLedger` at the residual
its branch argued about.  It is **not** a proof of `OfficialStatement`: the
rows that turn those exits into a contradiction -- rows `[11]` onwards of the
audit -- are not attached here, and until they are, no arm closes.

The legacy `Blueprint` topology this module used to hold is retired.  It was a
registry of parallel capability lists resolved by list position; the canonical
API replaces it outright.  It is not preserved here: the porting reference is
the audit and the manuscript, not a commented chain that no longer elaborates.
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

/-! ## Block A, run at this problem -/

/-- **The strategy DAG's endpoint: the entry spine, rooted here.**

`Graph.Strategy.Spine.runWithSurplusBranch` calls `Spine.run` once, continues
its two saturated Type A arms into Figure 8's exit list, continues node
`[19]`'s above arm through the sparse surplus block `[125]`--`[144]`, and
returns every other arm as it stands.  Each exit carries the one canonical
`ExactLedger` at the residual its branch argued about, indexed by exactly the
facts that branch established. -/
noncomputable def strategyDag
    (opened : Core.Strategy.OpenedScope
      (P := Hypostructure.Graph.Strategy.Spine.problem BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        spineData.{u})
      (Hypostructure.Graph.Strategy.Spine.K (BranchState := BranchState)
        (presentation := erdosReceiverLoadProfile) (data := spineData.{u})
        .selection)) :
    SpineWithSurplusResult opened.selected :=
  run
    (BranchState := BranchState) (presentation := erdosReceiverLoadProfile)
    (data := spineData.{u}) target.{u} rfl opened

end HypostructureErdos64EG
