import Hypostructure.Graph.Strategy.Route8Run

/-!
# Fixture: node `[103]`, the exit-`(5)` target-complete compression

`Spine.runRouteEight` runs node `[103]` as two `Decision`s: the exit test
itself, and — on its yes arm — the realization test of
`lem:typeA-exits-discharged`, *"if the compression is realized by a smaller
proper atom, it contradicts hereditary target-uncompressibility; if it occurs
only at the trace-basin response level, it is exactly failure alternative (b) in
`def:typeA-trace-basin` and therefore is not an admissible route-8 residual."*

This fixture checks that both halves of that sentence are what the run
produces, at the framework's own `Spine.Data`:

* the realized arm's index carries `lem:replacement`'s compression *and* Core's
  closure entry, and every fact the branch already had is still in it;
* the closure is not asserted by a row: the compression fact and node `[14]`'s
  `cor:uncompressible` are contradictory on their own, and the canonical
  dispatcher returns `closed` on the resulting index;
* the response-level arm carries neither the closure entry nor
  `typeAExitFiveFree`, so it is neither a closed terminal nor an admissible
  route-8 residual — which is exactly what the manuscript says about
  alternative (b);
* the realized arm's audit accounts for every fact with chronological commits,
  no fact twice, and no empty commit.
-/

namespace Hypostructure.Fixtures.Route8ExitFive

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The key index of node `[103]`'s closed arm, over the Type A residual of
node `[63]` that `Spine.run` already reaches. -/
abbrev closedKeys : FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.exitFiveClosedKeys
    (typeALowSurplusKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-- The key index of node `[103]`'s response-level arm, over the same
residual. -/
abbrev traceLevelKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys
    (typeALowSurplusKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-! ## The realized arm -/

/-- **No history is lost at node `[103]`.**

Every fact the branch carried into the node is still indexed by the arm it
leaves on, so nothing upstream was archived, rebased or re-scoped. -/
theorem closed_arm_retains_every_incoming_fact
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (key : FactKey (Input BranchState Presentation presentation data))
    (member : key ∈ known) :
    key ∈ Hypostructure.Graph.Strategy.Spine.exitFiveClosedKeys known := by
  simp only [Hypostructure.Graph.Strategy.Spine.exitFiveClosedKeys,
    List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr member))))

/-- **The realized arm carries `lem:replacement`'s compression and Core's
closure entry.** -/
theorem closed_arm_carries_compression_and_closure
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .typeAExitFiveCompression ∈
        Hypostructure.Graph.Strategy.Spine.exitFiveClosedKeys known ∧
      closed (BranchState := BranchState) (presentation := presentation)
          (data := data) ∈
        Hypostructure.Graph.Strategy.Spine.exitFiveClosedKeys known := by
  constructor <;>
    simp [Hypostructure.Graph.Strategy.Spine.exitFiveClosedKeys]

/-- **The closure is read off the two committed statements.**

Node `[14]`'s `cor:uncompressible` says the object has no target-complete
compression on a proper support; node `[103]`'s realized arm says it has one.
Neither row mentions the other, and this is the whole content of the
contradiction. -/
theorem compression_contradicts_uncompressible
    (input : Input BranchState Presentation presentation data)
    (uncompressible : (K (data := data) .uncompressible).At input)
    (compression : (K (data := data) .typeAExitFiveCompression).At input) :
    False :=
  Incompatible.contradiction (Residual :=
    Input BranchState Presentation presentation data) input uncompressible
    compression

/-- **The canonical dispatcher returns `closed` on the realized arm.**

The arm is a terminal for the framework's own router, not merely for the row
that produced it, and it is so for every task list. -/
theorem closed_arm_dispatches_closed
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys)
    (tasks : List (RoutedTask
      (Input BranchState Presentation presentation data))) :
    RoutedTask.dispatchFor history tasks = .closed := by
  rfl

/-- **The realized arm's audit accounts for every fact of the branch.** -/
theorem closed_arm_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice on the realized arm.** -/
theorem closed_arm_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **No empty commit occurs on the realized arm.** -/
theorem closed_arm_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected closedKeys) :
    List.Forall (fun record => record.produced ≠ [])
      (ExactLedger.audit history).commits :=
  ExactLedger.audit_commits_nonempty history

/-! ## The response-level arm -/

/-- **Alternative (b) is not an admissible route-8 residual.**

The response-level arm has no `typeAExitFiveFree` in its index, so the exit-`(5)`
absence clause (R2) that the route-8 arm reads is not available on it and node
`[109]`'s placement cannot be entered from here. -/
theorem trace_level_arm_has_no_exit_five_absence
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (fresh : K (data := data) .typeAExitFiveFree ∉ known) :
    K (data := data) .typeAExitFiveFree ∉
      Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys known := by
  simp [Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys, fresh]

/-- **The response-level arm is left open, as the manuscript leaves it.**

It carries no closure entry: the manuscript closes exit `(5)` only in the
realized case, and records the other as failure alternative (b). -/
theorem trace_level_arm_is_not_closed
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (fresh : closed (BranchState := BranchState) (presentation := presentation)
      (data := data) ∉ known) :
    closed (BranchState := BranchState) (presentation := presentation)
        (data := data) ∉
      Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys known := by
  simp [Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys, fresh]

/-- **The response-level arm keeps the whole incoming branch too.** -/
theorem trace_level_arm_retains_every_incoming_fact
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (key : FactKey (Input BranchState Presentation presentation data))
    (member : key ∈ known) :
    key ∈ Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys known := by
  simp only [Hypostructure.Graph.Strategy.Spine.exitFiveTraceLevelKeys,
    List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr member)))

end Hypostructure.Fixtures.Route8ExitFive
