import Hypostructure.Graph.Strategy.Route8Run

/-!
# Fixture: node `[105]`, the exit-`(6)` response delocalization

`Spine.runRouteEight` runs node `[105]` as two `Decision`s: the exit test
itself — clause (c) of `def:typeA-trace-basin`, *"an equality among coordinates
of `ρ_u(B_u)` becomes target-complete only after adjoining a larger connected
support `Z ⊋ B_u`, either with `Z ⊊ G` or with `Z = G`"* — and, on its yes arm,
the scope test of `lem:typeA-exits-discharged`, *"Exit (6) is excluded by
`lem:proper-smearing` in the proper-support case and by
`lem:no-silent-global-smearing` in the whole-graph case."*

This fixture checks that both halves of that sentence are what the run
produces, at the framework's own `Spine.Data`:

* both scope arms close — exit `(6)` is a *closed* exit in
  `def:typeA-saturated-exits`, so unlike exit `(5)` neither arm is left open;
* neither closure is asserted by a row: each arm's fact and node `[1]`--`[4]`'s
  `selection` are contradictory on their own, and the canonical dispatcher
  returns `closed` on both resulting indices;
* every fact the branch already had is still in each arm's index;
* the no arm carries (R2) for exit `(6)` and no closure entry, which is the
  cursor node `[109]`'s placement is entered on;
* each closed arm's audit accounts for every fact with chronological commits,
  no fact twice, and no empty commit.
-/

namespace Hypostructure.Fixtures.Route8ExitSix

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The key index of node `[105]`'s proper arm, over the Type A residual of
node `[63]` that `Spine.run` already reaches. -/
abbrev properKeys : FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.exitSixProperKeys
    (typeALowSurplusKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-- The key index of node `[105]`'s global arm, over the same residual. -/
abbrev globalKeys : FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.exitSixGlobalKeys
    (typeALowSurplusKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-- The key index of node `[105]`'s no arm — the cursor node `[107]` is asked
on, and behind it the (R2) entry of node `[109]`. -/
abbrev freeKeys : FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys
    (typeALowSurplusKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-! ## The proper arm: `lem:proper-smearing` -/

/-- **No history is lost on the proper arm.** -/
theorem proper_arm_retains_every_incoming_fact
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (key : FactKey (Input BranchState Presentation presentation data))
    (member : key ∈ known) :
    key ∈ Hypostructure.Graph.Strategy.Spine.exitSixProperKeys known := by
  simp only [Hypostructure.Graph.Strategy.Spine.exitSixProperKeys,
    Hypostructure.Graph.Strategy.Spine.exitFiveFreeKeys, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr member)))))

/-- **The proper arm carries `lem:proper-smearing`'s replacement and Core's
closure entry.** -/
theorem proper_arm_carries_replacement_and_closure
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .typeAExitSixProper ∈
        Hypostructure.Graph.Strategy.Spine.exitSixProperKeys known ∧
      closed (BranchState := BranchState) (presentation := presentation)
          (data := data) ∈
        Hypostructure.Graph.Strategy.Spine.exitSixProperKeys known := by
  constructor <;>
    simp [Hypostructure.Graph.Strategy.Spine.exitSixProperKeys]

/-- **The closure is read off the two committed statements.**

The selection says the object avoids the target and every strictly smaller
baseline object realizes it; the proper arm says the enlarging support is a
replacement of a proper boundaried support.  `lem:replacement` and
`cor:uncompressible` make the two incompatible, and neither row mentions the
other. -/
theorem proper_contradicts_selection
    (input : Input BranchState Presentation presentation data)
    (selection : (K (data := data) .selection).At input)
    (proper : (K (data := data) .typeAExitSixProper).At input) :
    False :=
  Incompatible.contradiction (Residual :=
    Input BranchState Presentation presentation data) input selection proper

/-- **The canonical dispatcher returns `closed` on the proper arm.** -/
theorem proper_arm_dispatches_closed
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected properKeys)
    (tasks : List (RoutedTask
      (Input BranchState Presentation presentation data))) :
    RoutedTask.dispatchFor history tasks = .closed := by
  rfl

/-- **The proper arm's audit accounts for every fact of the branch.** -/
theorem proper_arm_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected properKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice on the proper arm.** -/
theorem proper_arm_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected properKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **No empty commit occurs on the proper arm.** -/
theorem proper_arm_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected properKeys) :
    List.Forall (fun record => record.produced ≠ [])
      (ExactLedger.audit history).commits :=
  ExactLedger.audit_commits_nonempty history

/-! ## The global arm: `lem:no-silent-global-smearing` -/

/-- **No history is lost on the global arm.** -/
theorem global_arm_retains_every_incoming_fact
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (key : FactKey (Input BranchState Presentation presentation data))
    (member : key ∈ known) :
    key ∈ Hypostructure.Graph.Strategy.Spine.exitSixGlobalKeys known := by
  simp only [Hypostructure.Graph.Strategy.Spine.exitSixGlobalKeys,
    Hypostructure.Graph.Strategy.Spine.exitFiveFreeKeys, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr member)))))

/-- **The global arm carries `lem:no-silent-global-smearing`'s smaller closed
representative and Core's closure entry.** -/
theorem global_arm_carries_representative_and_closure
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .typeAExitSixGlobal ∈
        Hypostructure.Graph.Strategy.Spine.exitSixGlobalKeys known ∧
      closed (BranchState := BranchState) (presentation := presentation)
          (data := data) ∈
        Hypostructure.Graph.Strategy.Spine.exitSixGlobalKeys known := by
  constructor <;>
    simp [Hypostructure.Graph.Strategy.Spine.exitSixGlobalKeys]

/-- **The closure is read off the two committed statements.**

The global arm says the whole-graph dependence supplies a strictly smaller
admissible closed representative; the selection says every such object realizes
the target and that the selected object does not. -/
theorem global_contradicts_selection
    (input : Input BranchState Presentation presentation data)
    (selection : (K (data := data) .selection).At input)
    (global : (K (data := data) .typeAExitSixGlobal).At input) :
    False :=
  Incompatible.contradiction (Residual :=
    Input BranchState Presentation presentation data) input selection global

/-- **The canonical dispatcher returns `closed` on the global arm.** -/
theorem global_arm_dispatches_closed
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected globalKeys)
    (tasks : List (RoutedTask
      (Input BranchState Presentation presentation data))) :
    RoutedTask.dispatchFor history tasks = .closed := by
  rfl

/-- **The global arm's audit accounts for every fact of the branch.** -/
theorem global_arm_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected globalKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice on the global arm.** -/
theorem global_arm_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected globalKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **No empty commit occurs on the global arm.** -/
theorem global_arm_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected globalKeys) :
    List.Forall (fun record => record.produced ≠ [])
      (ExactLedger.audit history).commits :=
  ExactLedger.audit_commits_nonempty history

/-! ## The no arm: (R2) for exit `(6)` -/

/-- **The no arm carries the exit-`(6)` absence clause.**

This is one of the four facts node `[109]`'s placement is entered behind, in the
same shape as the exit-`(4)` and exit-`(5)` absences beside it. -/
theorem free_arm_carries_exit_six_absence
    {known : FactKeys (Input BranchState Presentation presentation data)} :
    K (data := data) .typeAExitSixFree ∈
      Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys known := by
  simp [Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys]

/-- **The no arm is not a terminal.**

Exit `(6)` closes only when it occurs; its absence continues the branch, which
is why the route-8 arm exists at all. -/
theorem free_arm_is_not_closed
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (fresh : closed (BranchState := BranchState) (presentation := presentation)
      (data := data) ∉ known) :
    closed (BranchState := BranchState) (presentation := presentation)
        (data := data) ∉
      Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys known := by
  simp [Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys,
    Hypostructure.Graph.Strategy.Spine.exitFiveFreeKeys, fresh]

/-- **The no arm keeps the whole incoming branch too.** -/
theorem free_arm_retains_every_incoming_fact
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (key : FactKey (Input BranchState Presentation presentation data))
    (member : key ∈ known) :
    key ∈ Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys known := by
  simp only [Hypostructure.Graph.Strategy.Spine.exitSixFreeKeys,
    Hypostructure.Graph.Strategy.Spine.exitFiveFreeKeys, List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr member)))

end Hypostructure.Fixtures.Route8ExitSix
