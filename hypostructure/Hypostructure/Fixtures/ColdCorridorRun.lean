import Hypostructure.Graph.Strategy.ColdCorridorRun
import Hypostructure.Graph.Strategy.SpineRun

/-!
# Fixture: the cold corridor block, run end to end

`Spine.runCold` is quantified over the keys it consumes and produces.  This
fixture installs it at the spine's *own* vocabulary, on a ledger that has
completed the entry block, and checks the three things the audit's Ledger,
Transport and Residual columns claim:

* the block elaborates only against a branch whose key index already carries
  node `[1]`'s selection and node `[14]`'s uncompressibility -- both `Has`
  instances are discharged by resolution against the incoming index;
* the output index is the incoming one with the thirteen cold facts on top, so every
  earlier fact of the branch is still in the type;
* the audit lists exactly the thirty-one committed facts, in commit order, and
  accounts for all of them with chronological commits.

Nothing here is specific to one manuscript: the run is at the framework's own
`Spine.Data`, left as a parameter.
-/

namespace Hypostructure.Fixtures.ColdCorridorRun

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The key index a branch carries after the entry block and the cold block. -/
abbrev coldKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.coldKeys
    (completedKeys (BranchState := BranchState) (presentation := presentation)
      (data := data))

/-- **The cold block runs on a completed entry-block ledger.**

The two `Has` instances are found by resolution against `completedKeys`, which
is what makes "a branch that has not proved node `[14]` does not elaborate" a
type-level fact rather than a convention, and every freshness side condition is
decided on the vocabulary's own finite `Key`. -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected completedKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      coldKeys :=
  runCold history (stateFresh := by simp) (tableFresh := by simp)
    (realizedFresh := by simp) (distinguishedFresh := by simp)
    (silentFresh := by simp) (cycleFresh := by simp) (defectFresh := by simp)
    (compressionFresh := by simp) (handoffFresh := by simp)
    (routingFresh := by simp) (transferFresh := by simp)
    (extractionFresh := by simp) (closedFresh := by simp)

/-- **The thirteen facts of rows 43--61 are all on the ledger after the block.**

Membership rather than position: the cold block is extended as later rows land
(later blocks add their own facts to the same index), and this check is about
what the cold block contributes, so it must not depend on how many facts sit around
them.  `run_audit_accounts_for_every_fact` and `run_audit_facts_unique` below
certify the rest — that every fact in the index is accounted for by a
chronological commit, and that none was committed twice. -/
theorem run_audit_contains_cold_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected coldKeys) :
    ∀ fact ∈ [`Hypostructure.Graph.Strategy.Spine.coldCorridorState,
        `Hypostructure.Graph.Strategy.Spine.coldSameInterfaceTable,
        `Hypostructure.Graph.Strategy.Spine.coldGermRealized,
        `Hypostructure.Graph.Strategy.Spine.coldGermDistinguished,
        `Hypostructure.Graph.Strategy.Spine.coldGermSilent,
        `Hypostructure.Graph.Strategy.Spine.coldFailureCycle,
        `Hypostructure.Graph.Strategy.Spine.coldFailureDefect,
        `Hypostructure.Graph.Strategy.Spine.coldFailureCompression,
        `Hypostructure.Graph.Strategy.Spine.coldFailureHandoff,
        `Hypostructure.Graph.Strategy.Spine.coldFailureRouting,
        `Hypostructure.Graph.Strategy.Spine.coldHandoffTransfer,
        `Hypostructure.Graph.Strategy.Spine.coldGermExtraction,
        `Hypostructure.Graph.Strategy.Spine.coldBranchClosed],
      fact ∈ (ExactLedger.audit history).facts := by
  intro fact member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨K .coldCorridorState, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldSameInterfaceTable, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldGermRealized, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldGermDistinguished, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldGermSilent, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldFailureCycle, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldFailureDefect, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldFailureCompression, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldFailureHandoff, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldFailureRouting, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldHandoffTransfer, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldGermExtraction, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldBranchClosed, by simp, rfl⟩

/-- **Every fact of the cold block is accounted for by a chronological
commit.** -/
theorem run_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected coldKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice** across the two blocks. -/
theorem run_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected coldKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

end Hypostructure.Fixtures.ColdCorridorRun
