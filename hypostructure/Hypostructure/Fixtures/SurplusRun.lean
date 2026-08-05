import Hypostructure.Graph.Strategy.SurplusRun

/-!
# Fixture: the sparse surplus activation block, run end to end

`Spine.runSparseActivation` is quantified over the keys it consumes and
produces.  This fixture installs it at the spine's *own* vocabulary, on the
literal exit ledger of node `[19]`'s above arm that `Spine.run` already
reaches, and checks the three things the audit's Ledger, Transport and Residual
columns claim:

* the block elaborates against that branch cursor, with both prerequisites --
  the node-`[1]`--`[4]` selection entry and node `[10]`'s slack independence --
  discharged by resolution against the incoming index;
* the output index is the incoming one with the four activation facts on top,
  so every earlier fact of the branch is still in the type;
* the audit accounts for every fact with chronological commits and no semantic
  fact was committed twice.

Nothing here is specific to one manuscript: the run is at the framework's own
`Spine.Data`, left as a parameter.
-/

namespace Hypostructure.Fixtures.SurplusRun

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The key index the branch carries after the block, over node `[19]`'s above
arm. -/
abbrev activatedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.sparseActivationKeys
    (surplusAboveKeys (BranchState := BranchState)
      (presentation := presentation) (data := data))

/-- **The block runs on the surplus-above residual of node `[19]`.** -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected surplusAboveKeys) :
    SurplusResult selected surplusAboveKeys :=
  runSurplusBranch history

/-- **The four facts of the block are all on the ledger after it runs.**

Membership rather than position: later blocks add their own facts to the same
index, and this check is about what the activation block contributes. -/
theorem run_audit_contains_activation_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    ∀ fact ∈ [`Hypostructure.Graph.Strategy.Spine.sparseSlackSurplus,
        `Hypostructure.Graph.Strategy.Spine.activeSurplusFamily,
        `Hypostructure.Graph.Strategy.Spine.sparsePortActivation,
        `Hypostructure.Graph.Strategy.Spine.baselineSpineDemand],
      fact ∈ (ExactLedger.audit history).facts := by
  intro fact member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨K .sparseSlackSurplus, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .activeSurplusFamily, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .sparsePortActivation, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .baselineSpineDemand, by simp, rfl⟩

/-- **Every fact of the block is accounted for by a chronological commit.** -/
theorem run_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice.** -/
theorem run_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-- **No commit is empty.** -/
theorem run_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected activatedKeys) :
    ((ExactLedger.audit history).commits.Forall
      fun record => record.produced ≠ []) :=
  ExactLedger.audit_commits_nonempty history

end Hypostructure.Fixtures.SurplusRun
