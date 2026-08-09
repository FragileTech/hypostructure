import Hypostructure.Graph.Strategy.ColdCorridorRun

/-!
# Fixture: the cold corridor ledger prefix

`Spine.runCold` is quantified over the keys it consumes and produces.  This
fixture checks the audit shape of a ledger that already carries the cold
corridor prefix at the spine's *own* vocabulary:

* the index is the incoming one with the fourteen cold facts on top, so every
  earlier fact of the branch is still in the type;
* the audit contains those fourteen facts and accounts for every fact with a
  chronological commit.

This fixture audits the prefix at an arbitrary incoming live cold residual.
Row 61 is audited here as the ordinary ledger fact `coldBranchClosed` on that
same residual.
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

/-- The key index a branch carries after appending the cold corridor prefix. -/
abbrev coldKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  Hypostructure.Graph.Strategy.Spine.coldKeys known

/-- **The fourteen facts of rows 43--61 are all on the ledger after the prefix.**

Membership rather than position: later rows may extend this same ledger, and
this check is about what the cold prefix contributes, so it must not depend on
how many facts sit around them.  `run_audit_accounts_for_every_fact` and
`run_audit_facts_unique` below certify the rest: every fact in the index is
accounted for by a chronological commit, and none was committed twice. -/
theorem run_audit_contains_cold_facts
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (coldKeys known)) :
    ∀ fact ∈ [(name .coldCorridorState),
        (name .coldSameInterfaceTable),
        (name .coldGermRealized),
        (name .coldGermDistinguished),
        (name .coldGermSilent),
        (name .coldFailureCycle),
        (name .coldFailureDefect),
        (name .coldFailureCompression),
        (name .coldFailureHandoff),
        (name .coldFailureRouting),
        (name .coldHandoffTransfer),
        (name .coldGermExtraction),
        (name .coldGermRouted),
        (name .coldBranchClosed)],
      fact ∈ (ExactLedger.audit history).facts := by
  intro fact member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
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
  · exact List.mem_map.mpr ⟨K .coldGermRouted, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldBranchClosed, by simp, rfl⟩

/-- **Every fact of the cold block is accounted for by a chronological
commit.** -/
theorem run_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (coldKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **No semantic fact was committed twice** across the two blocks. -/
theorem run_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (coldKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

end Hypostructure.Fixtures.ColdCorridorRun
