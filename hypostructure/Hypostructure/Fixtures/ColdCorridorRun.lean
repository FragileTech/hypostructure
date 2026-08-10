import Hypostructure.Graph.Strategy.ColdCorridorRun

/-!
# Fixture: the cold corridor ledger prefix

This fixture checks the audit shape of a ledger that already carries the cold
corridor prefix at the spine's *own* vocabulary:

* the index is the incoming one with the cold facts on top, so every
  earlier fact of the branch is still in the type;
* the audit contains those facts and accounts for every fact with a
  chronological commit.

This fixture audits the prefix at an arbitrary incoming live cold residual.
Row 61 is audited here as the ordinary ledger fact `coldBranchClosed` followed
by Core's reserved closure fact on that same residual.
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

/-- **The facts of rows 43--61 are all on the ledger after the prefix.**

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
    ∀ fact ∈ [closureFactName,
        (name .coldCorridorState),
        (name .coldSameInterfaceTable),
        (name .coldGermRealized),
        (name .coldGermDistinguished),
        (name .coldGermSilent),
        (name .coldFailureCycle),
        (name .coldFailureDefect),
        (name .coldFailureCompression),
        (name .coldFailureHandoff),
        (name .coldFailureRouting),
        (name .coldExchangeBound),
        (name .coldHotFailureMass),
        (name .coldSelectedBranchExcess),
        (name .coldAmbientCubicStubExcess),
        (name .coldHandoffTransfer),
        (name .coldGermExtraction),
        (name .coldGermRouted),
        (name .coldBranchClosed)],
      fact ∈ (ExactLedger.audit history).facts := by
  intro fact member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨closed, by simp [coldKeys], rfl⟩
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
  · exact List.mem_map.mpr ⟨K .coldExchangeBound, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldHotFailureMass, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldSelectedBranchExcess, by simp, rfl⟩
  · exact List.mem_map.mpr ⟨K .coldAmbientCubicStubExcess, by simp, rfl⟩
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

/-- **The concrete cold prefix closes by the terminal/no-terminal
incompatibility.** -/
theorem runCold_closure_reason
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .coldWindowLedgerSplit) known]
    [FactKeys.Has (K (data := data) .maximalPacking) known]
    [FactKeys.Has (K (data := data) .densityCap) known]
    [FactKeys.Has (K (data := data) .largeBudgetResidual) known]
    [FactKeys.Has (K (data := data) .negativeSupport) known]
    [FactKeys.Has (K (data := data) .sparseSurplusSurvivor) known]
    [FactKeys.Has (K (data := data) .spineSurplusEstimate) known]
    [FactKeys.Has (K (data := data) .sparsePressureNearCubic) known]
    [FactKeys.Has (K (data := data) .typeBExcluded) known]
    [FactKeys.Has (K (data := data) .route8TerminalNoGo) known]
    [FactKeys.Has (K (data := data) .coldTerminalResidual) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (stateFresh : K (data := data) .coldCorridorState ∉ known)
    (tableFresh : K (data := data) .coldSameInterfaceTable ∉ known)
    (realizedFresh : K (data := data) .coldGermRealized ∉ known)
    (distinguishedFresh : K (data := data) .coldGermDistinguished ∉ known)
    (silentFresh : K (data := data) .coldGermSilent ∉ known)
    (cycleFresh : K (data := data) .coldFailureCycle ∉ known)
    (defectFresh : K (data := data) .coldFailureDefect ∉ known)
    (compressionFresh : K (data := data) .coldFailureCompression ∉ known)
    (handoffFresh : K (data := data) .coldFailureHandoff ∉ known)
    (routingFresh : K (data := data) .coldFailureRouting ∉ known)
    (exchangeFresh : K (data := data) .coldExchangeBound ∉ known)
    (hotMassFresh : K (data := data) .coldHotFailureMass ∉ known)
    (selectedExcessFresh : K (data := data) .coldSelectedBranchExcess ∉ known)
    (ambientStubFresh : K (data := data) .coldAmbientCubicStubExcess ∉ known)
    (transferFresh : K (data := data) .coldHandoffTransfer ∉ known)
    (extractionFresh : K (data := data) .coldGermExtraction ∉ known)
    (routedFresh : K (data := data) .coldGermRouted ∉ known)
    (branchClosedFresh : K (data := data) .coldBranchClosed ∉ known)
    (closureFresh :
      closed (BranchState := BranchState) (Presentation := Presentation)
        (presentation := presentation) (data := data) ∉
        coldBranchClosedKeys known) :
    (ExactLedger.get
      (Hypostructure.Graph.Strategy.Spine.runCold
        (data := data) history stateFresh tableFresh realizedFresh
        distinguishedFresh silentFresh cycleFresh defectFresh compressionFresh
        handoffFresh routingFresh exchangeFresh hotMassFresh
        selectedExcessFresh ambientStubFresh transferFresh extractionFresh
        routedFresh branchClosedFresh closureFresh)
      (closed : FactKey (Input BranchState Presentation presentation data))).down.reason =
      AutomaticClosureReason.incompatibleFacts
        (name .coldTerminalResidual) (name .coldBranchClosed) := by
  rfl

end Hypostructure.Fixtures.ColdCorridorRun
