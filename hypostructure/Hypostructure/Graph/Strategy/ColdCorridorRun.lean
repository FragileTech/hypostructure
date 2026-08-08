import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.SpineAssembly

/-!
# The cold return corridor, ledger prefix

The rows of `ColdCorridorRows` are each quantified over the keys they consume
and produce.  This module installs them all at the spine's own vocabulary and
runs them in the manuscript's order against the one canonical `ExactLedger`,
from the cut-state of `def:cold-corridor-first-failure` through the three arms
of `lem:cold-bounded-germ-trichotomy` and the remaining cold-germ routing fact.
It does not append the framework closure key: oval closure is a later Core
closure from ordinary facts already visible on the same ledger.

The block is entered from any branch cursor whose key index already carries the
selection of node `[1]` and the uncompressibility of node `[14]`.  Those are the
only two facts the manuscript's proofs spend here: (F1) and the trichotomy's G1
are closed by the selection's target avoidance, (F3) and the trichotomy's G3 by
node `[14]`, while the cut-state, (F2), (F4), the trichotomy's G2 and the
existence dichotomy are theorems about the corridor, the germ and the registered
declared signature and read nothing.

Every prerequisite is discharged from the incoming index and every row body
reads its requirements with `FactInputs.get`.  Nothing is carried between the
rows but the residual and the ledger.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The rows, at the spine's own keys

Every schema bridge below is the identity on `PLift`: the spine's value at a
cold key *is* the manuscript statement, so nothing is re-encoded. -/

/-- Nodes `[145]`--`[157]`, the corridor cut-state `T(J)`. -/
@[reducible] noncomputable def coldCorridorState :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldCorridorStateRow (K .coldCorridorState) (fun _input value => ⟨value⟩)

/-- Nodes `[145]`--`[157]`, the same-interface table. -/
@[reducible] noncomputable def coldSameInterfaceTable :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sameInterfaceTableRow (K .selection) (K .uncompressible)
    (K .coldSameInterfaceTable) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[155]`: G1 of `lem:cold-bounded-germ-trichotomy`. -/
@[reducible] noncomputable def coldGermRealized :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldGermRealizedRow (K .selection) (K .coldGermRealized) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[156]`: G2 of `lem:cold-bounded-germ-trichotomy`. -/
@[reducible] noncomputable def coldGermDistinguished :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldGermDistinguishedRow (K .coldGermDistinguished)
    (fun _input value => ⟨value⟩)

/-- Node `[157]`: G3 of `lem:cold-bounded-germ-trichotomy`, with
`lem:cold-increment-arithmetic`. -/
@[reducible] noncomputable def coldGermSilent :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldGermSilentRow (K .uncompressible) (K .coldGermSilent) (by simp)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[154]`, `[155]`: the (F1) producer. -/
@[reducible] noncomputable def coldFailureCycle :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldFailureCycleRow (K .selection) (K .coldFailureCycle) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[154]`, `[156]`: the (F2) producer. -/
@[reducible] noncomputable def coldFailureDefect :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldFailureDefectRow (K .coldCorridorState) (K .coldFailureDefect) (by simp)
    (fun _input value => ⟨value⟩)

/-- Node `[154]`, `[157]`: the (F3) producer. -/
@[reducible] noncomputable def coldFailureCompression :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldFailureCompressionRow (K .uncompressible) (K .coldFailureCompression)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[154]`, `[156]`: the (F4) producer and its handoff exit. -/
@[reducible] noncomputable def coldFailureHandoff :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldFailureHandoffRow (K .coldCorridorState) (K .coldFailureHandoff) (by simp)
    (fun _input value => ⟨value⟩)

/-- Node `[154]`: the classified state. -/
@[reducible] noncomputable def coldFailureRouting :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldFailureRoutingRow (K .coldCorridorState) (K .coldFailureRouting) (by simp)
    (fun _input value => ⟨value⟩)

/-- Node `[156]`: the (F4) dispatch arm, as a transfer. -/
@[reducible] noncomputable def coldHandoffTransfer :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldHandoffTransferRow (K .coldFailureHandoff) (K .coldHandoffTransfer)
    (by simp) (fun _input value => ⟨value⟩)

/-- Nodes `[153]`, `[154]`: the (F5) arm's extraction. -/
@[reducible] noncomputable def coldGermExtraction :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldGermExtractionRow (K .coldFailureRouting) (K .coldGermExtraction)
    (by simp) (fun _input value => ⟨value⟩)

/-- Nodes `[145]`--`[157]`: `thm:cold-branch-quantitative-closure`. -/
@[reducible] noncomputable def coldGermRouted :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coldGermRoutedRow (K .coldGermRealized) (K .coldGermSilent)
    (K .coldGermRouted) (by simp)
    (fun _input fact => fact.down.1) (fun _input fact => fact.down.1)
    (fun _input value => ⟨value⟩)

/-! ## The ledger prefix, run -/

/-- The key index the ledger carries after the cold corridor block. -/
abbrev coldKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .coldGermRouted :: K .coldGermExtraction :: K .coldHandoffTransfer ::
    K .coldFailureRouting :: K .coldFailureHandoff :: K .coldFailureCompression ::
    K .coldFailureDefect :: K .coldFailureCycle :: K .coldGermSilent ::
    K .coldGermDistinguished :: K .coldGermRealized ::
    K .coldSameInterfaceTable :: K .coldCorridorState :: known

/-- **The cold corridor ledger prefix, run.**

The thirteen rows are composed by `AtomicCT.run`, which appends each row's declared
productions to the incoming index while retaining the literal ancestry.  The
output index is the incoming one with the cold facts on top, so every earlier
ledger fact remains readable and no cold fact can be read by a branch that did
not run this prefix. -/
noncomputable def runCold
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
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
    (transferFresh : K (data := data) .coldHandoffTransfer ∉ known)
    (extractionFresh : K (data := data) .coldGermExtraction ∉ known)
    (routedFresh : K (data := data) .coldGermRouted ∉ known) :
    ExactLedger (Input BranchState Presentation presentation data) current
      (coldKeys known) := by
  classical
  -- The cut-state first: it requires nothing, and the three later cold rows
  -- read it.
  have afterState :=
    (coldCorridorState (data := data)).run history (by simpa using stateFresh)
  have afterTable :=
    (coldSameInterfaceTable (data := data)).run afterState (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [tableFresh])
  -- The three arms of `lem:cold-bounded-germ-trichotomy`, in the manuscript's
  -- own order G1, G2, G3.
  have afterRealized :=
    (coldGermRealized (data := data)).run afterTable (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [realizedFresh])
  have afterDistinguished :=
    (coldGermDistinguished (data := data)).run afterRealized (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [distinguishedFresh])
  have afterSilent :=
    (coldGermSilent (data := data)).run afterDistinguished (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [silentFresh])
  have afterCycle :=
    (coldFailureCycle (data := data)).run afterSilent (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [cycleFresh])
  have afterDefect :=
    (coldFailureDefect (data := data)).run afterCycle (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [defectFresh])
  have afterCompression :=
    (coldFailureCompression (data := data)).run afterDefect (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [compressionFresh])
  have afterHandoff :=
    (coldFailureHandoff (data := data)).run afterCompression (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [handoffFresh])
  have afterRouting :=
    (coldFailureRouting (data := data)).run afterHandoff (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [routingFresh])
  -- Rows 57--61: the (F4) transfer, the (F5) extraction, and the remaining
  -- cold-germ routing fact.
  have afterTransfer :=
    (coldHandoffTransfer (data := data)).run afterRouting (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [transferFresh])
  have afterExtraction :=
    (coldGermExtraction (data := data)).run afterTransfer (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [extractionFresh])
  exact (coldGermRouted (data := data)).run afterExtraction (by
    intro key isNew isOld
    simp only [List.mem_singleton] at isNew
    subst isNew
    revert isOld
    simp [routedFresh])

end Hypostructure.Graph.Strategy.Spine
