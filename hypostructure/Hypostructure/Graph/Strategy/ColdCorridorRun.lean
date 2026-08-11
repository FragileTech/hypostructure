import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.SpineAssembly

/-!
# The cold return corridor, ledger prefix

The rows of `ColdCorridorRows` publish concrete `Spine.Key` facts.  This module
appends them in the manuscript's order to the one canonical `ExactLedger`,
from the cut-state of `def:cold-corridor-first-failure` through the three arms
of `lem:cold-bounded-germ-trichotomy` and the local cold-oval closure fact.

The block is entered only from a branch cursor whose key index already carries
the surviving cold prefix: the selected counterexample, uncompressibility,
node `[22]`'s hot/cold split, the density facts, the large-budget residual, the
live negative-support path, the near-cubic spine estimate, and the Type
B/route-8 closures.  The prefix does not reconstruct those facts or store a side object;
it requires them in `known`, so the same full residual ancestry is retained
while the cold facts are appended.

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

noncomputable instance instIncompatibleColdTerminalResidualClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldTerminalResidual) (K .coldBranchClosed) where
  contradiction := fun _input terminal closed =>
    closed.down terminal.down

/-! ## The ledger prefix, run -/

/-- The key index the ledger carries after the cold corridor block closes. -/
abbrev coldKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .coldBranchClosed :: K .coldGermRouted ::
    K .coldGermExtraction ::
    K .coldHandoffTransfer :: K .coldExchangeBound :: K .coldFailureRouting ::
    K .coldAmbientCubicStubExcess ::
    K .coldSelectedBranchExcess ::
    K .coldFailureHandoff :: K .coldFailureCompression ::
    K .coldFailureDefect :: K .coldFailureCycle :: K .coldGermSilent ::
    K .coldGermDistinguished :: K .coldGermRealized ::
    K .coldSameInterfaceTable :: K .coldCorridorState :: known

/-- The key index after the cold rows have proved the no-terminal fact, before
the framework-owned closure entry is appended. -/
abbrev coldBranchClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .coldBranchClosed :: K .coldGermRouted ::
    K .coldGermExtraction ::
    K .coldHandoffTransfer :: K .coldExchangeBound :: K .coldFailureRouting ::
    K .coldAmbientCubicStubExcess ::
    K .coldSelectedBranchExcess ::
    K .coldFailureHandoff :: K .coldFailureCompression ::
    K .coldFailureDefect :: K .coldFailureCycle :: K .coldGermSilent ::
    K .coldGermDistinguished :: K .coldGermRealized ::
    K .coldSameInterfaceTable :: K .coldCorridorState :: known

/-- **The cold corridor ledger prefix, run.**

The cold rows are composed by `AtomicCT.run`, which appends each row's declared
productions to the incoming index while retaining the literal ancestry.  The
output index is the incoming one with the cold facts on top, so every earlier
ledger fact remains readable and no cold fact can be read by a branch that did
not run this prefix. -/
noncomputable def runColdBranchClosed
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .hotColdPartition) known]
    [FactKeys.Has (K (data := data) .maximalPacking) known]
    [FactKeys.Has (K (data := data) .densityCap) known]
    [FactKeys.Has (K (data := data) .sparseSurplusSurvivor) known]
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
    (selectedExcessFresh : K (data := data) .coldSelectedBranchExcess ∉ known)
    (ambientStubFresh : K (data := data) .coldAmbientCubicStubExcess ∉ known)
    (transferFresh : K (data := data) .coldHandoffTransfer ∉ known)
    (extractionFresh : K (data := data) .coldGermExtraction ∉ known)
    (routedFresh : K (data := data) .coldGermRouted ∉ known)
    (branchClosedFresh : K (data := data) .coldBranchClosed ∉ known) :
    ExactLedger (Input BranchState Presentation presentation data) current
      (coldBranchClosedKeys known) := by
  classical
  have afterState :=
    (coldCorridorStateRow (data := data)).run history (by simpa using stateFresh)
  have afterTable :=
    (sameInterfaceTableRow (data := data)).run afterState (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [tableFresh])
  -- The three arms of `lem:cold-bounded-germ-trichotomy`, in the manuscript's
  -- own order G1, G2, G3.
  have afterRealized :=
    (coldGermRealizedRow (data := data)).run afterTable (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [realizedFresh])
  have afterDistinguished :=
    (coldGermDistinguishedRow (data := data)).run afterRealized (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [distinguishedFresh])
  have afterSilent :=
    (coldGermSilentRow (data := data)).run afterDistinguished (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [silentFresh])
  have afterCycle :=
    (coldFailureCycleRow (data := data)).run afterSilent (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [cycleFresh])
  have afterDefect :=
    (coldFailureDefectRow (data := data)).run afterCycle (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [defectFresh])
  have afterCompression :=
    (coldFailureCompressionRow (data := data)).run afterDefect (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [compressionFresh])
  have afterHandoff :=
    (coldFailureHandoffRow (data := data)).run afterCompression (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [handoffFresh])
  have afterSelectedExcess :=
    (coldSelectedBranchExcessRow (data := data)).run afterHandoff (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [selectedExcessFresh])
  have afterAmbientStub :=
    (coldAmbientCubicStubExcessRow (data := data)).run afterSelectedExcess (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [ambientStubFresh])
  have afterRouting :=
    (coldFailureRoutingRow (data := data)).run afterAmbientStub (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [routingFresh])
  have afterExchange :=
    (coldExchangeBoundRow (data := data)).run afterRouting (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [exchangeFresh])
  -- Rows 57--61: the (F4) transfer, the (F5) extraction, and the remaining
  -- cold-germ routing fact.
  have afterTransfer :=
    (coldHandoffTransferRow (data := data)).run afterExchange (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [transferFresh])
  have afterExtraction :=
    (coldGermExtractionRow (data := data)).run afterTransfer (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [extractionFresh])
  have afterRouted :=
    (coldGermRoutedRow (data := data)).run afterExtraction (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [routedFresh])
  have afterBranchClosed :=
    (coldBranchClosedRow (data := data)).run afterRouted (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [branchClosedFresh])
  exact afterBranchClosed

/-- **The cold corridor ledger prefix, run and closed at the terminal oval.**

After the cold rows append `K .coldBranchClosed`, the framework-owned closure
entry is appended only when the incoming branch also carries the ordinary
positive terminal-residual fact `K .coldTerminalResidual`. -/
noncomputable def runCold
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .hotColdPartition) known]
    [FactKeys.Has (K (data := data) .maximalPacking) known]
    [FactKeys.Has (K (data := data) .densityCap) known]
    [FactKeys.Has (K (data := data) .sparseSurplusSurvivor) known]
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
    ExactLedger (Input BranchState Presentation presentation data) current
      (coldKeys known) := by
  classical
  have afterBranchClosed :=
    runColdBranchClosed (data := data) history
      stateFresh tableFresh realizedFresh distinguishedFresh silentFresh
      cycleFresh defectFresh compressionFresh handoffFresh routingFresh
      exchangeFresh selectedExcessFresh
      ambientStubFresh transferFresh extractionFresh routedFresh
      branchClosedFresh
  exact closeIncompatible afterBranchClosed (K .coldTerminalResidual)
    (K .coldBranchClosed) (by
      simpa using closureFresh)

end Hypostructure.Graph.Strategy.Spine
