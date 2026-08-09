import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.SpineAssembly

/-!
# The cold return corridor, ledger prefix

The rows of `ColdCorridorRows` publish concrete `Spine.Key` facts.  This module
runs them in the manuscript's order against the one canonical `ExactLedger`,
from the cut-state of `def:cold-corridor-first-failure` through the three arms
of `lem:cold-bounded-germ-trichotomy` and the local cold-oval closure fact.

The block is entered only from a branch cursor whose key index already carries
the surviving cold prefix: the selected counterexample, uncompressibility, the
window package and density facts, the large-budget residual, the live
negative-support path, the near-cubic spine estimate, and the Type B/route-8
closures.  The runner does not reconstruct those facts or store a side object;
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

/-! ## The ledger prefix, run -/

/-- The key index the ledger carries after the cold corridor block. -/
abbrev coldKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .coldBranchClosed :: K .coldGermRouted :: K .coldGermExtraction ::
    K .coldHandoffTransfer :: K .coldFailureRouting :: K .coldFailureHandoff ::
    K .coldFailureCompression :: K .coldFailureDefect :: K .coldFailureCycle ::
    K .coldGermSilent :: K .coldGermDistinguished :: K .coldGermRealized ::
    K .coldSameInterfaceTable :: K .coldCorridorState :: known

/-- **The cold corridor ledger prefix, run.**

The cold rows are composed by `AtomicCT.run`, which appends each row's declared
productions to the incoming index while retaining the literal ancestry.  The
output index is the incoming one with the cold facts on top, so every earlier
ledger fact remains readable and no cold fact can be read by a branch that did
not run this prefix. -/
noncomputable def runCold
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .windowPackageSeparated) known]
    [FactKeys.Has (K (data := data) .densityCap) known]
    [FactKeys.Has (K (data := data) .largeBudgetResidual) known]
    [FactKeys.Has (K (data := data) .negativeSupport) known]
    [FactKeys.Has (K (data := data) .sparseSurplusSurvivor) known]
    [FactKeys.Has (K (data := data) .spineSurplusEstimate) known]
    [FactKeys.Has (K (data := data) .sparsePressureNearCubic) known]
    [FactKeys.Has (K (data := data) .typeBExcluded) known]
    [FactKeys.Has (K (data := data) .route8TerminalNoGo) known]
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
    (routedFresh : K (data := data) .coldGermRouted ∉ known)
    (closedFresh : K (data := data) .coldBranchClosed ∉ known) :
    ExactLedger (Input BranchState Presentation presentation data) current
      (coldKeys known) := by
  classical
  -- The cut-state first: it requires nothing, and the three later cold rows
  -- read it.
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
  have afterRouting :=
    (coldFailureRoutingRow (data := data)).run afterHandoff (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [routingFresh])
  -- Rows 57--61: the (F4) transfer, the (F5) extraction, and the remaining
  -- cold-germ routing fact.
  have afterTransfer :=
    (coldHandoffTransferRow (data := data)).run afterRouting (by
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
  exact (coldBranchClosedRow (data := data)).run afterRouted (by
    intro key isNew isOld
    simp only [List.mem_singleton] at isNew
    subst isNew
    revert isOld
    simp [closedFresh])

end Hypostructure.Graph.Strategy.Spine
