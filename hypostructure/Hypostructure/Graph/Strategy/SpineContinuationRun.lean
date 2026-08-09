import Hypostructure.Graph.Strategy.ColdCorridorRun
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Graph.Strategy.SurplusRun

/-!
# Spine continuation surface

Continuation transport is owned by the framework ledger/router.  This module is
the stable import surface for end-to-end composition over the existing rows; it
declares no custom continuation or result carrier.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Close the cold terminal oval by running the existing cold corridor rows on
the same incoming ledger and eliminating Core's closure key. -/
noncomputable def closeColdTerminalBranch
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .windowPackageCollided) known]
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
    (transferFresh : K (data := data) .coldHandoffTransfer ∉ known)
    (extractionFresh : K (data := data) .coldGermExtraction ∉ known)
    (routedFresh : K (data := data) .coldGermRouted ∉ known)
    (branchClosedFresh : K (data := data) .coldBranchClosed ∉ known)
    (closureFresh :
      closed (BranchState := BranchState) (Presentation := Presentation)
        (presentation := presentation) (data := data) ∉
        K .coldBranchClosed :: K .coldGermRouted ::
          K .coldGermExtraction :: K .coldHandoffTransfer ::
          K .coldFailureRouting :: K .coldFailureHandoff ::
          K .coldFailureCompression :: K .coldFailureDefect ::
          K .coldFailureCycle :: K .coldGermSilent ::
          K .coldGermDistinguished :: K .coldGermRealized ::
          K .coldSameInterfaceTable :: K .coldCorridorState :: known) :
    False := by
  classical
  have closedHistory :=
    runCold (data := data) history
      stateFresh tableFresh realizedFresh distinguishedFresh silentFresh
      cycleFresh defectFresh compressionFresh handoffFresh routingFresh
      transferFresh extractionFresh routedFresh branchClosedFresh closureFresh
  let present :
      FactKeys.Has
        (closed (BranchState := BranchState) (Presentation := Presentation)
          (presentation := presentation) (data := data))
        (coldKeys known) := by
    dsimp [coldKeys]
    infer_instance
  exact ExactLedger.elimClosed closedHistory present

end Hypostructure.Graph.Strategy.Spine
