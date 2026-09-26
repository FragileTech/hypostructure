import Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting
import HypostructureErdos64EG.Assembly.RouteEight.TypeBContinuation

/-!
# Assembly: TypeB / ChargedRoute

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- `[76]`/`[85]` → `[77]` → Part IX on an already charged Type-B boundary.
The two facts needed by the common route-8 continuation are proved on this
literal ledger, after which the registered `[75]`--`[77]` owners and `[123]`
consume the charged residual without projecting away its ancestry. -/
noncomputable def selectedTypeBChargedRoute8Continuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by
      key_fresh)
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (routingFresh : K .typeAReceiverRouting ∉ known := by key_fresh)
    (extractedFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by key_fresh)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by key_fresh)
   :
    SelectedRouteEightBoundary selected := by
  letI := cubicFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  let cubic := history
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by key_fresh)
  exact selectedTypeBRoute8Continuation routed
    (bridgeMassFresh := by key_fresh)
    (bridgeSublinearFresh := by key_fresh)
    (unifiedNegativeFresh := by key_fresh)
    (typeAExclusionFresh := by key_fresh)
    (typeBBridgeReductionFresh := by key_fresh)
    (piecesClassifiedFresh := by key_fresh)
    (sublinearLedgerFresh := by key_fresh)
    (sublinearResidualFresh := by key_fresh)
    (unifiedDeficitFresh := by key_fresh)
    (quotientFreeFresh := by key_fresh)
    (quotientResidualFresh := by key_fresh)
    (unifiedCensusFresh := by key_fresh)
    (extractedCensusFresh := by key_fresh)
    (unifiedTrueFresh := by key_fresh)
    (peelingFresh := by key_fresh)
    (stageFailedFresh := by key_fresh)
    (demandLedgerFresh := by key_fresh)
    (demandAbsorptionFresh := by key_fresh)
    (openBoundarySaturatedFresh := by key_fresh)
    (demandUnitCountFresh := by key_fresh)
    (windowBlockersFresh := by key_fresh)
    (windowShadowSignatureFresh := by key_fresh)
    (windowShadowTailFresh := by key_fresh)
    (windowShadowCycleFresh := by key_fresh)
    (windowShadowExcludedFresh := by key_fresh)
    (demandResidualFresh := by key_fresh)
    (unpaidExitFourFresh := by key_fresh)
    (unifiedVisibleFresh := by key_fresh)
    (unifiedVisibleOverloadFresh := by
      key_fresh)
    (jointBalanceFresh := by key_fresh)
    (unifiedTerminalFresh := by key_fresh)

end HypostructureErdos64EG
