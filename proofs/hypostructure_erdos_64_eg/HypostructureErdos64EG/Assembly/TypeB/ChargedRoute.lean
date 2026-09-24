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
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by
      simp [K_eq_iff])
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (extractedFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by simp [K_eq_iff])
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by simp [K_eq_iff])
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by simp [K_eq_iff])
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by simp [K_eq_iff])
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by simp [K_eq_iff])
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by simp [K_eq_iff])
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff])
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
   :
    SelectedRouteEightBoundary selected := by
  letI := cubicFresh
  let _cubicBaseline := (history.get (K .cubicBaseline)).down
  let cubic := history
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, routingFresh])
  exact selectedTypeBRoute8Continuation routed
    (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
    (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
    (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
    (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
    (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
    (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
    (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
    (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
    (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
    (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
    (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
    (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
    (extractedCensusFresh := by simp [K_eq_iff, extractedFresh])
    (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
    (peelingFresh := by simp [K_eq_iff, peelingFresh])
    (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
    (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
    (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
    (openBoundarySaturatedFresh := by simp [K_eq_iff, openBoundarySaturatedFresh])
    (demandUnitCountFresh := by simp [K_eq_iff, demandUnitCountFresh])
    (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
    (windowShadowSignatureFresh := by simp [K_eq_iff, windowShadowSignatureFresh])
    (windowShadowTailFresh := by simp [K_eq_iff, windowShadowTailFresh])
    (windowShadowCycleFresh := by simp [K_eq_iff, windowShadowCycleFresh])
    (windowShadowExcludedFresh := by simp [K_eq_iff, windowShadowExcludedFresh])
    (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
    (unpaidExitFourFresh := by simp [K_eq_iff, unpaidExitFourFresh])
    (unifiedVisibleFresh := by simp [K_eq_iff, unifiedVisibleFresh])
    (unifiedVisibleOverloadFresh := by
      simp [K_eq_iff, unifiedVisibleOverloadFresh])
    (jointBalanceFresh := by simp [K_eq_iff, jointBalanceFresh])
    (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])

end HypostructureErdos64EG
