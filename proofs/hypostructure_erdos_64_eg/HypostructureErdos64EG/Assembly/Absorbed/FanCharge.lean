import HypostructureErdos64EG.Assembly.TypeB.ChargedRoute
import HypostructureErdos64EG.Assembly.TypeB.Continuation

/-!
# Assembly: Absorbed / FanCharge

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The common charged tail of the absorbed case-(ii) family.  Its input is
the literal `[177]` ledger, possibly already carrying `[176]`'s closure for the
case-(i) subfamily.  Every Type-B alternative is consumed at its registered
owner and then converted by the common `[76]`/`[85]` quantitative tail.  Thus a
mixed absorbed family never discards the facts appended before this call. -/
noncomputable def Assembly.Internal.selectedAbsorbedFanChargeContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known)
    (localFresh : K .typeBFanLocalDichotomy ∉ known)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (triangularFresh : K .triangularFanCore ∉ known)
    (capFresh : K .fanCertificateCap ∉ known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known)
    (portReturnFresh : K .triangularPortReturn ∉ known)
    (firstLandingFresh : K .triangularFirstLanding ∉ known)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known)
    (fanSafeFresh : K .typeBFanSafe ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (extractedFresh : K .route8ExtractedEntryCensus ∉ known)
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
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
  let boundary := selectedTypeBContinuation history
    (by simp [K_eq_iff, normalFormFresh])
    (by simp [K_eq_iff, heavyFresh])
    (by simp [K_eq_iff, degreeFourFresh])
    (by simp [K_eq_iff, compatibilityFresh])
    (by simp [K_eq_iff, localFresh])
    (by simp [K_eq_iff, profileFresh])
    (by simp [K_eq_iff, triangularFresh])
    (by simp [K_eq_iff, capFresh])
    (by simp [K_eq_iff, markedFresh])
    (by simp [K_eq_iff, residualFresh])
    (by simp [K_eq_iff, certificateMassFresh])
    (by simp [K_eq_iff, cycleFresh])
    (by simp [K_eq_iff, freeFresh])
    (by simp [K_eq_iff, choiceFresh])
    (by simp [K_eq_iff, obstructionFresh])
    (by simp [K_eq_iff, hybridFresh])
    (by simp [K_eq_iff, ledgerFresh])
    (by simp [K_eq_iff, excludedFresh])
    (by simp [K_eq_iff, exclusionResidualFresh])
    (by simp [K_eq_iff, exclusionMassFresh])
    (by simp [K_eq_iff, obstructionMassFresh])
    (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
    (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
    (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
    (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
    (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
    (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
    (portReturnFresh := by simp [K_eq_iff, portReturnFresh])
    (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
    (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
    (fanSafeFresh := by simp [K_eq_iff, fanSafeFresh])
    (globalLocalBridgeFresh := by simp [K_eq_iff, globalLocalBridgeFresh])
  rcases boundary with (mass | paid | mass | mass) | (mass | paid | mass | mass)
  all_goals
    first
    | exact selectedTypeBChargedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by infer_instance)
        (by simp [K_eq_iff, routingFresh])
        (by simp [K_eq_iff, extractedFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
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
    | exact selectedTypeBChargedRoute8Continuation paid
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by infer_instance)
        (by simp [K_eq_iff, routingFresh])
        (by simp [K_eq_iff, extractedFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
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
