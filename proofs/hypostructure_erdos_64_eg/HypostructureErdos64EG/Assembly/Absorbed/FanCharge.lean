import Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting
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

/-- The `[177]` → `[65]` entry of the absorbed case-(ii) family.  The literal
`[177]` ledger, possibly already carrying `[176]`'s closure for the case-(i)
subfamily, receives the object-wide receiver routing of `[88]` read by the
common Part IX census, and the common continuation runs `[67]`--`[85]` on it. -/
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
    (degreeFourLedgerFresh : K .typeBDegreeFourLedger ∉ known)
    (degreeFourOverlapFresh : K .typeBDegreeFourOverlap ∉ known)
    (degreeFourClosedFresh : K .typeBDegreeFourClosed ∉ known)
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
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (extractedFresh : K .route8ExtractedEntryCensus ∉ known)
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
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by key_fresh)
    (demandResidualFresh : K .route8StageRate ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known := by key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
   :
    SelectedRouteEightBoundary selected := by
  letI := cubicFresh
  exact Assembly.Internal.selectedTypeBFanContinuation history

end HypostructureErdos64EG
