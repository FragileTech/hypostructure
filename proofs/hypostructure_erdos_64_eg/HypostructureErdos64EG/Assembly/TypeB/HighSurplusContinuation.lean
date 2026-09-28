import Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting
import Hypostructure.Graph.Strategy.SpineRows.TypeBAssignedSupport
import HypostructureErdos64EG.Assembly.TypeB.Continuation
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGermFanEnvelope

/-!
# Assembly: TypeB / HighSurplusContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **Node `[64]`: the ordinary Type B entry**, on the `[62]` yes-residual of any
arm.  The object-wide receiver routing of `[88]`, read by the common Part IX
census, is published on this literal residual; `[65]`
(`typeBAssignedSupportRow`, `def:canonical-decomp`) publishes the ordinary
assigned support, and the common continuation runs `[67]`--`[85]`.

`arm` names the prefix and entropy arm; the Type B high-surplus lane block is
added before the Type B chain. -/
-- EG-NODE [65] Type B assigned support: high-degree fan centers and decorated handoff data
noncomputable def selectedTypeBHighSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : NetChargeArms selected)
    [FactKeys.Has (K .netChargeNegative) known]
    [FactKeys.Has (K .typeBHighSurplus) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .bridgeless) known]
    (cubicFresh : FactKeys.Has (K .cubicBaseline) known := by infer_instance)
    (assignedFresh : K .typeBAssignedSupport ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (normalFormFresh : K .highCentreNormalForm ∉ known := by key_fresh)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by key_fresh)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by key_fresh)
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by key_fresh)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      key_fresh)
    (capFresh : K .fanCertificateCap ∉ known := by key_fresh)
    (markedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (residualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    -- `[72]`--`[85]` continue on this same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (route8EntryFresh : K .typeBRoute8Entry ∉ known := by key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
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
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by key_fresh)
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
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (degreeFourLedgerFresh : K .typeBDegreeFourLedger ∉ known := by key_fresh)
    (degreeFourOverlapFresh : K .typeBDegreeFourOverlap ∉ known := by key_fresh)
    (degreeFourClosedFresh : K .typeBDegreeFourClosed ∉ known := by key_fresh)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by key_fresh)
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by key_fresh)
    (triangularCoreFresh : K .triangularFanCore ∉ known := by key_fresh)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (route8BasinBurdenFresh_ : K .route8BasinBurden ∉ known := by key_fresh)
    (route8CarrierCoreFresh_ : K .route8CarrierCore ∉ known := by key_fresh)
    (typeBAbsorbedChargeFresh_ : K .typeBAbsorbedCharge ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
   :
    SelectedRouteEightBoundary selected := by
  letI := cubicFresh
  -- `[65]`: the ordinary Type B assigned support.
  let assigned := (typeBAssignedSupportRow (data := spineData)).run history
    (by key_fresh)
  -- `[65]`: the Type B entry read from the assigned support.
  let entry := (typeBAssignedEntryRow (data := spineData)).run assigned
    (by key_fresh)
  -- The absorbed Type B charge of `[177]` is a fact of G on this lane too.
  let charged := (typeBAbsorbedChargeRow (data := spineData)).run entry
    (by key_fresh)
  exact Assembly.Internal.selectedTypeBFanContinuation charged
    (arm.typeBHighSurplus (NetChargeLaneBlock_typeBHighSurplus.ret charged))

end HypostructureErdos64EG
