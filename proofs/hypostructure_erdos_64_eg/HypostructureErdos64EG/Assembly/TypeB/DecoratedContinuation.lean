import HypostructureErdos64EG.Assembly.TypeB.Continuation
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGermFanEnvelope

/-!
# Assembly: TypeB / DecoratedContinuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **Type B `[67]`--`[85]` on the decorated envelope** (`def:decorated-fan-envelope`,
`def:typeB-assigned-ledger`), on the `[108]`/`[66]` → `[65]` decorated residual:
the common continuation runs on this literal ledger.

`arm` names the Type A lane arms; the decorated-handoff block is added before
the Type B chain. -/
noncomputable def selectedTypeBDecoratedContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : TypeAExitFourArms selected)
    [FactKeys.Has (K .typeAExitFiveFree) known]
    [FactKeys.Has (K .typeAExitSevenEnvelope) known]
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    [FactKeys.Has (K .typeAExitSixFree) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .typeBDecoratedAssignedSupport) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (route8EntryFresh : K .typeBRoute8Entry ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (foldPeelsFresh : K .route8FoldPeels ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known)
    (demandResidualFresh : K .route8StageRate ∉ known)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (entriesAtGFresh : K .route8QuotientEntriesAtG ∉ known := by key_fresh)
    (pieceWindowAttachmentFresh : K .route8PieceWindowAttachment ∉ known := by key_fresh)
    (pieceChainCycleFresh : K .route8PieceChainCycle ∉ known := by key_fresh)
    (piecewiseRateFresh : K .route8PiecewiseRate ∉ known := by key_fresh)
    (packingExchangeFresh : K .route8PackingExchange ∉ known := by key_fresh)
    (armExchangeFresh : K .route8ArmExchange ∉ known := by key_fresh)
    (fullArmLandingCapFresh : K .route8FullArmLandingCap ∉ known := by key_fresh)
    (hubPieceMassFresh : K .route8HubPieceMass ∉ known := by key_fresh)
    (netCapExcessFresh : K .route8NetCapExcess ∉ known := by key_fresh)
    (cleanLandingRulesFresh : K .route8CleanLandingRules ∉ known := by key_fresh)
    (cleanLandingCapFresh : K .route8CleanLandingCap ∉ known := by key_fresh)
    (armClosureResidualFresh : K .route8ArmClosureResidual ∉ known := by key_fresh)
    (typeBSublinearCanonicalFormFresh : K .typeBSublinearCanonicalForm ∉ known := by key_fresh)
    (groupedAbsorbedCoreSubsetFresh : K .groupedAbsorbedCoreSubset ∉ known := by key_fresh)
    (typeBSublinearFailureArmsFresh : K .typeBSublinearFailureArms ∉ known := by key_fresh)
    (groupedCentresHighFresh : K .groupedCentresHigh ∉ known := by key_fresh)
    (handoffDegreeClauseEmptyFresh : K .handoffDegreeClauseEmpty ∉ known := by key_fresh)
    (pieceRoutingTotalFresh : K .pieceRoutingTotal ∉ known := by key_fresh)
    (coverPaymentFresh : K .coverPayment ∉ known := by key_fresh)
    (loadFailureSaturatedFresh : K .loadFailureSaturated ∉ known := by key_fresh)
    (unpaidAbsorbedWindowPortFresh : K .unpaidAbsorbedWindowPort ∉ known := by key_fresh)
    (receiverPortsAreWindowStubsFresh : K .receiverPortsAreWindowStubs ∉ known := by key_fresh)
    (saturatedReceiverBasinFresh : K .saturatedReceiverBasin ∉ known := by key_fresh)
    (loadFlowValueFresh : K .loadFlowValue ∉ known := by key_fresh)
    (coverFlowValueFresh : K .coverFlowValue ∉ known := by key_fresh)
    (pieceSizeProfileFresh : K .pieceSizeProfile ∉ known := by key_fresh)
    (bridgePieceMassDichotomyFresh : K .bridgePieceMassDichotomy ∉ known := by key_fresh)
    (traceIntoCentreStructureFresh : K .traceIntoCentreStructure ∉ known := by key_fresh)
    (traceIntoAbsorbedStructureFresh : K .traceIntoAbsorbedStructure ∉ known := by key_fresh)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedDegreeFourLedgerFresh : K .typeBDegreeFourLedger ∉ known)
    (decoratedDegreeFourOverlapFresh : K .typeBDegreeFourOverlap ∉ known)
    (decoratedDegreeFourClosedFresh : K .typeBDegreeFourClosed ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by key_fresh)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by key_fresh)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by key_fresh)
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by key_fresh)
    (portReturnFresh : K .triangularPortReturn ∉ known := by key_fresh)
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by key_fresh)
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by key_fresh)
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by key_fresh)
    (decoratedGlobalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known)
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
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
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
  -- The absorbed Type B charge of `[177]` is a fact of G on this lane too.
  let charged := (typeBAbsorbedChargeRow (data := spineData)).run history
    (by key_fresh)
  exact Assembly.Internal.selectedTypeBFanContinuation charged
    (arm.decorated (TypeAArmBlock_decorated.ret charged))

end HypostructureErdos64EG
