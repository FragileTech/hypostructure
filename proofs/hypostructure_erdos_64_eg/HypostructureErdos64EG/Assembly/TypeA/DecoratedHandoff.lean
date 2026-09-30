import Hypostructure.Graph.Strategy.SpineRows.TypeBDecoratedAssignedSupport
import HypostructureErdos64EG.Assembly.TypeB.DecoratedContinuation

/-!
# Assembly: TypeA / DecoratedHandoff

Node `[108]` → Type B `[65]`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys the decorated Type B continuation from node `[108]` may add. -/
noncomputable abbrev typeADecoratedHandoffKeys : FactKeys EGInput.{u} :=
  [K .typeBDecoratedAssignedSupport,
    K .typeBFanEntry,
    K .highCentreNormalForm,
    K .typeBFanHeavyCentre,
    K .typeBFanDegreeFourCentres,
    K .typeBFanLocalDichotomy,
    K .sameCenterOpenPortCompatibility,
    K .typeBFanDegreeFourProfile,
    K .triangularFanCore,
    K .fanCertificateCap,
    K .fanCertificateMarked,
    K .fanCertificateResidual,
    K .fanCertificateResidualMass,
    K .typeBRoute8Entry,
    K .typeBDirectCycleFree,
    K .typeBB2Choice,
    K .typeBOverlapObstruction,
    K .typeBHybridEntry,
    K .typeBDisjointLedger,
    K .typeBBridgeMass,
    K .typeBBridgeSublinear,
    K .route8UnifiedNegative,
    K .typeAExclusion,
    K .typeBBridgeReduction,
    K .route8PiecesClassified,
    K .typeBSublinearLedger,
    K .typeBSublinearResidual,
    K .typeBSublinearCanonicalForm,
    K .groupedAbsorbedCoreSubset,
    K .typeBSublinearFailureArms,
    K .groupedCentresHigh,
    K .handoffDegreeClauseEmpty,
    K .pieceRoutingTotal,
    K .coverPayment,
    K .loadFailureSaturated,
    K .unpaidAbsorbedWindowPort,
    K .receiverPortsAreWindowStubs,
    K .saturatedReceiverBasin,
    K .loadFlowValue,
    K .coverFlowValue,
    K .pieceSizeProfile,
    K .bridgePieceMassDichotomy,
    K .traceIntoCentreStructure,
    K .traceIntoAbsorbedStructure,
    K .route8UnifiedDeficit,
    K .route8FoldPeels,
    K .route8QuotientFree,
    K .route8QuotientResidual,
    K .route8UnifiedEntryCensus,
    K .route8ExtractedEntryCensus,
    K .route8UnifiedTrueTwoCarrierEntry,
    K .route8PeelingDescent,
    K .route8StageRateFailed,
    K .route8DemandLedger,
    K .route8DemandAbsorption,
    K .route8OpenBoundarySaturated,
    K .route8DemandUnitCount,
    K .route8WindowBlockers,
    K .windowShadowHitCycle,
    K .windowShadowHitExcluded,
    K .route8UnpaidExitFourResidual,
    K .route8UnifiedVisibleResidual,
    K .route8UnifiedVisibleOverload,
    K .route8JointBalance,
    K .typeBExcluded,
    K .typeBExclusionResidual,
    K .typeBDegreeFourLedger,
    K .typeBDegreeFourOverlap,
    K .typeBDegreeFourClosed,
    K .typeBOverlapObstructionMass,
    K .compatiblePairFanClosure,
    K .fanClosedPortTypeBRouting,
    K .compatiblePairTypeBRouting,
    K .triangularShoulderCompletion,
    K .triangularPortReturn,
    K .triangularFirstLanding,
    K .triangularCrossShoulder,
    K .triangularPortTypeBRouting,
    K .typeBGlobalLocalBridge,
    closed,
    K .route8TwoCarrierExit,
    K .route8UnifiedTwoCarrierExit,
    K .route8StageRate,
    K .route8UnpaidTwoCarrier,
    K .route8UnpaidWitnessFree,
    K .route8QuotientEntriesAtG,
    K .route8PieceWindowAttachment, K .route8PieceChainCycle, K .route8PiecewiseRate,
    K .pieceDominanceIrreducible, K .twoExitNewLength,
    K .canonicalPieceDominance, K .canonicalTwoExitNewLength,
    K .twoExitSizeMonotone, K .canonicalTwoExitSizeMonotone,
    K .route8PackingExchange, K .route8ArmExchange, K .route8FullArmLandingCap,
    K .route8HubPieceMass, K .route8NetCapExcess, K .route8CleanLandingRules,
    K .route8CleanLandingCap, K .route8ArmClosureResidual,
    K .route8HubFreeDensity, K .route8X15LongLandings, K .route8HubFreePi,
    K .route8HubPieceExcess, K .route8ArmClosure, K .route8NetCapLarge,
    K .route8NetCapSmall,
    K .route8X15DoubleLanding, K .route8ArmPairTrigger, K .route8X15HeavyPair,
    K .route8BasinBurden,
    K .route8CarrierCore,
    K .typeBAbsorbedCharge]

set_option maxHeartbeats 8000000 in
/-- **Node `[108]` → Type B `[65]` on the decorated envelope**: the exact
envelope committed at `[108]` (`K .typeAExitSevenEnvelope`) enters the Type B
branch at `[65]`.  There `typeBDecoratedAssignedSupportRow` reads the inherited
selection, normalization, and uncompressibility facts, proves
`lem:decorated-fan-admissibility`, and commits the envelope's assigned support.
Then `[67]`--`[70]` run on that decorated envelope
(`selectedTypeBDecoratedContinuation`).

`arm` names the Type A lane arms with the exit-`(4)` block. -/
-- EG-NODE [65] Type B assigned support: high-degree fan centers and decorated handoff data
noncomputable def selectedTypeADecoratedHandoff
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : TypeAExitFourArms selected)
    [FactKeys.Has (K .typeAExitFiveFree) known]
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    [FactKeys.Has (K .typeAExitSixFree) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .typeAExitSevenEnvelope) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (fresh : List.Disjoint typeADecoratedHandoffKeys known := by key_fresh)
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
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  let assigned :=
    (typeBDecoratedAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[65]`: the Type B entry read from the decorated assigned support.
  let entry :=
    (typeBDecoratedEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      assigned (by key_fresh)
  exact selectedTypeBDecoratedContinuation entry arm
    (normalFormFresh := by key_fresh)
    (decoratedHeavyFresh := by key_fresh)
    (decoratedDegreeFourFresh := by key_fresh)
    (decoratedLocalFresh := by key_fresh)
    (decoratedCompatibilityFresh := by key_fresh)
    (decoratedProfileFresh := by key_fresh)
    (decoratedTriangularCoreFresh := by key_fresh)
    (fanCapFresh := by key_fresh)
    (decoratedMarkedFresh := by key_fresh)
    (decoratedResidualFresh := by key_fresh)
    (decoratedCertificateMassFresh := by key_fresh)
    (route8EntryFresh := by key_fresh)
    (decoratedFreeFresh := by key_fresh)
    (decoratedB2ChoiceFresh := by key_fresh)
    (decoratedB2ObstructionFresh := by key_fresh)
    (decoratedHybridFresh := by key_fresh)
    (decoratedLedgerFresh := by key_fresh)
    (decoratedBridgeMassFresh := by key_fresh)
    (decoratedBridgeSublinearFresh := by key_fresh)
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
    (windowShadowCycleFresh := by key_fresh)
    (windowShadowExcludedFresh := by key_fresh)
    (demandResidualFresh := by key_fresh)
    (unpaidExitFourFresh := by key_fresh)
    (unifiedVisibleFresh := by key_fresh)
    (unifiedVisibleOverloadFresh := by key_fresh)
    (jointBalanceFresh := by key_fresh)
    (unifiedTerminalFresh := by key_fresh)
    (decoratedExcludedFresh := by key_fresh)
    (decoratedExclusionResidualFresh := by key_fresh)
    (decoratedDegreeFourLedgerFresh := by key_fresh)
    (decoratedDegreeFourOverlapFresh := by key_fresh)
    (decoratedDegreeFourClosedFresh := by key_fresh)
    (decoratedObstructionMassFresh := by key_fresh)
    (compatibleClosureFresh := by key_fresh)
    (fanClosedRoutingFresh := by key_fresh)
    (compatibleRoutingFresh := by key_fresh)
    (shoulderCompletionFresh := by key_fresh)
    (portReturnFresh := by key_fresh)
    (firstLandingFresh := by key_fresh)
    (crossShoulderFresh := by key_fresh)
    (triangularRoutingFresh := by key_fresh)
    (decoratedGlobalLocalBridgeFresh := by key_fresh)

end HypostructureErdos64EG
