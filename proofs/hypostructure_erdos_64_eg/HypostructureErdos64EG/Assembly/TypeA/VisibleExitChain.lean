import Hypostructure.Graph.Strategy.SpineRows.TypeAExitOneDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitThreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitTwoDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleExitEntry
import HypostructureErdos64EG.Assembly.TypeA.ExitFourChain

/-!
# Assembly: TypeA / VisibleExitChain

Exits `(1)`--`(3)` of the visible saturated lane.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys exits `(1)`--`(3)` and the exit segment may add. -/
noncomputable abbrev typeAVisibleExitKeys : FactKeys EGInput.{u} :=
  [K .typeAExitOneReturn,
    K .typeAExitOneFree,
    K .typeAExitTwoTheta,
    K .typeAExitTwoFree,
    K .typeAExitThreeCollision,
    K .typeAExitThreeFree,
    K .typeASaturatedExitEntry,
    K .typeAExitFourFiniteDescent,
    K .typeASaturatedHandoffExitFour,
    K .typeAExitFourAbsent,
    K .typeAExitFourPeeled,
    K .typeASaturatedHandoffExitFourFree,
    K .typeAExitFourReceiverDischarged,
    K .typeAExitFive,
    K .typeAExitFiveFree,
    K .typeAExitSix,
    K .typeAExitSixFree,
    K .typeAExitSixProperScope,
    K .typeAExitSixGlobalScope,
    K .typeAExitSixProper,
    K .typeAExitSixGlobal,
    K .typeAExitSevenHandoff,
    K .typeAExitSevenFree,
    K .highCentreNormalForm,
    closed,
    K .typeBDecoratedAssignedSupport,
    K .typeBFanEntry,
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
    K .route8ResidualProfile,
    K .route8BasinBurden,
    K .route8LargeBudgetDeficit,
    K .route8LargeBudgetDeficitFails,
    K .route8CarrierCore,
    K .route8TrueResidual,
    K .route8CarrierCutParity,
    K .route8SmallCoreEntry,
    K .route8NoSmallCoreEntry,
    K .route8SmallCoreCollapse,
    K .route8Census,
    K .route8TwoCarrierEntry,
    K .route8NoTwoCarrierEntry,
    K .route8TrueTwoCarrierEntry,
    K .route8CarrierDeletionWitnesses,
    K .route8PrivateCarrierBudget,
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
    K .typeAExitFourSwitchCycle,
    K .typeAExitSevenSwitch,
    K .typeAPeeledSaturatedReceiver,
    K .typeAPeeledUnsaturatedDischarge,
    K .typeAPeeledVisibleEntry,
    K .typeAPeeledNoVisibleEntry,
    K .typeAPeeledSilentExcess,
    K .typeAPeeledExitOneReturn,
    K .typeAPeeledExitOneFree,
    K .typeAPeeledExitTwoTheta,
    K .typeAPeeledExitTwoFree,
    K .typeAPeeledExitThreeCollision,
    K .typeAPeeledExitThreeFree,
    K .typeAExitThreeCycle,
    K .typeAExitSevenEnvelope,
    K .typeBAbsorbedCharge]

set_option maxHeartbeats 8000000 in
/-- **Nodes `[95]`--`[100]`: exits `(1)`--`(3)`** on node `[93]`'s visible arm
(index-polymorphic).  `def:typeA-saturated-exits`, `lem:typeA-exits-discharged`:
exit `(1)` — a Mersenne anchored return — closes at `[96]` against the
return-avoidance invariant `[5]`--`[7]`; exit `(2)` — a power-of-two
common-port theta, read from `[95]`'s no arm — closes at `[98]` against the
selection; exit `(3)` — two returns through the port failing `C_s` at a common
packed window, read from `[97]`'s no arm — closes an accepted cycle at `[100]`,
against the selection.  The exit-`(3)`-free arm enters the shared exit segment
at `[101]`.

`arm` names the prefix and entropy arm; the visible-entry block is added at
the exit segment. -/
-- EG-NODE [95] exit 1? Mersenne return
-- EG-NODE [96] target cycle
-- EG-NODE [97] exit 2? power-of-two theta
-- EG-NODE [98] target cycle
-- EG-NODE [99] exit 3? $P_{13}$ label collision
-- EG-NODE [100] label/target collision
noncomputable def selectedTypeAVisibleExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : NetChargeArms selected)
    [FactKeys.Has (K .netChargeNegative) known]
    [FactKeys.Has (K .typeABoundedSupport) known]
    [FactKeys.Has (K .typeAPortReturn) known]
    [FactKeys.Has (K .typeASaturatedReceiver) known]
    [FactKeys.Has (K .typeASupport) known]
    [FactKeys.Has (K .typeAVisibleEntry) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8Rate) known]
    (fresh : List.Disjoint typeAVisibleExitKeys known := by key_fresh)
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
  -- `[95]`
  match typeAExitOneDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left returnHistory =>
      -- `[96]`
      exact ((closeIncompatible returnHistory (K .returnAvoidance)
        (K .typeAExitOneReturn) (by key_fresh)).elimClosed
          (by infer_instance)).elim
  | .right oneFree =>
      -- `[97]`
      match typeAExitTwoDichotomy (data := spineData) oneFree
          (by key_fresh) (by key_fresh) with
      | .left thetaHistory =>
          -- `[98]`
          exact ((closeIncompatible thetaHistory (K .selection)
            (K .typeAExitTwoTheta) (by key_fresh)).elimClosed
              (by infer_instance)).elim
      | .right twoFree =>
          -- `[99]`
          match typeAExitThreeDichotomy (data := spineData) twoFree
              (by key_fresh) (by key_fresh) with
          | .left collisionHistory =>
              -- `[100]`: the collision closes an accepted cycle of `G`.
              exact ((AtomicCT.runAndCloseIncompatible
                (typeAExitThreeCycleRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData))
                collisionHistory (K .selection) (K .typeAExitThreeCycle)
                (by key_fresh) (by key_fresh)).elimClosed
                  (by infer_instance)).elim
          | .right threeFree =>
              -- `[99]` → `[101]`: the shared exit segment.
              let entered :=
                (typeAVisibleExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  threeFree (by key_fresh)
              exact selectedTypeAExitSegment entered
                ⟨arm, Or.inl (TypeAEntryBlock_visible.ret entered)⟩

end HypostructureErdos64EG
