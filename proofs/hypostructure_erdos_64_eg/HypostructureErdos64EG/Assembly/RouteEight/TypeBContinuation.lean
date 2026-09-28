import Hypostructure.Graph.Strategy.SpineRows.BridgeFanMass
import Hypostructure.Graph.Strategy.SpineRows.Route8ExtractedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8PiecesClassified
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedNegative
import Hypostructure.Graph.Strategy.SpineRows.TypeAExclusion
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeReduction
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeSublinear
import Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion
import HypostructureErdos64EG.Assembly.RouteEight.Local
import Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCore

/-!
# Assembly: RouteEight / TypeBContinuation

The unified-demand continuation entered with the Type B bridge allowance.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The Type B bridge allowance and the unified collection prefix
(`prop:typeB-bridge-sublinear`, `def:typeA-unified-negative`, the Type A
exclusion and Type B bridge reduction, `thm:branch-kill`'s piece
classification, and the extracted route-`8` core census), appended to the
incoming ledger. -/
noncomputable def selectedRouteEightBridgePrefix
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh) :
    ExactLedger EGInput.{u} selected
      ([K .route8ExtractedEntryCensus, K .route8PiecesClassified,
        K .typeBBridgeReduction, K .typeAExclusion, K .route8UnifiedNegative,
        K .typeBBridgeSublinear, K .typeBBridgeMass] ++ known) :=
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by key_fresh)
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeSublinear (by key_fresh)
  let typeAExcluded :=
    (typeAExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unifiedNegative (by key_fresh)
  let typeBReduced :=
    (typeBBridgeReductionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeAExcluded (by key_fresh)
  let classified :=
    (route8PiecesClassifiedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeBReduced (by key_fresh)
  let extractedCensus :=
    (route8ExtractedEntryCensusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      classified (by key_fresh)
  extractedCensus


set_option maxHeartbeats 8000000 in
/-- **The unified target-defect/route-`8` ledger with the Type B bridge
allowance** (`rem:why-unified`, `prop:typeB-bridge-sublinear`).

The Type B bridge mass and its sublinear reading are published, then
`def:typeA-unified-negative`, the Type A exclusion and Type B bridge reduction,
`thm:branch-kill`'s piece classification, and the extracted route-`8` core
census; the branch then continues through the unified residual
(`selectedRouteEightUnifiedResidual`).  Every caller that reaches this ledger
-- the negative arm of node `[113]` and the Type B certificate lanes -- runs
this one composition on its own literal residual.

`arm` names the path's prefix, entropy arm and net-charge continuation. -/
noncomputable def selectedTypeBRoute8Continuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : Route8Arms selected)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8CarrierCore) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected :=
  selectedRouteEightUnifiedResidual (selectedRouteEightBridgePrefix history) arm

set_option maxHeartbeats 8000000 in
/-- **Node `[77]`, the Type B entry into route `8`** (tex 979: "route-8 cores
continue in Part IX").  It reads the `[76]`/`[85]` fact of the Type B support
(`K .typeBExclusionResidual`) and publishes its route-8 cores: a negative Type B
support hands the negative remaining core of its canonical B2 ledger to route
`8`, or is a bridge residual charged to its surplus.  The branch then continues
through the route-`8` census of Part IX on the same ledger.

`arm` names the arms fixed before the chain with the fan and certificate
blocks; the chain's entry block completes the net-charge continuation. -/
-- EG-NODE [77] route-8 cores continue in Part IX
noncomputable def selectedTypeBRoute8Entry
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : BChainArms selected ∧ BChainFanCertificate selected)
    [FactKeys.Has (K .compatiblePairFanClosure) known]
    [FactKeys.Has (K .compatiblePairTypeBRouting) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .fanClosedPortTypeBRouting) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .typeBExclusionResidual) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (route8EntryFresh : K .typeBRoute8Entry ∉ known := by key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh)
    (carrierCoreFresh : K .route8CarrierCore ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected :=
  let entry :=
    (typeBRoute8EntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- The route-8 burden `[112]` and the carrier cores `[114]` are facts of G on
  -- the Type B lanes too.
  let burdened :=
    (route8BasinBurdenRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      entry (by key_fresh)
  let cored :=
    (route8CarrierCoreRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      burdened (by key_fresh)
  selectedTypeBRoute8Continuation cored
    (arm.1.route8 ⟨BChainEntryBlock.ret entry, arm.2⟩)

end HypostructureErdos64EG
