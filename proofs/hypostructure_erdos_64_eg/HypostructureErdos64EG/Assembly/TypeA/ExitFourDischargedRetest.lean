import Hypostructure.Graph.Strategy.SpineRows.BridgeFanMass
import Hypostructure.Graph.Strategy.SpineRows.Route8ExtractedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8PiecesClassified
import Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedNegative
import Hypostructure.Graph.Strategy.SpineRows.TypeAExclusion
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeReduction
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeSublinear
import Hypostructure.Graph.Strategy.SpineRows.TypeBSublinearDichotomy
import HypostructureErdos64EG.Assembly.RouteEight.Boundary
import HypostructureErdos64EG.Assembly.RouteEight.Local
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.SameCenterOpenPortCompatibility
import Hypostructure.Graph.Strategy.SpineRows.TriangularShoulderCompletion
import Hypostructure.Graph.Strategy.SpineRows.TriangularPortReturn
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGermFanEnvelope
import Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCore

/-!
# Assembly: TypeA / ExitFourDischargedRetest

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys the Part IX continuation of the discharged receiver may add. -/
noncomputable abbrev typeADischargedRetestKeys : FactKeys EGInput.{u} :=
  [K .route8UnifiedNegative,
    K .typeAExclusion,
    K .typeBBridgeReduction,
    K .route8PiecesClassified,
    K .typeBBridgeMass,
    K .typeBBridgeSublinear,
    K .typeBSublinearLedger,
    K .typeBSublinearResidual,
    K .route8UnifiedDeficit,
    K .route8FoldPeels,
    K .route8QuotientFree,
    K .route8QuotientResidual,
    K .route8UnifiedEntryCensus,
    K .route8ExtractedEntryCensus,
    K .route8PeelingDescent,
    K .route8UnifiedTrueTwoCarrierEntry,
    K .route8StageRateFailed,
    closed,
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
    K .route8UnifiedTwoCarrierExit,
    K .route8StageRate,
    K .route8UnpaidTwoCarrier,
    K .route8UnpaidWitnessFree,
    K .highCentreNormalForm,
    K .sameCenterOpenPortCompatibility,
    K .triangularShoulderCompletion,
    K .triangularPortReturn,
    K .typeBAbsorbedCharge,
    K .route8BasinBurden,
    K .route8CarrierCore]

set_option maxHeartbeats 8000000 in
/-- **`[102]` → `[89]` no → `[90]`--`[91]` → `[123]`, the peeled supports.**  On
the no arm of the recompute-`L₄` retest every receiver of `X₀` is unsaturated
after peeling (`K .typeAExitFourReceiverDischarged`, node `[90]` with `L₄`),
and node `[91]` bounds the charge of the unpeeled loads
(`K .typeAPeeledUnsaturatedDischarge`, `lem:typeA-exit4-peeling-charge`).  The
diagram closes this arm at node `[92]`; with a nonempty peeling set that
closure does not follow (see `lean-vs-paper-discrepancies.md`, Paper errors,
[92]).  The paper's own routing of the peeled loads is taken instead:
`rem:typeA-exit4-peeling-use` sends a support with an exit-`(4)` witness through
alternative (iii) of `lem:density-mersenne` to the unified target-defect/route-`8`
ledger of node `[123]`, the one shared composition
`selectedRouteEightUnifiedResidual`.

`arm` names the Type A lane arms; the retest block completes the net-charge
continuation. -/
-- EG-NODE none (the second pass of [90]--[91]; [92] recorded as a paper error)
noncomputable def selectedTypeAExitFourDischargedRetest
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : TypeALaneArms selected)
    [FactKeys.Has (K .typeAExitFourPeeled) known]
    [FactKeys.Has (K .typeAExitFourReceiverDischarged) known]
    [FactKeys.Has (K .typeAPeeledUnsaturatedDischarge) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFour) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .tightEndpoint) known]
    (fresh : List.Disjoint typeADischargedRetestKeys known := by key_fresh)
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
  -- `[123]`: publish `def:typeA-unified-negative` on this residual.
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
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
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      extractedCensus (by key_fresh)
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by key_fresh)
  -- Facts of G that the other lanes into `[123]` carry, published on this lane
  -- from its own ledger: the heavy-neighbourhood normal form `[67]`, the
  -- same-centre and triangular landing lemmas of `[69]`, the absorbed Type B
  -- charge of `[177]`, the route-8 burden `[112]` and the carrier cores `[114]`.
  let normal :=
    (highCentreNormalFormRow (data := spineData)).run bridgeSublinear
      (by key_fresh)
  let compatible :=
    (sameCenterOpenPortCompatibilityRow (data := spineData)).run normal
      (by key_fresh)
  let completed :=
    (triangularShoulderCompletionRow (data := spineData)).run compatible
      (by key_fresh)
  let returned :=
    (triangularPortReturnRow (data := spineData)).run completed (by key_fresh)
  let charged :=
    (typeBAbsorbedChargeRow (data := spineData)).run returned (by key_fresh)
  let burdened :=
    (route8BasinBurdenRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      charged (by key_fresh)
  let cored :=
    (route8CarrierCoreRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      burdened (by key_fresh)
  exact selectedRouteEightUnifiedResidual cored
    (arm.dischargedRetest (TypeAArmBlock_dischargedRetest.ret cored))

end HypostructureErdos64EG
