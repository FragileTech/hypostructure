import Hypostructure.Graph.Strategy.SpineRows.TypeABoundedSupport
import Hypostructure.Graph.Strategy.SpineRows.TypeAPortReturn
import Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting
import Hypostructure.Graph.Strategy.SpineRows.TypeASaturationDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeASilentExitEntry
import Hypostructure.Graph.Strategy.SpineRows.TypeASupport
import Hypostructure.Graph.Strategy.SpineRows.TypeAUnsaturatedDischarge
import Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleEntryDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleFirstExcess
import HypostructureErdos64EG.Assembly.TypeA.VisibleExitChain

/-!
# Assembly: TypeA / LowSurplusContinuation

The Type A branch from node `[63]` to the saturated exit segment.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys the Type A branch and its continuations may add. -/
noncomputable abbrev typeALowSurplusKeys : FactKeys EGInput.{u} :=
  [K .typeASupport,
    K .typeABoundedSupport,
    K .typeAReceiverRouting,
    K .typeASaturatedReceiver,
    K .typeAUnsaturatedReceivers,
    K .typeAUnsaturatedDischarge,
    K .typeAPortReturn,
    K .typeAVisibleEntry,
    K .typeANoVisibleEntry,
    K .typeAVisibleFirstExcess,
    K .typeASaturatedExitEntry,
    closed,
    K .typeAExitOneReturn,
    K .typeAExitOneFree,
    K .typeAExitTwoTheta,
    K .typeAExitTwoFree,
    K .typeAExitThreeCollision,
    K .typeAExitThreeFree,
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
    K .route8UnifiedDeficit,
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
/-- **Nodes `[63]`, `[86]`--`[94]`: the Type A entry**, on the `[62]` Type A arm
(index-polymorphic).

`[86]`: the negative support of node `[61]` has `σ(X) = 0`, hence
`s·def⁺(X) < |V(X)|` (`def:typeA-support`).  `[87]`: node `[27]` makes it
`P₁₃`-free, with `diam(X) ≤ 11` and `|X| ≤ 6142`.  `[88]`: receiver routing and
the threshold algebra.  `[89]`: is some receiver saturated?  No: `[90]`
`L(w) ≤ s·q(w) − 1`, `[91]` `|X| ≤ s·def⁺(X)`, and `[92]` closes against
`[86]`.  `[89]` reads `[88]`.  Yes: `lem:typeA-port-return`, then `[93]`: does a saturated receiver
see `s` visible receiver-entry returns at one port?  Yes → exits `[95]`--`[100]`
and the shared exit segment; no → `[94]` `S_sil^exc(X) ≥ s·D_A(X)` and the same
exit segment from `[101]`.

`arm` names the prefix and entropy arm; each visible-entry arm adds its block. -/
-- EG-NODE [86] Type A: $\sigma(X)=0$, hence $\defp(X)<|X|/4$
-- EG-NODE [87] $P_{13}$-free; subcubic case has $\diam(X)\le11$ and $|X|\le6142$
-- EG-NODE [88] raw thresholds $H_0\le4$, $H_1\le8$, $H_2\le12$
-- EG-NODE [89] some receiver has $L(w)\ge4q(w)$?
-- EG-NODE [90] no: unsaturated $L(w)\le4q(w)-1$
-- EG-NODE [91] $3/7/11$ charge bound
-- EG-NODE [92] unsaturated Type A charge closes
-- EG-NODE [93] some port has four visible receiver-entry returns?
-- EG-NODE [94] visible-first excess: $S_{\rm sil}^{\rm exc}(X)\ge4D_A(X)$
noncomputable def selectedTypeALowSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : NetChargeArms selected)
    [FactKeys.Has (K .netChargeNegative) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
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
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    (fresh : List.Disjoint typeALowSurplusKeys known := by key_fresh)
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
  -- `[86]`
  let support :=
    (typeASupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[87]`
  let bounded :=
    (typeABoundedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      support (by key_fresh)
  -- `[88]`
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      bounded (by key_fresh)
  -- `[89]`
  match typeASaturationDichotomy (data := spineData) routed
      (by key_fresh) (by key_fresh) with
  | .right unsaturatedHistory =>
      -- `[90]`--`[92]`
      exact ((AtomicCT.runAndCloseIncompatible
        (typeAUnsaturatedDischargeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData))
        unsaturatedHistory (K .typeASupport) (K .typeAUnsaturatedDischarge)
        (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim
  | .left saturatedHistory =>
      -- `lem:typeA-port-return`
      let ports :=
        (typeAPortReturnRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          saturatedHistory (by key_fresh)
      -- `[93]`
      match typeAVisibleEntryDichotomy (data := spineData) ports
          (by key_fresh) (by key_fresh) with
      | .left visibleHistory =>
          -- `[95]`--`[109]` on the visible lane.
          exact selectedTypeAVisibleExitChain visibleHistory arm
      | .right noVisibleHistory =>
          -- `[94]`
          let excess :=
            (typeAVisibleFirstExcessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              noVisibleHistory (by key_fresh)
          -- `[94]` → `[101]`: the shared exit segment.
          let entered :=
            (typeASilentExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              excess (by key_fresh)
          exact selectedTypeAExitSegment entered
            ⟨arm, Or.inr (TypeAEntryBlock_noVisible.ret entered)⟩

end HypostructureErdos64EG
